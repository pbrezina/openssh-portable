/*
 * Copyright (c) 2026 Alexander Bokovoy <abokovoy@redhat.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * SSH S4U2Self X.509 attestation certificate construction.
 *
 * Builds a short-lived X.509 certificate encoding the SSH authentication
 * event, signed with a key derived from the host Kerberos keytab.  The
 * certificate is passed as subject_cert in a PA-FOR-X509-USER TGS-REQ so
 * that the KDC KDB plugin can verify the attestation and inject auth
 * indicators into the resulting service ticket.
 *
 * Design: ~/todo/ssh-s4u2self-binding.md
 * Server-side counterpart: ipa_kdb_s4u_x509.c in the IPA KDB plugin.
 *
 * Implementation split:
 *   gss-s4u-x509-crypto.c  — HKDF, key derivation, ephemeral key generation
 *   gss-s4u-x509-asn1.c    — ASN.1 types, SPKI conversion, PKINIT SAN
 *   gss-s4u-x509-keytab.c  — keytab enumeration
 *   gss-s4u-x509.c         — certificate assembly (this file)
 */

#include "includes.h"

#if defined(GSSAPI) && defined(KRB5) && !defined(HEIMDAL) && defined(WITH_OPENSSL)

#include <sys/types.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <arpa/inet.h>

#include <openssl/x509.h>
#include <openssl/x509v3.h>
#include <openssl/evp.h>
#include <openssl/asn1.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include <openssl/err.h>
#include <openssl/objects.h>

#include <krb5.h>

#include "xmalloc.h"
#include "sshbuf.h"
#include "sshkey.h"
#include "crypto_api.h"
#include "log.h"

#include "gss-s4u-x509.h"
#include "gss-s4u-x509-internal.h"

/* ------------------------------------------------------------------ *
 * Build the DER-encoded attestation certificate.
 *
 * On success, *cert_der_out is set to a malloc'd buffer of
 * *cert_der_len_out bytes.  Returns 0 on success, -1 on failure.
 * ------------------------------------------------------------------ */
int
ssh_gssapi_s4u_x509_build_cert(
    const char *user, const char *realm,
    const char *auth_method,
    const struct sshbuf *session_id_buf,
    const struct sshkey *auth_method_key,
    const char *key_fingerprint,
    const char *client_address,
    const struct sshkey *host_pubkey,
    const unsigned char *ikm, size_t ikm_len,
    krb5_enctype enctype, uint32_t kvno,
    const char *hostname,
    u_int cert_lifetime,
    unsigned char **cert_der_out, size_t *cert_der_len_out)
{
	int		 fips_mode;
	EVP_PKEY	*derived_key  = NULL;
	EVP_PKEY	*subject_pkey = NULL;
	X509_PUBKEY	*host_spki    = NULL;
	X509		*cert         = NULL;
	char		*principal    = NULL;
	unsigned char	*ib_der = NULL, *ai_der = NULL;
	int		 ib_len = 0,     ai_len = 0;
	unsigned char	*cert_der = NULL;
	int		 cert_der_len;
	int		 key_id   = 0;
	const EVP_MD	*sign_md  = NULL;
	int		 ret = -1;

	*cert_der_out     = NULL;
	*cert_der_len_out = 0;

	fips_mode = EVP_default_properties_is_fips_enabled(NULL);

	/* In FIPS mode, Ed25519 client keys cannot go into a SPKI */
	if (fips_mode && auth_method_key != NULL &&
	    auth_method_key->type == KEY_ED25519) {
		debug2_f("S4U X.509: Ed25519 client key not usable in FIPS "
		    "mode; skipping attestation");
		return -1;
	}

	/* Attestation certificates are short-lived regardless of GSS lifetime */
	if (cert_lifetime > SSH_S4U_CERT_LIFETIME_MAX)
		cert_lifetime = SSH_S4U_CERT_LIFETIME_MAX;

	xasprintf(&principal, "host/%s@%s", hostname, realm);

	derived_key = derive_attestation_key(ikm, ikm_len,
	    hostname, realm, kvno, fips_mode, "ssh-attestation-v1");
	if (!derived_key) {
		/* derive_attestation_key logs the specific failure */
		goto done;
	}
	key_id  = EVP_PKEY_base_id(derived_key);
	sign_md = (key_id == EVP_PKEY_ED25519) ? NULL : EVP_sha256();

	host_spki = sshkey_to_x509_pubkey(host_pubkey);
	if (!host_spki) {
		debug2_f("S4U X.509: cannot convert host key to SPKI");
		goto done;
	}

	/* ---- Build id-ce-kerberosServiceIssuerBinding ---- */
	{
		KERBEROS_SERVICE_ISSUER_BINDING *ib;
		unsigned char   digest[SHA256_DIGEST_LENGTH];
		unsigned char   sig[128]; /* Ed25519 = 64, ECDSA P-256 ≤ 72 */
		size_t          siglen = sizeof(sig);
		EVP_MD_CTX     *mdctx = NULL;

		ib = KERBEROS_SERVICE_ISSUER_BINDING_new();
		if (!ib)
			goto done;

		if (!ASN1_INTEGER_set(ib->version, 0) ||
		    !ASN1_STRING_set(ib->service_type, "ssh",
		        (int)strlen("ssh")) ||
		    !ASN1_STRING_set(ib->principal, principal,
		        (int)strlen(principal)) ||
		    !ASN1_INTEGER_set(ib->enctype, (long)enctype) ||
		    !ASN1_INTEGER_set(ib->kvno, (long)kvno)) {
			KERBEROS_SERVICE_ISSUER_BINDING_free(ib);
			goto done;
		}

		{
			ASN1_OBJECT *sig_obj = OBJ_nid2obj(
			    key_id == EVP_PKEY_ED25519
			    ? NID_ED25519 : NID_ecdsa_with_SHA256);
			if (sig_obj == NULL ||
			    !X509_ALGOR_set0(ib->sig_alg, sig_obj,
			    V_ASN1_UNDEF, NULL)) {
				ASN1_OBJECT_free(sig_obj);
				KERBEROS_SERVICE_ISSUER_BINDING_free(ib);
				goto done;
			}
		}

		/* Transfer host_spki ownership into ib */
		X509_PUBKEY_free(ib->service_key);
		ib->service_key = host_spki;
		host_spki = NULL;

		if (compute_binding_digest(ib->service_key, principal,
		    kvno, "ssh-attestation-binding-v1", digest) != 0) {
			OPENSSL_cleanse(digest, sizeof(digest));
			/*
			 * service_key was transferred into ib; NULL it before
			 * KERBEROS_SERVICE_ISSUER_BINDING_free to prevent
			 * double-free of the X509_PUBKEY via both host_spki
			 * and ib cleanup paths.
			 */
			ib->service_key = NULL;
			KERBEROS_SERVICE_ISSUER_BINDING_free(ib);
			goto done;
		}

		mdctx = EVP_MD_CTX_new();
		if (!mdctx) {
			OPENSSL_cleanse(digest, sizeof(digest));
			ib->service_key = NULL; /* see above */
			KERBEROS_SERVICE_ISSUER_BINDING_free(ib);
			goto done;
		}
		if (EVP_DigestSignInit(mdctx, NULL, sign_md, NULL,
		    derived_key) <= 0 ||
		    EVP_DigestSign(mdctx, sig, &siglen,
		        digest, SHA256_DIGEST_LENGTH) <= 0 ||
		    !ASN1_STRING_set(ib->binding, sig, (int)siglen)) {
			EVP_MD_CTX_free(mdctx);
			OPENSSL_cleanse(sig, sizeof(sig));
			OPENSSL_cleanse(digest, sizeof(digest));
			ib->service_key = NULL; /* see above */
			KERBEROS_SERVICE_ISSUER_BINDING_free(ib);
			goto done;
		}
		EVP_MD_CTX_free(mdctx);
		OPENSSL_cleanse(sig, sizeof(sig));
		OPENSSL_cleanse(digest, sizeof(digest));

		ib_len = i2d_KERBEROS_SERVICE_ISSUER_BINDING(ib, &ib_der);
		ib->service_key = NULL; /* see above */
		KERBEROS_SERVICE_ISSUER_BINDING_free(ib);

		if (!ib_der || ib_len <= 0)
			goto done;
	}

	/* ---- Build id-ce-sshAuthnContext ---- */
	{
		SSH_AUTHN_CONTEXT *ai = SSH_AUTHN_CONTEXT_new();
		if (!ai)
			goto done;

		const unsigned char *sid     = sshbuf_ptr(session_id_buf);
		size_t		     sid_len = sshbuf_len(session_id_buf);

		if (sid_len > INT_MAX) {
			SSH_AUTHN_CONTEXT_free(ai);
			goto done;
		}
		if (!ASN1_INTEGER_set(ai->version, 0) ||
		    !ASN1_STRING_set(ai->auth_method, auth_method,
		        (int)strlen(auth_method)) ||
		    !ASN1_STRING_set(ai->session_id, sid, (int)sid_len)) {
			SSH_AUTHN_CONTEXT_free(ai);
			goto done;
		}
		if (key_fingerprint) {
			if (!ai->key_fingerprint)
				ai->key_fingerprint = ASN1_UTF8STRING_new();
			if (!ai->key_fingerprint ||
			    !ASN1_STRING_set(ai->key_fingerprint,
			        key_fingerprint, (int)strlen(key_fingerprint))) {
				SSH_AUTHN_CONTEXT_free(ai);
				goto done;
			}
		}
		if (client_address) {
			if (!ai->client_address)
				ai->client_address = ASN1_UTF8STRING_new();
			if (!ai->client_address ||
			    !ASN1_STRING_set(ai->client_address,
			        client_address, (int)strlen(client_address))) {
				SSH_AUTHN_CONTEXT_free(ai);
				goto done;
			}
		}

		ai_len = i2d_SSH_AUTHN_CONTEXT(ai, &ai_der);
		SSH_AUTHN_CONTEXT_free(ai);

		if (!ai_der || ai_len <= 0)
			goto done;
	}

	/* ---- Assemble X.509 certificate ---- */
	cert = X509_new();
	if (!cert)
		goto done;

	if (X509_set_version(cert, X509_VERSION_3) != 1) {
		error_f("S4U X.509: X509_set_version failed");
		goto done;
	}

	/* Random positive serial number */
	{
		uint64_t serial = 0;
		if (RAND_bytes((unsigned char *)&serial, sizeof(serial)) != 1) {
			error_f("S4U X.509: RAND_bytes failed");
			goto done;
		}
		serial &= ~((uint64_t)1 << 63);	/* clear sign bit */
		if (!ASN1_INTEGER_set_uint64(X509_get_serialNumber(cert),
		    serial)) {
			error_f("S4U X.509: ASN1_INTEGER_set_uint64 failed");
			goto done;
		}
	}

	{
		time_t now = time(NULL);
		ASN1_TIME_set(X509_getm_notBefore(cert), now);
		ASN1_TIME_set(X509_getm_notAfter(cert),
		    now + (time_t)cert_lifetime);
	}

	/* Issuer: CN = "host/hostname@REALM" */
	if (X509_NAME_add_entry_by_NID(X509_get_issuer_name(cert),
	    NID_commonName, MBSTRING_UTF8,
	    (unsigned char *)principal, (int)strlen(principal), -1, 0) != 1) {
		error_f("S4U X.509: failed to set Issuer CN");
		goto done;
	}

	/* Subject: CN = user */
	if (X509_NAME_add_entry_by_NID(X509_get_subject_name(cert),
	    NID_name, MBSTRING_UTF8,
	    (unsigned char *)user, (int)strlen(user), -1, 0) != 1) {
		error_f("S4U X.509: failed to set Subject CN");
		goto done;
	}

	/* SubjectPublicKeyInfo */
	if (auth_method_key != NULL &&
	    (auth_method_key->type == KEY_RSA ||
	     auth_method_key->type == KEY_ECDSA)) {
		if (X509_set_pubkey(cert, auth_method_key->pkey) != 1) {
			error_f("S4U X.509: X509_set_pubkey failed for "
			    "RSA/ECDSA client key");
			goto done;
		}
	} else if (auth_method_key != NULL &&
	    auth_method_key->type == KEY_ED25519 && !fips_mode) {
		EVP_PKEY *epkey = EVP_PKEY_new_raw_public_key(
		    EVP_PKEY_ED25519, NULL,
		    auth_method_key->ed25519_pk, ED25519_PK_SZ);
		if (epkey == NULL) {
			error_f("S4U X.509: EVP_PKEY_new_raw_public_key "
			    "failed for Ed25519 client key");
			goto done;
		}
		int r = X509_set_pubkey(cert, epkey);
		EVP_PKEY_free(epkey);
		if (r != 1) {
			error_f("S4U X.509: X509_set_pubkey failed for "
			    "Ed25519 client key");
			goto done;
		}
	} else {
		subject_pkey = generate_ephemeral_key(fips_mode);
		if (!subject_pkey) {
			error_f("S4U X.509: generate_ephemeral_key failed");
			goto done;
		}
		if (X509_set_pubkey(cert, subject_pkey) != 1) {
			error_f("S4U X.509: X509_set_pubkey failed for "
			    "ephemeral key");
			goto done;
		}
	}

	/* basicConstraints: CA:FALSE (critical) */
	{
		X509_EXTENSION *bc = X509V3_EXT_conf_nid(NULL, NULL,
		    NID_basic_constraints, "critical,CA:FALSE");
		if (bc == NULL || X509_add_ext(cert, bc, -1) != 1) {
			error_f("S4U X.509: failed to add basicConstraints");
			X509_EXTENSION_free(bc);
			goto done;
		}
		X509_EXTENSION_free(bc);
	}

	/* keyUsage: digitalSignature (critical) */
	{
		X509_EXTENSION *ku = X509V3_EXT_conf_nid(NULL, NULL,
		    NID_key_usage, "critical,digitalSignature");
		if (ku == NULL || X509_add_ext(cert, ku, -1) != 1) {
			error_f("S4U X.509: failed to add keyUsage");
			X509_EXTENSION_free(ku);
			goto done;
		}
		X509_EXTENSION_free(ku);
	}

	/* extKeyUsage: id-pkinit-KPClientAuth (required by RFC 4556) */
	{
		ASN1_OBJECT *eku_obj =
		    OBJ_txt2obj(OID_PKINIT_KP_CLIENTAUTH, 1);
		EXTENDED_KEY_USAGE *eku = NULL;
		int eku_ok = 0;

		if (eku_obj != NULL) {
			eku = sk_ASN1_OBJECT_new_null();
			if (eku != NULL) {
				sk_ASN1_OBJECT_push(eku, eku_obj);
				eku_obj = NULL;
				if (X509_add1_ext_i2d(cert, NID_ext_key_usage,
				    eku, 0, 0) == 1)
					eku_ok = 1;
				sk_ASN1_OBJECT_pop_free(eku, ASN1_OBJECT_free);
			}
		}
		ASN1_OBJECT_free(eku_obj);
		if (!eku_ok) {
			error_f("S4U X.509: failed to add extKeyUsage "
			    "(id-pkinit-KPClientAuth)");
			goto done;
		}
	}

	/* subjectAltName: id-pkinit-san (critical — KDC identifies principal by this) */
	if (add_pkinit_san(cert, user, realm) != 0) {
		error_f("S4U X.509: failed to add PKINIT SAN; "
		    "aborting attestation cert");
		goto done;
	}

	/* id-ce-kerberosServiceIssuerBinding */
	if (add_raw_extension(cert, OID_KERBEROS_SERVICE_ISSUER_BINDING, 0,
	    ib_der, ib_len) != 0) {
		error_f("S4U X.509: cannot add issuer binding extension");
		goto done;
	}

	/* id-ce-sshAuthnContext */
	if (add_raw_extension(cert, OID_SSH_AUTHN_CONTEXT, 0,
	    ai_der, ai_len) != 0) {
		error_f("S4U X.509: cannot add authn context extension");
		goto done;
	}

	/* Sign with the derived attestation key */
	if (X509_sign(cert, derived_key, sign_md) <= 0) {
		error_f("S4U X.509: cert signing failed");
		goto done;
	}

	/* DER-encode the completed certificate */
	cert_der_len = i2d_X509(cert, NULL);
	if (cert_der_len <= 0)
		goto done;
	cert_der = malloc((size_t)cert_der_len);
	if (!cert_der)
		goto done;
	{
		unsigned char *p = cert_der;
		int written = i2d_X509(cert, &p);
		if (written != cert_der_len) {
			error_f("S4U X.509: i2d_X509 length mismatch "
			    "(%d vs %d)", written, cert_der_len);
			goto done;
		}
	}

	*cert_der_out     = cert_der;
	*cert_der_len_out = (size_t)cert_der_len;
	cert_der = NULL;
	debug_f("S4U X.509: built attestation cert for user %.100s "
	    "realm %.64s method %.32s (%d bytes)",
	    user, realm, auth_method, cert_der_len);
	ret = 0;

done:
	free(principal);
	OPENSSL_free(ib_der);
	OPENSSL_free(ai_der);
	free(cert_der);
	EVP_PKEY_free(derived_key);
	EVP_PKEY_free(subject_pkey);
	X509_PUBKEY_free(host_spki);
	X509_free(cert);
	return ret;
}

#endif /* GSSAPI && KRB5 && !HEIMDAL && WITH_OPENSSL */
