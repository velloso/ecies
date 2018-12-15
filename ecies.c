#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <relic/relic_md.h>
#include <relic/relic_ep.h>
#include <relic/relic_fp.h>
#include <relic/relic_cp.h>
#include <relic/relic_bn.h>
#include <relic/relic_core.h>
#include <openssl/evp.h>
#include <time.h>


#define MAX_BYTE	0xFF


void print_uint8_t(uint8_t *key, int len, char c[20]) {
	int i;
	printf("%s value: ", c);
	for (i = len-1; i >= 0; i--)
		printf("%d ", key[i]);
	printf("\n");
}

// Returns 1 for v1 > v2
// Returns 0 for v1 == v2
// Returns -1 for v1 == v2
int compare_array(uint8_t *v1, uint8_t *v2, int len) {
	int i = 0;
	for (i = len-1; i >= 0; i--)
		if (v1[i] > v2[i])
			return 1;
		else if (v1[i] < v2[i])
			return -1;
	return 0;
}

// Elliptic point addition
void point_addition(const fp_t x1, const fp_t y1, const fp_t x2, const fp_t y2, fp_t x3, fp_t y3){
	fp_t c, d, lambda;
	fp_new (c);
	fp_new (d);
	fp_new (lambda);
	
	fp_sub_basic(c, y2, y1);
	fp_sub_basic(d, x2, x1); 
	fp_inv_basic(d, d);
	fp_mul_basic(lambda, c, d);

	fp_sqr_basic(c, lambda);
	fp_sub_basic(c, c, x1);
	fp_sub_basic(x3, c, x2);
	
	fp_sub_basic(c, x1, x3);
	fp_mul_basic(d, lambda, c);
	fp_sub_basic(y3, d, y1);

	fp_free(c);
	fp_free(d);
	fp_free(lambda);

	return;	
}

// Elliptic point doubling
void point_doubling(const fp_t x, const fp_t y, unsigned long  a, fp_t x3, fp_t y3){
	unsigned long a2 = a;
	fp_t c, d, lambda;
	fp_new (c);
	fp_new (d);
	fp_new (lambda);
	
	fp_sqr_basic(c, x);
	fp_mul_dig(c, c, 3);
	fp_add_dig(c, c, a);
	fp_mul_dig(d, y, 2);
	fp_inv_basic(d, d);
	fp_mul_basic(lambda, c, d);
	
	fp_sqr_basic(c, lambda);
	fp_mul_dig(d, x, 2);
	fp_sub_basic(x3, c, d);
	
	fp_sub_basic(c, x, x3);
	fp_mul_basic(d, lambda, c);
	fp_sub_basic(y3, d, y);
	
	fp_free(c);
	fp_free(d);
	fp_free(lambda);
	
	return;	
}

// Function for point multiplication kP 
void point_multi(bn_t d, fp_t x, fp_t y, unsigned long a, fp_t x3, fp_t y3){
	bn_t k;
	bn_copy(k, d);	
	if (bn_is_zero(k)){
		fp_zero(x3);
		fp_zero(x3);
		return;
	}
	if (bn_cmp_dig(k, 1) == CMP_EQ){
		fp_copy(x3, x);
		fp_copy(y3, y);
		return;
	}
	if (!bn_is_even(k)){
		fp_t nx, ny;
		fp_t n2x, n2y;
		bn_sub_dig(k, k, 1);
		bn_hlv(k, k);
		point_multi(k, x, y, a, nx, ny);
		fp_copy(n2x, nx);
		fp_copy(n2y, ny);
		point_doubling(n2x, n2y, a, nx, ny);
		fp_copy(n2x, nx);
		fp_copy(n2y, ny);
		if (fp_cmp(nx, x) == CMP_EQ && fp_cmp(ny, y) == CMP_EQ) point_doubling(n2x, n2y, a, nx, ny);
		else point_addition(x, y, n2x, n2y, nx, ny);	
		fp_copy(x3, nx);
		fp_copy(y3, ny);
		return;
	} else {
		fp_t nx, ny;
		fp_t n2x, n2y;
		bn_hlv(k, k);
		point_multi(k, x, y, a, nx, ny);
		fp_copy(n2x, nx);
		fp_copy(n2y, ny);
		point_doubling(n2x, n2y, a, nx, ny);
		fp_copy(x3, nx);
		fp_copy(y3, ny);
		return;
	}
}


void generate_keypair(bn_t p, unsigned long a, fp_t p_x, fp_t p_y, bn_t d, fp_t q_x, fp_t q_y) {
	while (1){
		bn_rand(d, BN_POS, bn_bits(p));
		bn_mod(d, d, p);
		point_multi(d, p_x, p_y, a, q_x, q_y);
		if (!fp_is_zero(q_x) || !fp_is_zero(q_y)) break;
	}
	return;
}


void ecies_enc(uint8_t *msg, int msg_len, bn_t p, bn_t h, unsigned long a, fp_t p_x, fp_t p_y, fp_t q_x, fp_t q_y, fp_t r_x, fp_t r_y, uint8_t *enc, int *enc_len, uint8_t *hmac, int hmac_len) {
	int size = 32;
	bn_t k;
	bn_null(k);
	bn_new(k);
	bn_t c;
	fp_t z_x, z_y;
	uint8_t key1[size], key2[size], uzx[FP_BYTES], ur[FP_BYTES];
	
	// Finds the points in the eliptic curve
	// Where: R = k.P
	// and: Z = k.h.P
	while (1){
		bn_rand(k, BN_POS, bn_bits(p));
		bn_mod(k, k, p);
		bn_mul_basic(c, h, k);
		point_multi(k, p_x, p_y, a, r_x, r_y);
		point_multi(c, q_x, q_y, a, z_x, z_y);
		if (!fp_is_zero(z_x) || !fp_is_zero(z_y)) break;
	}
	fp_write_bin(uzx, FP_BYTES, z_x);
	fp_write_bin(ur, FP_BYTES, r_x);
	
	// Use the key derivation function from relic
	// to find two keys
	// key1 = KDF(Zx)
	// key2 = KDF(R)
	md_kdf2(key1, size, uzx, FP_BYTES);
	md_kdf2(key2, size, ur, FP_BYTES);
	
	// Ecrypts the message using AES with key1
	EVP_CIPHER_CTX ctx;
    unsigned char iv[16] = {0};
    int outlen1, outlen2;

    EVP_EncryptInit(&ctx, EVP_aes_256_cbc(), key1, iv);
    EVP_EncryptUpdate(&ctx, enc, &outlen1, msg, msg_len);
    EVP_EncryptFinal(&ctx, enc + outlen1, &outlen2);
	*enc_len = outlen1 + outlen2;

	// Finds the MAC of the encripted message using hmac
	uint8_t hmac_comp[hmac_len];
	md_hmac(hmac_comp, enc, *enc_len, key2, size);
	memcpy(hmac, hmac_comp, hmac_len);
 	
	return;
}

void ecies_dec(bn_t h, bn_t d, unsigned long a, fp_t r_x, fp_t r_y, uint8_t *enc, int *enc_len, uint8_t *hmac, int hmac_len) {
	int size = 32;
	int k;
	fp_t z_x, z_y;
	uint8_t key1[size], key2[size], uzx[FP_BYTES], ur[FP_BYTES];

	// Finds the points in the eliptic curve
	// where: Z = h.d.R
	bn_t c;
	bn_mul_basic(c, h, d);
	point_multi(c, r_x, r_y, a, z_x, z_y);
	if (fp_is_zero(z_x) && fp_is_zero(z_y)) {
		printf("Reject the ciphertext.\n");
		return;
	}
	fp_write_bin(uzx, FP_BYTES, z_x);
	fp_write_bin(ur, FP_BYTES, r_x);
	
	// Use the key derivation function from relic
	// to find two keys
	// key1 = KDF(Zx)
	// key2 = KDF(R)
	md_kdf2(key1, size, uzx, FP_BYTES);
	md_kdf2(key2, size, ur, FP_BYTES);
	
	// Finds the MAC of the encripted message using hmac
	// compares with the given hmac
	uint8_t hmac_comp[hmac_len];
	md_hmac(hmac_comp, enc, *enc_len, key2, size);
	if (compare_array(hmac_comp, hmac, hmac_len) != 0) {
		printf("Wrong hash\n");
		return;
	}
	
	// Decrypts the message
	EVP_CIPHER_CTX ctx;
    unsigned char iv[16] = {0};
    unsigned char out[32];
    int outlen1, outlen2;

    EVP_DecryptInit(&ctx, EVP_aes_256_cbc(), key1, iv);
    EVP_DecryptUpdate(&ctx, out, &outlen1, enc, *enc_len);
    EVP_DecryptFinal(&ctx, out + outlen1, &outlen2);
    
    printf("%s\n", out);
	
	return;
}

int main(){
	// Initialize relic
	core_init();
	
	// Initialize the finite prime field
	fp_prime_init();
	fp_param_set_any();
	// Initialize the eliptic curve
	ep_curve_init();
	if (ep_param_set_any() == STS_ERR) {
		printf("Error\n");
		return -1;
	}
	
	bn_t drelic;
	ep_t Q;
	cp_ecies_gen(drelic, Q);
	
	ep_t res;					// point result
	int enc_len = 32;			// enc len
	uint8_t enc[enc_len];		// encrypted result	
	int msg_len = 16;			// msg len
	uint8_t msg[msg_len];		// message to encrypt
	int new_msg_len = 16;		// msg len
	uint8_t new_msg[msg_len];	// message to encrypt
	int hmac_len = 16;
	uint8_t hmac[hmac_len];
	fp_t r_x, r_y, px, py, qx, qy;
	bn_t q_x, q_y, p_x, p_y;
	unsigned long a = *ep_curve_get_a();
	bn_t d;
	bn_new(d);
	
	ep_t g;
	ep_curve_get_gen(g);
	ec_get_x(p_x, g);
	ec_get_y(p_y, g);
	fp_prime_conv(px, p_x);
	fp_prime_conv(py, p_y);
	
	bn_t p;
	ep_curve_get_ord (p);
	bn_t h;
	ep_curve_get_cof (h);
	
	
	generate_keypair(p, a, px, py, d, qx, qy);

	printf("Write a message: ");
	fgets (msg, msg_len, stdin);
	uint8_t msg_sav[msg_len];		// message to encrypt
	memcpy(msg_sav, msg, msg_len);
	
	clock_t t; 
	t = clock();
	// Encrypts the message using the ECIES protocol
	ecies_enc(msg, msg_len, p, h, a, px, py, qx, qy, r_x, r_y, enc, &enc_len, hmac, hmac_len);
	
	// Decrypts the message using the ECIES protocol
	ecies_dec(h, d, a, r_x, r_y, enc, &enc_len, hmac, hmac_len);
	t = clock() - t;
	double time_taken = ((double)t)/CLOCKS_PER_SEC;
	printf("My ecies took %f seconds to execute \n", time_taken);
	
	
	
	t = clock(); 
	// RELIC Encrypt
	cp_ecies_enc(res, enc, &enc_len, msg_sav, msg_len, Q);
	// RELIC Decrypt
	cp_ecies_dec(new_msg, &new_msg_len, res, enc, enc_len, drelic);
	t = clock() - t;
	time_taken = ((double)t)/CLOCKS_PER_SEC;
	printf("RELIC took %f seconds to execute \n", time_taken);
	
	ep_free(q);
	ep_curve_clean();
	fp_prime_clean();
	core_clean();
	return 1;
}

/*
// Modular inversion using the 

// Extended Euclidean Algorithm
int modular_inversion(int a, int mod){
	if (a >= mod || a < 1 || mod < 1) {
		printf("Invalid inputs; a = %d, mod = %d.\n", a, mod);
		return -1;
	}
	int u = a;
	int v = mod;
	int x1 = 1;
	int x2 = 0;
	int q, r, x;
	
	while (u != 1){
		q = (int)v/u;
		r = v - q*u;
		x = x2 - q*x1;
		
		v = u;
		u = r;
		x2 = x1;
		x1 = x;
	}
	x1 = x1%mod;
	return (x1 < 0) ? mod+x1 : x1;
}

int division(int a, int b, int mod) {
	int inverse = modular_inversion(b, mod);
	if (inverse == -1) {

		printf("Division not defined.\n");
		return -1;
	}
	return (inverse * a) % mod;
}

int power(int a, int b, int p) {
	int res = (int)pow(a, b)%p;
	return (res < 0) ? p+res : res;
}


int multi(int a, int b, int p) {
	int res = (a * b)%p;
	return (res < 0) ? p+res : res;
}

// Subtraction function
int sub_(uint8_t *res, uint8_t *a, uint8_t *b, int len) {
	unsigned short e = 0;
	for (unsigned int i=0; i<len; i++) {
		res[i] = a[i] - b[i] - e;
		e = (res[i]>a[i]);
	}

	return e;
}

// Sum function
int sum_(uint8_t *res, uint8_t *a, uint8_t *b, int len) {
	unsigned short e = 0;
	for (unsigned int i=0; i<len; i++) {
		res[i] = a[i] + b[i] + e;
		e = (res[i]<a[i]);
	}
	return e;
}

// Modular sum
void mod_sub(uint8_t *res, uint8_t *a, uint8_t *b, uint8_t *p, int len) {
	if (compare_array(a, p, len) >= 0) {
		print_uint8_t(a, len, "Wrong input value a");
		return;
	} else if(compare_array(b, p, len) >= 0) {
		print_uint8_t(b, len, "Wrong input value b");
		return;
	}
	unsigned short e = sub_(res, a, b, len);
	if (e == 1) sum_(res, res, p, len);
	printf("%d\n", e);
	return;
}

int sub(int a, int b, int p) {

	int res = (a - b)%p;
	return (res < 0) ? p+res : res;
}

// Modular sum
void mod_sum(uint8_t *res, uint8_t *a, uint8_t *b, uint8_t *p, int len) {
	if (compare_array(a, p, len) >= 0) {
		print_uint8_t(a, len, "Wrong input value a");
		return;
	} else if(compare_array(b, p, len) >= 0) {
		print_uint8_t(b, len, "Wrong input value b");
		return;
	}
	unsigned short e = sum_(res, a, b, len);
	if (e == 1) 
		sub_(res, res, p, len);
	else {
		short dif = compare_array(res, p, len);
		if (dif > 0) sub_(res, res, p, len); 
		else if (dif == 0){
			for (int i = len-1; i >= 0; i--)
				res[i] = 0;
		}
	}
	return;
}

int sum(int a, int b, int p) {
	int res = (a + b)%p;
	return (res < 0) ? p+res : res;
}

*/
