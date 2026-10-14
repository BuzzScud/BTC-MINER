/*
 * latcalc/bigint.h -- arbitrary-precision signed integers.
 *
 * Part of latcalc, the exact lattice / base-60 calculation library.
 *
 * Representation: sign and magnitude, magnitude in little-endian 32-bit limbs.
 * Every function that produces an lc_int writes into an already-initialised
 * output, and outputs may alias inputs (lc_int_add(&a, &a, &b) is allowed).
 *
 * All functions returning int return LC_OK (0) on success or a negative
 * LC_E* error code (see latcalc/common.h), unless documented otherwise.
 */
#ifndef LATCALC_BIGINT_H
#define LATCALC_BIGINT_H

#include <stddef.h>
#include <stdint.h>
#include "latcalc/common.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int sign;          /* -1, 0 or +1 */
    size_t len;        /* number of used limbs (0 iff value is 0) */
    size_t cap;        /* allocated limbs */
    uint32_t *d;       /* limbs, least significant first */
} lc_int;

/* Life cycle */
void lc_int_init(lc_int *a);
void lc_int_clear(lc_int *a);
int  lc_int_copy(lc_int *r, const lc_int *a);
void lc_int_swap(lc_int *a, lc_int *b);

/* Conversion from / to C integer types */
int  lc_int_set_i64(lc_int *r, int64_t v);
int  lc_int_set_u64(lc_int *r, uint64_t v);
int  lc_int_get_i64(const lc_int *a, int64_t *out);   /* LC_ERANGE if it does not fit */
int  lc_int_get_u64(const lc_int *a, uint64_t *out);  /* LC_ERANGE if negative or too big */
int  lc_int_fits_i64(const lc_int *a);

/* Conversion from / to double.  set_double is exact for integral doubles
 * (LC_EINEXACT if the double has a fractional part, LC_ERANGE for inf/nan);
 * get_double truncates |a| to 64 significant bits, then rounds to double. */
int    lc_int_set_double(lc_int *r, double x);
double lc_int_get_double(const lc_int *a);

/* Text conversion in any base 2..36 (optional leading '+'/'-', '_' separators ignored). */
int    lc_int_set_str(lc_int *r, const char *s, int base);
char  *lc_int_get_str(const lc_int *a, int base);          /* malloc'd; free with lc_free */

/* Queries */
int    lc_int_sign(const lc_int *a);
int    lc_int_is_zero(const lc_int *a);
int    lc_int_is_one(const lc_int *a);
int    lc_int_is_even(const lc_int *a);
int    lc_int_cmp(const lc_int *a, const lc_int *b);
int    lc_int_cmp_abs(const lc_int *a, const lc_int *b);
int    lc_int_cmp_i64(const lc_int *a, int64_t v);
size_t lc_int_bitlen(const lc_int *a);                     /* bits of |a| */

/* Arithmetic */
int lc_int_neg(lc_int *r, const lc_int *a);
int lc_int_abs(lc_int *r, const lc_int *a);
int lc_int_add(lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_sub(lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_mul(lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_add_i64(lc_int *r, const lc_int *a, int64_t v);
int lc_int_mul_i64(lc_int *r, const lc_int *a, int64_t v);
int lc_int_shl(lc_int *r, const lc_int *a, size_t bits);   /* r = a * 2^bits */
int lc_int_shr(lc_int *r, const lc_int *a, size_t bits);   /* r = floor(a / 2^bits) */
int lc_int_pow_ui(lc_int *r, const lc_int *a, unsigned long e);
int lc_int_ui_pow_ui(lc_int *r, unsigned long b, unsigned long e);

/* Division.  tdiv truncates toward zero (C semantics), fdiv rounds toward
 * -infinity (remainder has the sign of b), ediv gives 0 <= r < |b| always.
 * q or r may be NULL.  LC_EDIVZERO when b == 0. */
int lc_int_tdivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_fdivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_edivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_divexact(lc_int *q, const lc_int *a, const lc_int *b); /* LC_EINEXACT if b does not divide a */
int lc_int_divmod_u32(lc_int *q, uint32_t *r, const lc_int *a, uint32_t b); /* truncating */
int lc_int_divisible(const lc_int *a, const lc_int *b);    /* 1 if b | a (b == 0: a == 0) */
uint32_t lc_int_mod_u32(const lc_int *a, uint32_t m);      /* a mod m in [0, m), m > 0 */

/* Number theory */
int lc_int_gcd(lc_int *r, const lc_int *a, const lc_int *b);          /* r >= 0 */
int lc_int_gcdext(lc_int *g, lc_int *x, lc_int *y, const lc_int *a, const lc_int *b); /* g = ax + by */
int lc_int_lcm(lc_int *r, const lc_int *a, const lc_int *b);
int lc_int_invmod(lc_int *r, const lc_int *a, const lc_int *m);       /* LC_EDOMAIN if not invertible */
int lc_int_powmod(lc_int *r, const lc_int *a, const lc_int *e, const lc_int *m); /* e >= 0, m > 0.
                                   Odd m of >= 2 limbs: Montgomery multiplication with a 5-bit
                                   fixed window (no divisions in the loop); otherwise the
                                   square-and-multiply of lc_int_powmod_basic. */
int lc_int_sqrt(lc_int *r, const lc_int *a);                           /* floor sqrt, a >= 0 */
int lc_int_is_probable_prime(const lc_int *a, int rounds);             /* Miller-Rabin: 1/0, or error.
                                                                          PROBABILISTIC for large a;
                                                                          prefer the two below. */
/* Deterministic primality by trial division up to floor(sqrt(a)): 1 prime, 0 not, or error.
   Exact for every a (Lean model: LatticeCalc.Verified.isPrime_iff); cost O(sqrt(a)). */
int lc_int_is_prime(const lc_int *a);

/* A Pratt (Lucas) primality certificate line: p is prime, witnessed by a, where qs[0..nqs)
   are the prime factors of p - 1 with multiplicity, each certified by an EARLIER line. */
typedef struct {
    lc_int p;
    lc_int a;
    const lc_int *qs;
    size_t nqs;
} lc_pratt_entry;

/* Deterministic certificate check: 1 if every line checks and n is the p of some line (then n
   is prime), 0 otherwise, or an error code.  Mirrors LatticeCalc.Verified.checkCert, proved
   sound (checkCert_sound) and complete (exists_cert: every prime has a certificate). */
int lc_int_check_pratt(const lc_pratt_entry *cert, size_t len, const lc_int *n);

/* Test hook: plain square-and-multiply with a division per step (to cross-check the Montgomery
   path of lc_int_powmod). */
int lc_int_powmod_basic(lc_int *r, const lc_int *a, const lc_int *e, const lc_int *m);

/* Test hook: the schoolbook multiplication (to cross-check the Karatsuba path). */
int lc_int_mul_schoolbook(lc_int *r, const lc_int *a, const lc_int *b);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_BIGINT_H */
