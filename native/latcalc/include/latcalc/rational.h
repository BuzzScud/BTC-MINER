/*
 * latcalc/rational.h -- exact rational numbers over lc_int.
 *
 * An lc_rat is always normalised: den > 0 and gcd(num, den) = 1, so equal
 * numbers have equal representations.  This is the universal exchange type
 * of the library: every user input (integer, decimal, fraction, scientific
 * notation, repeating decimal, base-60 string, IEEE double) converts to an
 * lc_rat without loss, and every exact type of the library converts to it.
 */
#ifndef LATCALC_RATIONAL_H
#define LATCALC_RATIONAL_H

#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    lc_int num;
    lc_int den;
} lc_rat;

typedef enum {
    LC_ROUND_FLOOR,      /* toward -infinity */
    LC_ROUND_CEIL,       /* toward +infinity */
    LC_ROUND_TRUNC,      /* toward zero */
    LC_ROUND_HALF_EVEN,  /* to nearest, ties to even */
    LC_ROUND_HALF_UP     /* to nearest, ties away from zero */
} lc_round;

void lc_rat_init(lc_rat *q);
void lc_rat_clear(lc_rat *q);
int  lc_rat_copy(lc_rat *r, const lc_rat *q);

/* Construction */
int lc_rat_set_int(lc_rat *r, const lc_int *n);
int lc_rat_set_frac(lc_rat *r, const lc_int *num, const lc_int *den);   /* normalises */
int lc_rat_set_i64(lc_rat *r, int64_t num, int64_t den);
int lc_rat_set_double(lc_rat *r, double x);          /* exact: every finite double is a dyadic rational */
double lc_rat_get_double(const lc_rat *q);           /* correctly rounded up to one final rounding step */

/*
 * Text input.  Accepted forms (optional sign, surrounding spaces):
 *   integer           42, -17, 1_000_000
 *   fraction          22/7, -3/4
 *   decimal           3.14159, .5, -12.375
 *   scientific        1.5e-3, 6.02E23
 *   repeating decimal 0.1(6)  = 1/6,   0.(142857) = 1/7
 *   base 60           1,2;30  = 62.5,  3;08,29,44,   0;(08,34,17) = 1/7,  1,0,1 = 3601
 *                     (a ';' marks base 60: digits 0..59 separated by ',')
 */
int lc_rat_set_str(lc_rat *r, const char *s);

/* Text output */
char *lc_rat_get_str(const lc_rat *q);                          /* "n" or "n/d" */
char *lc_rat_get_decimal(const lc_rat *q, unsigned digits, lc_round mode); /* fixed digits */
char *lc_rat_get_sexa(const lc_rat *q, unsigned places, lc_round mode);    /* "a,b;c,d" */

/*
 * Exact positional expansion in base 2..3600 with the repeating block marked:
 * base 10: "0.1(6)", base 60: "0;(08,34,17)".  If the preperiod plus period is
 * longer than max_digits the output is truncated and ends in "...".
 */
char *lc_rat_get_expansion(const lc_rat *q, unsigned base, size_t max_digits);

/* Structural data of the base-b expansion of |q|: *pre = number of
 * non-repeating places, *period = length of the repeating block (0 if the
 * expansion terminates).  LC_ERANGE if the period exceeds max_period. */
int lc_rat_expansion_shape(const lc_rat *q, unsigned base, size_t max_period,
                           size_t *pre, size_t *period);

/* 1 if q has a finite expansion in the base (every prime of den divides base). */
int lc_rat_is_finite_in_base(const lc_rat *q, unsigned base);

/* Arithmetic */
int lc_rat_add(lc_rat *r, const lc_rat *a, const lc_rat *b);
int lc_rat_sub(lc_rat *r, const lc_rat *a, const lc_rat *b);
int lc_rat_mul(lc_rat *r, const lc_rat *a, const lc_rat *b);
int lc_rat_div(lc_rat *r, const lc_rat *a, const lc_rat *b);
int lc_rat_neg(lc_rat *r, const lc_rat *a);
int lc_rat_abs(lc_rat *r, const lc_rat *a);
int lc_rat_inv(lc_rat *r, const lc_rat *a);
int lc_rat_pow_si(lc_rat *r, const lc_rat *a, long e);
int lc_rat_cmp(const lc_rat *a, const lc_rat *b);
int lc_rat_sign(const lc_rat *a);
int lc_rat_is_int(const lc_rat *a);

/* Rounding to an integer, and to k places in a base: *out = round(q * base^k). */
int lc_rat_round(lc_int *out, const lc_rat *q, lc_round mode);
int lc_rat_round_places(lc_int *out, const lc_rat *q, unsigned base, unsigned k, lc_round mode);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_RATIONAL_H */
