/*
 * latcalc/sexa.h -- exact base-60 fixed-point numbers, integers only.
 *
 * An lc_sexa is the pair (num, places) standing for num / 60^places, the C
 * counterpart of the Lean type LatticeCalc.Sexa (LatticeCalc/Base60.lean).
 * Proved there, and mirrored here:
 *   - addition, subtraction and multiplication are exact;
 *   - every terminating decimal a/10^k is exactly (a * 6^k) / 60^k;
 *   - a rational has a finite base-60 form iff its reduced denominator has no
 *     prime factors other than 2, 3, 5 (so 1/7 has none: lc_sexa_from_rat
 *     then returns LC_EINEXACT, and lc_sexa_floor_rat gives the k-place
 *     truncation with error < 60^-k).
 */
#ifndef LATCALC_SEXA_H
#define LATCALC_SEXA_H

#include "latcalc/rational.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    lc_int num;
    unsigned long places;
} lc_sexa;

void lc_sexa_init(lc_sexa *x);
void lc_sexa_clear(lc_sexa *x);
int  lc_sexa_copy(lc_sexa *r, const lc_sexa *x);

int lc_sexa_set_int(lc_sexa *r, const lc_int *n);
int lc_sexa_set_i64(lc_sexa *r, int64_t n);
int lc_sexa_from_decimal(lc_sexa *r, const lc_int *a, unsigned long k);  /* a / 10^k, exact */
int lc_sexa_from_rat(lc_sexa *r, const lc_rat *q);        /* exact or LC_EINEXACT */
int lc_sexa_floor_rat(lc_sexa *r, const lc_rat *q, unsigned long k);   /* floor to k places */
int lc_sexa_round_rat(lc_sexa *r, const lc_rat *q, unsigned long k, lc_round mode);
int lc_sexa_to_rat(lc_rat *r, const lc_sexa *x);

int lc_sexa_add(lc_sexa *r, const lc_sexa *a, const lc_sexa *b);
int lc_sexa_sub(lc_sexa *r, const lc_sexa *a, const lc_sexa *b);
int lc_sexa_mul(lc_sexa *r, const lc_sexa *a, const lc_sexa *b);
int lc_sexa_neg(lc_sexa *r, const lc_sexa *a);
int lc_sexa_shift(lc_sexa *r, const lc_sexa *a, unsigned long k);   /* same value, k more places */
int lc_sexa_normalize(lc_sexa *r, const lc_sexa *a);                /* strip trailing zero places */
/* exact division by n > 0 when n is 5-smooth (2^a 3^b 5^c); LC_EINEXACT otherwise */
int lc_sexa_div_regular(lc_sexa *r, const lc_sexa *a, uint64_t n);
int lc_sexa_cmp(const lc_sexa *a, const lc_sexa *b);

/* "a,b;c,d" notation (the same notation lc_rat_set_str accepts) */
int   lc_sexa_set_str(lc_sexa *r, const char *s);  /* finite base-60 or decimal strings */
char *lc_sexa_get_str(const lc_sexa *x);

/* 1 if n > 0 is 5-smooth (a "regular" number of Babylonian mathematics) */
int lc_is_regular_u64(uint64_t n);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_SEXA_H */
