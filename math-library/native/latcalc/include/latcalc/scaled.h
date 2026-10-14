/*
 * latcalc/scaled.h -- fixed-scale integer arithmetic ("multiply everything by S").
 *
 * With a scale S > 0 the integer raw stands for raw / S.  C counterpart of the
 * Lean type LatticeCalc.Scaled (LatticeCalc/Scale361.lean), where it is proved:
 *   - addition and subtraction are exact at any scale;
 *   - a product needs one division by S and is exact iff S | raw_a * raw_b;
 *   - a fixed scale S represents q exactly iff den(q) | S.  For S = 361 = 19^2
 *     that is only den 1, 19, 361: 361 does NOT clear 1/2, 1/3, 1/5, 1/60;
 *   - a fixed scale S > 1 is not closed under multiplication (1/S * 1/S), so a
 *     consistent scheme must either round (lc_scaled_mul_round) or let the
 *     scale grow (use lc_sexa for powers of 60, or lc_scale_init with S^k).
 *
 * Scales compose: lc_scale_init_product builds S1*S2 (e.g. 60^k * 361), which
 * represents exactly the rationals whose denominator divides S1*S2.
 */
#ifndef LATCALC_SCALED_H
#define LATCALC_SCALED_H

#include "latcalc/rational.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    lc_int S;           /* the scale, > 0 */
} lc_scale;

typedef struct {
    lc_int raw;         /* stands for raw / S */
} lc_scaled;

int  lc_scale_init_u64(lc_scale *ctx, uint64_t S);
int  lc_scale_init(lc_scale *ctx, const lc_int *S);
int  lc_scale_init_product(lc_scale *ctx, const lc_scale *a, const lc_scale *b);
int  lc_scale_init_pow(lc_scale *ctx, uint64_t base, unsigned long k);   /* base^k */
void lc_scale_clear(lc_scale *ctx);

void lc_scaled_init(lc_scaled *x);
void lc_scaled_clear(lc_scaled *x);

int lc_scaled_from_int(const lc_scale *ctx, lc_scaled *r, const lc_int *n);
int lc_scaled_from_rat(const lc_scale *ctx, lc_scaled *r, const lc_rat *q);  /* exact or LC_EINEXACT */
int lc_scaled_from_rat_round(const lc_scale *ctx, lc_scaled *r, const lc_rat *q, lc_round mode);
int lc_scaled_to_rat(const lc_scale *ctx, lc_rat *r, const lc_scaled *x);
int lc_scaled_representable(const lc_scale *ctx, const lc_rat *q);          /* den(q) | S */

int lc_scaled_add(lc_scaled *r, const lc_scaled *a, const lc_scaled *b);
int lc_scaled_sub(lc_scaled *r, const lc_scaled *a, const lc_scaled *b);
int lc_scaled_mul_exact(const lc_scale *ctx, lc_scaled *r, const lc_scaled *a, const lc_scaled *b);
int lc_scaled_mul_round(const lc_scale *ctx, lc_scaled *r, const lc_scaled *a, const lc_scaled *b,
                        lc_round mode);
/* change of scale: exact iff the value is representable at the new scale */
int lc_scaled_rescale(const lc_scale *from, const lc_scale *to, lc_scaled *r, const lc_scaled *x);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_SCALED_H */
