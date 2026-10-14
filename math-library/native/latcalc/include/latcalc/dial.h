/*
 * latcalc/dial.h -- modular "dial" arithmetic on N marks (N < 2^32).
 *
 * Formulas on the dial are polynomials evaluated mod N (chord diagrams),
 * step-k walks form gcd(N, k) star polygons, and x -> m x is a symmetry of the
 * dial exactly when gcd(m, N) = 1 (Lean: LatticeCalc/Dial.lean).  On the
 * 360-dial the squares-to-one are the 16 marks 1, 19, 71, 89, ..., 359 and 19
 * is the least of them after 1 (Lean: LatticeCalc.sqrt_one_mod360,
 * nineteen_least); 361 = 19^2 = 1 on every dial whose size divides 360
 * (Lean: sq_nineteen_mod_eq_one_iff).
 */
#ifndef LATCALC_DIAL_H
#define LATCALC_DIAL_H

#include <stddef.h>
#include <stdint.h>
#include "latcalc/common.h"

#ifdef __cplusplus
extern "C" {
#endif

uint64_t lc_gcd_u64(uint64_t a, uint64_t b);
uint32_t lc_mulmod_u32(uint32_t a, uint32_t b, uint32_t N);
uint32_t lc_powmod_u32(uint32_t a, uint64_t e, uint32_t N);

/* f(x) mod N for f = coef[0] + coef[1] x + ... + coef[deg] x^deg (signed coefficients) */
uint32_t lc_dial_poly(const int64_t *coef, size_t deg, uint32_t x, uint32_t N);
/* chords: out[x] = f(x) mod N for every mark x in [0, N) */
int lc_dial_chords(const int64_t *coef, size_t deg, uint32_t N, uint32_t *out);

/* number of disjoint star polygons traced by step k on N marks */
uint64_t lc_dial_star_cycles(uint64_t N, uint64_t k);
/* multiplicative order of a mod N, 0 if gcd(a, N) != 1 */
uint64_t lc_dial_order(uint32_t a, uint32_t N);
/* the marks x in [0, N) with x^2 = 1 (mod N); returns their number, writes up to cap */
size_t lc_dial_sqrt_one(uint32_t N, uint32_t *out, size_t cap);
/* 1 if x -> m x permutes the N marks */
int lc_dial_is_symmetry(uint32_t m, uint32_t N);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_DIAL_H */
