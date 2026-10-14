/*
 * latcalc/binrods.h -- binary (Mersenne) rods and the universal twelve-dial.
 *
 * A rod of size 2^w - 1 is a w-bit word: reduction is end-around carry (no division) and
 * doubling is w-bit rotation.  2^a - 1 and 2^b - 1 are coprime exactly when a and b are, so a
 * coprime abacus lifts to coprime word rods (Lean: LatticeCalc/Verified/BinaryRods.lean).
 *
 * The twelve-dial 65520 = 2^4 * (2^12 - 1) = 2^16 - 16 is the largest modulus on which every
 * unit u satisfies u^12 = 1 (Lean: TwelveDial.twelve_dial_iff); it contains the 360 dial
 * (360 * 182 = 65520).  A 16-bit residue splits into a 4-bit rod (mask) and the 12-bit Mersenne
 * rod 4095 (fold); inverses are eleventh powers (Lean: BinaryKernels.lean).
 */
#ifndef LATCALC_BINRODS_H
#define LATCALC_BINRODS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* x mod (2^w - 1) by end-around carry, 1 <= w <= 63 (Lean: BinaryKernels.mmod_eq). */
uint64_t lc_mersenne_mod(uint64_t x, unsigned w);
/* w-bit left rotation of x < 2^w, 1 <= w <= 63: doubling mod 2^w - 1 (Lean: rotl_bits_eq_rotl). */
uint64_t lc_rotl(uint64_t x, unsigned w);

#define LC_DIAL12 65520u
/* split a residue x < 65520 into (x mod 16, x mod 4095) and join it back (Lean: join_split). */
void     lc_dial12_split(uint32_t x, uint32_t *lo4, uint32_t *r12);
uint32_t lc_dial12_join(uint32_t lo4, uint32_t r12);
uint32_t lc_dial12_mul(uint32_t a, uint32_t b);           /* a*b mod 65520 */
uint32_t lc_dial12_pow(uint32_t a, uint64_t e);           /* a^e mod 65520 */
/* inverse of a unit mod 65520 as a^11 (Lean: dial12_inv_spec); 0 if gcd(a, 65520) != 1. */
uint32_t lc_dial12_inv(uint32_t a);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_BINRODS_H */
