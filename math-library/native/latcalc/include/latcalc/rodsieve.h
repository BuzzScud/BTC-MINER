/*
 * latcalc/rodsieve.h -- rod sieves: excluding powers along a linear recurrence.
 *
 * Setting.  An integer 2x2 matrix F and start vectors s_1, ..., s_n define orbits
 * v_0 = s, v_{k+1} = F v_k; z_k is one coordinate of v_k.  Question: can z_k be a power b^j of a
 * prime b with j >= e?  (Example: the Mersenne flowers, 3y^2 + 5 = 2z^2, F = [[5,4],[6,5]],
 * starts (1,2), (3,4), b = 2, e = 5; Lean: MersenneFlowerAll.)
 *
 * A rod-sieve certificate is a set of rods: the rod b^e and odd prime rods p_1..p_r, with
 *   (a) F^L = I on every rod (mod M = b^e p_1 ... p_r), so every orbit reads periodically, period L;
 *   (b) b^Q = 1 mod M' = p_1 ... p_r;
 *   (c) for every start and every r < L: if the b^e rod reads 0 at z_r, then no j < Q has b^j equal
 *       to z_r on all odd rods.
 * Then z_k = b^j with j >= e is impossible: z_k would read 0 on the b^e rod and b^(j mod Q) on the
 * odd rods, at position k mod L.  The Lean kernel checks certificates of this shape
 * (MersenneFlowerAll.sieve_check); lc_rodsieve_verify checks them here with big integers read on
 * the rod abacus (lc_rns).
 *
 * lc_rodsieve_find searches: for L = L0, 2 L0, ... (L0 = the period of F on the b^e rod) it
 * collects the primes p <= pmax on which F^L = I, and adds them greedily while Q stays <= Qmax,
 * until no residue class survives.  Searching the rods jointly (class k mod L together with
 * j mod Q) is what keeps certificates small.
 *
 * These routines have no Lean model; only the certificates they print are re-checked in Lean.
 */
#ifndef LATCALC_RODSIEVE_H
#define LATCALC_RODSIEVE_H

#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

#define LC_RODSIEVE_MAXRODS 32

typedef struct {
    uint32_t b, e;                          /* prime base and exponent: the rod b^e */
    uint32_t bpow;                          /* b^e */
    size_t nrods;                           /* odd prime rods */
    uint32_t rods[LC_RODSIEVE_MAXRODS];
    uint32_t L;                             /* common period of the orbits on all rods */
    uint64_t Q;                             /* period of b^j on the odd rods */
} lc_rodsieve_cert;

/* F = {{f00, f01}, {f10, f11}}; starts[i] = {y, z}; coord = index (0 or 1) of z in the vector.
   Returns LC_OK and fills cert, or LC_EDOMAIN if no certificate exists within the limits
   (Lmax periods multiple, pmax, Qmax), LC_EINVAL on bad arguments. */
int lc_rodsieve_find(lc_rodsieve_cert *cert, const int64_t F[2][2], const int64_t (*starts)[2],
                     size_t nstarts, int coord, uint32_t b, uint32_t e,
                     uint32_t Lmult_max, uint32_t pmax, uint64_t Qmax);

/* Independent check of (a), (b), (c) with big integers and the rod abacus.
   Returns 1 if the certificate is valid, 0 if not, negative on error. */
int lc_rodsieve_verify(const lc_rodsieve_cert *cert, const int64_t F[2][2],
                       const int64_t (*starts)[2], size_t nstarts, int coord);

/* The modulus M = b^e * p_1 * ... * p_r of a certificate. */
int lc_rodsieve_modulus(lc_int *M, const lc_rodsieve_cert *cert);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_RODSIEVE_H */
