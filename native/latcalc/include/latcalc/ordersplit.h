/*
 * latcalc/ordersplit.h -- order splitting: factor n = p*q from an exponent E that kills
 * every unit mod p and mod q, and read off k = lcm(p-1, q-1).
 *
 * Part of latcalc.  Lean model and proofs: LatticeCalc/Verified/OrderSplit.lean
 *   lc_int_order_split      <-> splitWith   (splitWith_sound, splitWith_pq)
 *   lc_int_qtok             <-> qToK        (qToK_pq)
 *   lc_int_check_lucas_pow  <-> prime_of_factored_witness
 * The C code follows the Lean definitions step for step; it is tested, not proved.
 */
#ifndef LATCALC_ORDERSPLIT_H
#define LATCALC_ORDERSPLIT_H

#include <stddef.h>
#include <stdint.h>
#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

/* For each r in rs[0..nrs): split E = r^v * m with r not dividing m, set x = a^m mod n and walk
   x, x^r, x^(r^2), ..., (v + 1 terms, all mod n), testing g = gcd(x + n - 1, n).
   Returns 1 and sets *g when 1 < g < n (then g is a proper divisor of n: always true, no
   hypotheses -- Lean: splitWith_sound); 0 if no step splits; or a negative error code.
   Completeness (Lean: splitWith_pq): on n = p*q, if a^E = 1 mod p and mod q, the orders of a
   mod p and mod q differ, and rs lists every prime of E, the answer is 1.
   *steps (may be NULL) receives the number of gcd tests made. */
int lc_int_order_split(lc_int *g, const lc_int *n, const lc_int *a, const lc_int *E,
                       const uint32_t *rs, size_t nrs, size_t *steps);

/* Order splitting followed by h = n / g and k = lcm(g - 1, h - 1).  Returns as above. */
int lc_int_qtok(lc_int *g, lc_int *h, lc_int *k, const lc_int *n, const lc_int *a,
                const lc_int *E, const uint32_t *rs, size_t nrs, size_t *steps);

/* Lucas' test with p - 1 = prod qs[i]^es[i]: returns 1 when the product matches,
   a^(p-1) = 1 and a^((p-1)/qs[i]) != 1 (mod p) for every i; 0 otherwise.  If every qs[i] is
   prime, 1 proves p prime (Lean: prime_of_factored_witness).  One modular power per DISTINCT
   prime of p - 1. */
int lc_int_check_lucas_pow(const lc_int *p, const lc_int *a, const uint32_t *qs,
                           const unsigned long *es, size_t nq);

/* Certificate search for a number with completely factored p - 1 = prod qs[i]^es[i]: tries
   witnesses a = 2, 3, ..., wmax - 1 with lc_int_check_lucas_pow and returns the first that passes
   (a proof that p is prime), 0 if none passes (p composite, or no small witness), or a negative
   error code.  Used for the chain 18*10^k + 1 (examples/chain_primes.c). */
long lc_int_find_lucas_witness(const lc_int *p, const uint32_t *qs, const unsigned long *es,
                               size_t nq, long wmax);

/* Deterministic Q-tower prime generator.  Walks a fixed lattice path of exponent pairs (b, c),
   starting at step `start`, sets a so that p = 2^a 3^b 5^c + 1 has exactly `bits` bits, filters
   candidates by small primes and two Miller-Rabin rounds, and returns the first candidate that
   PASSES lc_int_check_lucas_pow with some witness < 1000 -- a deterministic proof that p is prime
   (Lean: prime_of_factored_witness).  On success returns the step index (>= start) and fills
   p, e[0..2] = (a, b, c) and *witness; returns a negative error code on bad arguments.
   Each accepted prime costs 4 modular powers to certify, whatever its size.  How many steps the
   search needs is NOT bounded by any theorem (even the infinitude of such primes is open). */
long lc_int_qtower_prime(lc_int *p, unsigned long bits, unsigned long start, unsigned long e[3],
                         unsigned long *witness);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_ORDERSPLIT_H */
