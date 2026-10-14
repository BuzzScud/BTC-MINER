/*
 * latcalc/abacus.h -- one shared, resident abacus for many simultaneous formulas.
 *
 * An abacus is a frame of pairwise coprime rods m_0 .. m_{n-1} (each < 2^31).  It is built once,
 * is immutable afterwards and is reference counted, so any number of calculations -- in any
 * number of threads -- can use the same abacus at the same time.  A number on the abacus is a
 * *column*: an array of n small residues owned by the caller.  Calculations read the abacus and
 * write columns; they never modify the abacus.
 *
 *   views   lc_abacus_view(A, idx, k) is a sub-abacus made of pointers into A's rods.  It shares
 *           A's tables (the pairwise rod inverses are referenced, not recomputed); a column on A
 *           restricted to idx is the column of the same number on the view.
 *   merge   lc_abacus_merge(A, B) joins two independent abaci with coprime rods; the capacity
 *           is the product, and columns computed separately are placed side by side.
 *   run     lc_abacus_run executes a program -- a system of formulas that may use each other's
 *           results -- rod by rod over the shared abacus: all formulas advance together on each
 *           rod, and each rod is independent of every other rod.
 *   read    conversion to a positional integer (Garner's mixed radix, small operations until the
 *           final Horner pass) is only needed for output.
 *
 * Lean: LatticeCalc/Verified/AbacusSystem.lean (run_enc, runSys_enc, runProg_spec, relation_iff,
 * run_local, run_view, run_merge, capacity_merge) and RNS.lean (read-back).
 *
 * Rod Montgomery (lc_rmont_*): modular multiplication and powers mod a large odd p with the value
 * held on the rods throughout (fast base extension between two views A and B of one abacus, plus
 * a redundant rod for the exact correction).  Lean: LatticeCalc/Verified/RodMont.lean
 * (montMul_spec, rodPow_spec, montMul_out).
 */
#ifndef LATCALC_ABACUS_H
#define LATCALC_ABACUS_H

#include <stdint.h>
#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct lc_abacus lc_abacus;

/* Build an abacus on the given rods (each 2 <= m < 2^31, pairwise coprime).  NULL on error,
   with *err set (LC_EDOMAIN for bad rods, LC_ENOMEM).  The result has reference count 1. */
lc_abacus *lc_abacus_new(const uint32_t *moduli, size_t n, int *err);
/* The n largest primes below 2^31 (a convenient standard frame). */
lc_abacus *lc_abacus_primes(size_t n, int *err);
lc_abacus *lc_abacus_retain(lc_abacus *a);
void       lc_abacus_release(lc_abacus *a);

size_t          lc_abacus_size(const lc_abacus *a);
const uint32_t *lc_abacus_moduli(const lc_abacus *a);
/* log2 of the capacity (product of the rods), as a double. */
double          lc_abacus_capacity_bits(const lc_abacus *a);
/* For a view: the index of rod i in the root abacus it points into (identity for a root). */
size_t          lc_abacus_origin(const lc_abacus *a, size_t i);

/* A view made of the rods idx[0..k-1] of a (distinct indices).  The view keeps a alive. */
lc_abacus *lc_abacus_view(lc_abacus *a, const size_t *idx, size_t k, int *err);
/* Merge two abaci whose rods are mutually coprime (LC_EDOMAIN otherwise). */
lc_abacus *lc_abacus_merge(const lc_abacus *a, const lc_abacus *b, int *err);

/* Columns (arrays of lc_abacus_size(a) residues). */
int  lc_abacus_encode(const lc_abacus *a, uint32_t *col, const lc_int *x);
void lc_abacus_encode_i64(const lc_abacus *a, uint32_t *col, int64_t x);
int  lc_abacus_decode(const lc_abacus *a, lc_int *x, const uint32_t *col);         /* [0, M) */
int  lc_abacus_decode_signed(const lc_abacus *a, lc_int *x, const uint32_t *col);  /* (-M/2, M/2] */
int  lc_abacus_col_equal(const lc_abacus *a, const uint32_t *c1, const uint32_t *c2);

/* ---- programs: systems of formulas on the shared abacus ---------------------------------- */

enum { LC_AOP_CONST, LC_AOP_COPY, LC_AOP_ADD, LC_AOP_SUB, LC_AOP_MUL, LC_AOP_POW,
       LC_AOP_MULC, LC_AOP_ADDC };

typedef struct {
    int      kind;
    int      dst, a, b;    /* slot numbers */
    int64_t  c;            /* constant for CONST / MULC / ADDC */
    uint64_t e;            /* exponent for POW */
} lc_aop;

/* Run the program on every rod of the abacus.  slots[s] points to a column for slot s; input
   slots must be filled (lc_abacus_encode), output slots are written.  Slots may be reused.
   The abacus is only read, so programs may run concurrently on the same abacus. */
int lc_abacus_run(const lc_abacus *a, const lc_aop *ops, size_t nops, uint32_t *const *slots,
                  size_t nslots);

/* ---- jumps: linear recurrences to any depth, no enumeration ------------------------------ */

/* The sequence u_{n} = c[0] u_{n-1} + c[1] u_{n-2} + ... + c[d-1] u_{n-d}, with u_0..u_{d-1} =
   init[0..d-1]: writes the column of u_N, computed on every rod by a d x d companion-matrix power
   (O(d^3 log N) small operations per rod, each rod independent).  1 <= d <= 8.
   Lean: LatticeCalc/Verified/RodJump.lean (iterate_eq_pow, pow_mulVec_cast, powSq_eq;
   the Soddy counts: soddy_state, soddy_mod). */
int lc_abacus_linrec(const lc_abacus *a, uint32_t *col, const int64_t *c, const int64_t *init,
                     size_t d, uint64_t N);

/* ---- rod Montgomery ------------------------------------------------------------------------ */

typedef struct lc_rmont lc_rmont;

/* Use the first k rods of ab as base A, the next l rods as base B and the rod after that as the
   redundant rod (requires k + l + 1 <= size, l <= redundant rod).  p odd, coprime to M_A, with
   (C p)^2 + k M_A p <= min(M_B, C p) M_A for C = 2k + 2 (checked; LC_EDOMAIN otherwise). */
lc_rmont *lc_rmont_new(lc_abacus *ab, size_t k, size_t l, const lc_int *p, int *err);
void      lc_rmont_free(lc_rmont *c);
/* Smallest (k, l) = (k, k) with 2k + 1 rods of ab that fits p; 0 if none. */
size_t    lc_rmont_fit(const lc_abacus *ab, const lc_int *p);
/* r = b^e mod p, computed with the value on the rods throughout (b >= 0). */
int       lc_rmont_powmod(lc_rmont *c, lc_int *r, const lc_int *b, const lc_int *e);

#ifdef __cplusplus
}
#endif

#endif
