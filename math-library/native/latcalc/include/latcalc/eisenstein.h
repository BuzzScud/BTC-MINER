/*
 * latcalc/eisenstein.h -- the hexagonal (Eisenstein) lattice Z[w], w^2 + w + 1 = 0,
 * and its self-similar "flower" tilings.
 *
 * A point a + b*w is stored with arbitrary-precision coordinates.  Its squared
 * length is the norm a^2 - ab + b^2, which is multiplicative
 * (Lean: LatticeCalc.Eis.norm_mul in LatticeCalc/Scale361.lean).
 *
 * Hexagonal bases.  For k >= 1 let beta_k = (2k+1) + k*w, of squared length
 * N_k = 3k^2 + 3k + 1 (1, 7, 19, 37, 61, ...; Lean: Eis.norm_beta).  The digit
 * set is the hexagonal ball of radius k (the k-th flower: 7 circles for k = 1,
 * 19 circles for k = 2).  lc_hexbase_split writes z = d + beta_k * w with d a
 * digit; iterating gives base-beta_k addresses, i.e. the lattice as N_k^n copies
 * of itself scaled by beta_k^n.  For k = 2 (beta_2 = 5 + 2w, the prime over 19)
 * the digit set is proved to be a complete residue system and the address to
 * exist and be unique (Lean: Eis.flower19_tiles, address_exists,
 * address_unique in LatticeCalc/Flower19.lean); for k = 1 see the research
 * file FlowerOfLife.lean.  For other k, lc_hexbase_init checks the
 * complete-residue property at run time and returns LC_EDOMAIN if it fails.
 */
#ifndef LATCALC_EISENSTEIN_H
#define LATCALC_EISENSTEIN_H

#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    lc_int a;
    lc_int b;
} lc_eis;

void lc_eis_init(lc_eis *z);
void lc_eis_clear(lc_eis *z);
int  lc_eis_copy(lc_eis *r, const lc_eis *z);
int  lc_eis_set_i64(lc_eis *r, int64_t a, int64_t b);
int  lc_eis_equal(const lc_eis *x, const lc_eis *y);

int lc_eis_add(lc_eis *r, const lc_eis *x, const lc_eis *y);
int lc_eis_sub(lc_eis *r, const lc_eis *x, const lc_eis *y);
int lc_eis_mul(lc_eis *r, const lc_eis *x, const lc_eis *y);  /* (ac-bd) + (ad+bc-bd)w */
int lc_eis_conj(lc_eis *r, const lc_eis *z);                  /* (a-b) - b w */
int lc_eis_norm(lc_int *r, const lc_eis *z);                  /* a^2 - ab + b^2 */
int lc_eis_pow_ui(lc_eis *r, const lc_eis *z, unsigned long e);
void lc_eis_to_complex(const lc_eis *z, double *re, double *im); /* w = -1/2 + (sqrt 3 / 2) i */
/* E coordinates: w^2=-1-w; distance max(|a|, |b|, |a-b|).
   The arbitrary-precision function returns an LC_* status. */
int lc_eis_hexdist(lc_int *r, const lc_eis *z);
uint64_t lc_eis_hexdist_u64(int64_t a, int64_t b);
/* Legacy signed result: -1 if the exact distance exceeds INT64_MAX. */
int64_t lc_eis_hexdist_i64(int64_t a, int64_t b);

typedef struct {
    unsigned k;
    uint32_t N;           /* 3k^2 + 3k + 1 */
    uint32_t root;        /* w -> root (mod N) is the ring map with beta -> 0 */
    int32_t (*digit)[2];  /* digit[r] = hex-ball point with residue r */
    lc_eis beta, beta_conj;
} lc_hexbase;

int  lc_hexbase_init(lc_hexbase *hb, unsigned k);
void lc_hexbase_clear(lc_hexbase *hb);
uint32_t lc_hexbase_residue(const lc_hexbase *hb, const lc_eis *z);
/* z = d + beta * w with d a digit */
int lc_hexbase_split(const lc_hexbase *hb, const lc_eis *z, int32_t d[2], lc_eis *w);
/* n digits (least significant first) and the remainder */
int lc_hexbase_address(const lc_hexbase *hb, const lc_eis *z, size_t n, int32_t (*digits)[2],
                       lc_eis *rem);
/* inverse: d_0 + beta (d_1 + beta (... + beta rem)) */
int lc_hexbase_from_address(const lc_hexbase *hb, lc_eis *z, size_t n, const int32_t (*digits)[2],
                            const lc_eis *rem);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_EISENSTEIN_H */
