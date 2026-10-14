/*
 * latcalc/rns.h -- the rod abacus: residue number system with CRT read-back.
 *
 * A number is copied onto rods; rod i stores the remainder mod m_i.  Addition,
 * subtraction and multiplication act rod by rod with no carries between rods.
 * With pairwise coprime moduli the rods determine the number modulo
 * M = m_1 * ... * m_n (Chinese remainder theorem) and lc_rns_decode reads it
 * back exactly (Lean: LatticeCalc.decode_encode in LatticeCalc/Rods.lean).
 */
#ifndef LATCALC_RNS_H
#define LATCALC_RNS_H

#include "latcalc/bigint.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    size_t n;
    uint32_t *m;        /* moduli, each >= 2, pairwise coprime */
    lc_int M;           /* product */
    lc_int *basis;      /* CRT basis e_i: e_i = 1 mod m_i, 0 mod m_j */
} lc_rns;

/* LC_EDOMAIN if some modulus < 2 or two moduli share a factor. */
int  lc_rns_init(lc_rns *ctx, const uint32_t *moduli, size_t n);
void lc_rns_clear(lc_rns *ctx);

int lc_rns_encode(const lc_rns *ctx, uint32_t *res, const lc_int *x);
int lc_rns_decode(const lc_rns *ctx, lc_int *x, const uint32_t *res);          /* in [0, M) */
int lc_rns_decode_signed(const lc_rns *ctx, lc_int *x, const uint32_t *res);   /* in (-M/2, M/2] */
void lc_rns_add(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b);
/* add/sub/mul expect reduced residues (res[i] < m[i]), as produced by lc_rns_encode. */
void lc_rns_sub(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b);
void lc_rns_mul(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_RNS_H */
