/* latcalc -- residue number system (rod abacus). */
#include <stdlib.h>
#include "latcalc/rns.h"

static uint32_t gcd32(uint32_t a, uint32_t b) { while (b) { uint32_t t = a % b; a = b; b = t; } return a; }

int lc_rns_init(lc_rns *ctx, const uint32_t *moduli, size_t n)
{
    ctx->n = 0; ctx->m = NULL; ctx->basis = NULL;
    lc_int_init(&ctx->M);
    if (n == 0) return LC_EINVAL;
    for (size_t i = 0; i < n; i++) {
        if (moduli[i] < 2) return LC_EDOMAIN;
        for (size_t j = 0; j < i; j++) if (gcd32(moduli[i], moduli[j]) != 1) return LC_EDOMAIN;
    }
    ctx->m = malloc(n * sizeof *ctx->m);
    ctx->basis = malloc(n * sizeof *ctx->basis);
    if (!ctx->m || !ctx->basis) { free(ctx->m); free(ctx->basis); ctx->m = NULL; ctx->basis = NULL; return LC_ENOMEM; }
    ctx->n = n;
    for (size_t i = 0; i < n; i++) { ctx->m[i] = moduli[i]; lc_int_init(&ctx->basis[i]); }
    int e = lc_int_set_i64(&ctx->M, 1);
    for (size_t i = 0; !e && i < n; i++) e = lc_int_mul_i64(&ctx->M, &ctx->M, moduli[i]);
    lc_int Mi, mi, inv; lc_int_init(&Mi); lc_int_init(&mi); lc_int_init(&inv);
    for (size_t i = 0; !e && i < n; i++) {
        e = lc_int_set_u64(&mi, moduli[i]);
        if (!e) e = lc_int_divexact(&Mi, &ctx->M, &mi);
        if (!e) e = lc_int_invmod(&inv, &Mi, &mi);
        if (!e) e = lc_int_mul(&ctx->basis[i], &Mi, &inv);
    }
    lc_int_clear(&Mi); lc_int_clear(&mi); lc_int_clear(&inv);
    if (e) lc_rns_clear(ctx);
    return e;
}

void lc_rns_clear(lc_rns *ctx)
{
    for (size_t i = 0; i < ctx->n; i++) lc_int_clear(&ctx->basis[i]);
    free(ctx->basis); free(ctx->m);
    lc_int_clear(&ctx->M);
    ctx->n = 0; ctx->m = NULL; ctx->basis = NULL;
}

int lc_rns_encode(const lc_rns *ctx, uint32_t *res, const lc_int *x)
{
    for (size_t i = 0; i < ctx->n; i++) res[i] = lc_int_mod_u32(x, ctx->m[i]);
    return LC_OK;
}

int lc_rns_decode(const lc_rns *ctx, lc_int *x, const uint32_t *res)
{
    lc_int acc, t; lc_int_init(&acc); lc_int_init(&t);
    int e = LC_OK;
    for (size_t i = 0; !e && i < ctx->n; i++) {
        e = lc_int_mul_i64(&t, &ctx->basis[i], res[i]);
        if (!e) e = lc_int_add(&acc, &acc, &t);
    }
    if (!e) e = lc_int_edivmod(NULL, x, &acc, &ctx->M);
    lc_int_clear(&acc); lc_int_clear(&t);
    return e;
}

int lc_rns_decode_signed(const lc_rns *ctx, lc_int *x, const uint32_t *res)
{
    int e = lc_rns_decode(ctx, x, res);
    if (e) return e;
    lc_int twice; lc_int_init(&twice);
    e = lc_int_shl(&twice, x, 1);
    if (!e && lc_int_cmp(&twice, &ctx->M) > 0) e = lc_int_sub(x, x, &ctx->M);
    lc_int_clear(&twice);
    return e;
}

void lc_rns_add(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b)
{
    for (size_t i = 0; i < ctx->n; i++) r[i] = (uint32_t)(((uint64_t)a[i] + b[i]) % ctx->m[i]);
}

void lc_rns_sub(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b)
{
    for (size_t i = 0; i < ctx->n; i++) r[i] = (uint32_t)(((uint64_t)a[i] + ctx->m[i] - b[i]) % ctx->m[i]);
}

void lc_rns_mul(const lc_rns *ctx, uint32_t *r, const uint32_t *a, const uint32_t *b)
{
    for (size_t i = 0; i < ctx->n; i++) r[i] = (uint32_t)(((uint64_t)a[i] * b[i]) % ctx->m[i]);
}
