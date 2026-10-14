/* latcalc -- fixed-scale arithmetic (mirror of LatticeCalc/Scale361.lean). */
#include "latcalc/scaled.h"

int lc_scale_init_u64(lc_scale *ctx, uint64_t S)
{
    lc_int_init(&ctx->S);
    if (S == 0) return LC_EDOMAIN;
    return lc_int_set_u64(&ctx->S, S);
}

int lc_scale_init(lc_scale *ctx, const lc_int *S)
{
    lc_int_init(&ctx->S);
    if (lc_int_sign(S) <= 0) return LC_EDOMAIN;
    return lc_int_copy(&ctx->S, S);
}

int lc_scale_init_product(lc_scale *ctx, const lc_scale *a, const lc_scale *b)
{
    lc_int_init(&ctx->S);
    return lc_int_mul(&ctx->S, &a->S, &b->S);
}

int lc_scale_init_pow(lc_scale *ctx, uint64_t base, unsigned long k)
{
    lc_int_init(&ctx->S);
    if (base == 0) return LC_EDOMAIN;
    return lc_int_ui_pow_ui(&ctx->S, (unsigned long)base, k);
}

void lc_scale_clear(lc_scale *ctx) { lc_int_clear(&ctx->S); }

void lc_scaled_init(lc_scaled *x) { lc_int_init(&x->raw); }
void lc_scaled_clear(lc_scaled *x) { lc_int_clear(&x->raw); }

int lc_scaled_from_int(const lc_scale *ctx, lc_scaled *r, const lc_int *n)
{
    return lc_int_mul(&r->raw, n, &ctx->S);
}

int lc_scaled_representable(const lc_scale *ctx, const lc_rat *q)
{
    return lc_int_divisible(&ctx->S, &q->den);
}

int lc_scaled_from_rat(const lc_scale *ctx, lc_scaled *r, const lc_rat *q)
{
    if (!lc_scaled_representable(ctx, q)) return LC_EINEXACT;
    lc_int c; lc_int_init(&c);
    int e = lc_int_divexact(&c, &ctx->S, &q->den);    /* raw = num * (S / den) */
    if (!e) e = lc_int_mul(&r->raw, &q->num, &c);
    lc_int_clear(&c);
    return e;
}

int lc_scaled_from_rat_round(const lc_scale *ctx, lc_scaled *r, const lc_rat *q, lc_round mode)
{
    lc_rat t; lc_rat_init(&t);
    lc_rat s; lc_rat_init(&s);
    int e = lc_rat_set_int(&s, &ctx->S);
    if (!e) e = lc_rat_mul(&t, q, &s);
    if (!e) e = lc_rat_round(&r->raw, &t, mode);
    lc_rat_clear(&t); lc_rat_clear(&s);
    return e;
}

int lc_scaled_to_rat(const lc_scale *ctx, lc_rat *r, const lc_scaled *x)
{
    return lc_rat_set_frac(r, &x->raw, &ctx->S);
}

int lc_scaled_add(lc_scaled *r, const lc_scaled *a, const lc_scaled *b) { return lc_int_add(&r->raw, &a->raw, &b->raw); }
int lc_scaled_sub(lc_scaled *r, const lc_scaled *a, const lc_scaled *b) { return lc_int_sub(&r->raw, &a->raw, &b->raw); }

int lc_scaled_mul_exact(const lc_scale *ctx, lc_scaled *r, const lc_scaled *a, const lc_scaled *b)
{
    lc_int p; lc_int_init(&p);
    int e = lc_int_mul(&p, &a->raw, &b->raw);
    if (!e) e = lc_int_divexact(&p, &p, &ctx->S);
    if (!e) lc_int_swap(&r->raw, &p);
    lc_int_clear(&p);
    return e;
}

int lc_scaled_mul_round(const lc_scale *ctx, lc_scaled *r, const lc_scaled *a, const lc_scaled *b,
                        lc_round mode)
{
    lc_rat t; lc_rat_init(&t);
    lc_int p; lc_int_init(&p);
    int e = lc_int_mul(&p, &a->raw, &b->raw);
    if (!e) e = lc_rat_set_frac(&t, &p, &ctx->S);
    if (!e) e = lc_rat_round(&r->raw, &t, mode);
    lc_rat_clear(&t); lc_int_clear(&p);
    return e;
}

int lc_scaled_rescale(const lc_scale *from, const lc_scale *to, lc_scaled *r, const lc_scaled *x)
{
    lc_rat q; lc_rat_init(&q);
    int e = lc_scaled_to_rat(from, &q, x);
    if (!e) e = lc_scaled_from_rat(to, r, &q);
    lc_rat_clear(&q);
    return e;
}
