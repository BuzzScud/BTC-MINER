/* latcalc -- exact base-60 fixed point (mirror of LatticeCalc/Base60.lean). */
#include <stdlib.h>
#include "latcalc/sexa.h"

void lc_sexa_init(lc_sexa *x) { lc_int_init(&x->num); x->places = 0; }
void lc_sexa_clear(lc_sexa *x) { lc_int_clear(&x->num); x->places = 0; }

int lc_sexa_copy(lc_sexa *r, const lc_sexa *x)
{
    int e = lc_int_copy(&r->num, &x->num);
    if (!e) r->places = x->places;
    return e;
}

int lc_sexa_set_int(lc_sexa *r, const lc_int *n) { r->places = 0; return lc_int_copy(&r->num, n); }
int lc_sexa_set_i64(lc_sexa *r, int64_t n) { r->places = 0; return lc_int_set_i64(&r->num, n); }

int lc_sexa_from_decimal(lc_sexa *r, const lc_int *a, unsigned long k)
{
    lc_int p; lc_int_init(&p);
    int e = lc_int_ui_pow_ui(&p, 6, k);           /* a/10^k = a*6^k / 60^k */
    if (!e) e = lc_int_mul(&r->num, a, &p);
    if (!e) r->places = k;
    lc_int_clear(&p);
    return e;
}

int lc_sexa_to_rat(lc_rat *r, const lc_sexa *x)
{
    lc_int p; lc_int_init(&p);
    int e = lc_int_ui_pow_ui(&p, 60, x->places);
    if (!e) e = lc_rat_set_frac(r, &x->num, &p);
    lc_int_clear(&p);
    return e;
}

int lc_sexa_round_rat(lc_sexa *r, const lc_rat *q, unsigned long k, lc_round mode)
{
    int e = lc_rat_round_places(&r->num, q, 60, (unsigned)k, mode);
    if (!e) r->places = k;
    return e;
}

int lc_sexa_floor_rat(lc_sexa *r, const lc_rat *q, unsigned long k)
{
    return lc_sexa_round_rat(r, q, k, LC_ROUND_FLOOR);
}

int lc_sexa_from_rat(lc_sexa *r, const lc_rat *q)
{
    if (!lc_rat_is_finite_in_base(q, 60)) return LC_EINEXACT;
    size_t pre = 0, per = 0;
    int e = lc_rat_expansion_shape(q, 60, 1, &pre, &per);
    if (e) return e;
    return lc_sexa_round_rat(r, q, pre, LC_ROUND_FLOOR);   /* exact at `pre` places */
}

int lc_sexa_shift(lc_sexa *r, const lc_sexa *a, unsigned long k)
{
    lc_int p; lc_int_init(&p);
    int e = lc_int_ui_pow_ui(&p, 60, k);
    if (!e) e = lc_int_mul(&r->num, &a->num, &p);
    if (!e) r->places = a->places + k;
    lc_int_clear(&p);
    return e;
}

int lc_sexa_add(lc_sexa *r, const lc_sexa *a, const lc_sexa *b)
{
    unsigned long m = a->places > b->places ? a->places : b->places;
    lc_sexa x, y; lc_sexa_init(&x); lc_sexa_init(&y);
    int e = lc_sexa_shift(&x, a, m - a->places);
    if (!e) e = lc_sexa_shift(&y, b, m - b->places);
    if (!e) e = lc_int_add(&r->num, &x.num, &y.num);
    if (!e) r->places = m;
    lc_sexa_clear(&x); lc_sexa_clear(&y);
    return e;
}

int lc_sexa_neg(lc_sexa *r, const lc_sexa *a)
{
    int e = lc_int_neg(&r->num, &a->num);
    if (!e) r->places = a->places;
    return e;
}

int lc_sexa_sub(lc_sexa *r, const lc_sexa *a, const lc_sexa *b)
{
    lc_sexa nb; lc_sexa_init(&nb);
    int e = lc_sexa_neg(&nb, b);
    if (!e) e = lc_sexa_add(r, a, &nb);
    lc_sexa_clear(&nb);
    return e;
}

int lc_sexa_mul(lc_sexa *r, const lc_sexa *a, const lc_sexa *b)
{
    unsigned long pl = a->places + b->places;
    int e = lc_int_mul(&r->num, &a->num, &b->num);
    if (!e) r->places = pl;
    return e;
}

int lc_sexa_normalize(lc_sexa *r, const lc_sexa *a)
{
    int e = lc_sexa_copy(r, a);
    while (!e && r->places > 0 && lc_int_mod_u32(&r->num, 60) == 0) {
        e = lc_int_divmod_u32(&r->num, NULL, &r->num, 60);
        r->places--;
    }
    return e;
}

int lc_is_regular_u64(uint64_t n)
{
    if (n == 0) return 0;
    while (n % 2 == 0) n /= 2;
    while (n % 3 == 0) n /= 3;
    while (n % 5 == 0) n /= 5;
    return n == 1;
}

int lc_sexa_div_regular(lc_sexa *r, const lc_sexa *a, uint64_t n)
{
    if (n == 0) return LC_EDIVZERO;
    if (!lc_is_regular_u64(n)) return LC_EINEXACT;
    /* find j with n | 60^j, then a/n = a*(60^j/n) / 60^(places+j) */
    lc_int p, nn, c; lc_int_init(&p); lc_int_init(&nn); lc_int_init(&c);
    int e = lc_int_set_u64(&nn, n);
    unsigned long j = 0;
    if (!e) e = lc_int_set_i64(&p, 1);
    while (!e && !lc_int_divisible(&p, &nn)) { e = lc_int_mul_i64(&p, &p, 60); j++; }
    if (!e) e = lc_int_divexact(&c, &p, &nn);
    if (!e) e = lc_int_mul(&r->num, &a->num, &c);
    if (!e) r->places = a->places + j;
    lc_int_clear(&p); lc_int_clear(&nn); lc_int_clear(&c);
    return e;
}

int lc_sexa_cmp(const lc_sexa *a, const lc_sexa *b)
{
    lc_sexa d; lc_sexa_init(&d);
    lc_sexa_sub(&d, a, b);
    int s = lc_int_sign(&d.num);
    lc_sexa_clear(&d);
    return s;
}

int lc_sexa_set_str(lc_sexa *r, const char *s)
{
    lc_rat q; lc_rat_init(&q);
    int e = lc_rat_set_str(&q, s);
    if (!e) e = lc_sexa_from_rat(r, &q);
    lc_rat_clear(&q);
    return e;
}

char *lc_sexa_get_str(const lc_sexa *x)
{
    lc_rat q; lc_rat_init(&q);
    char *s = NULL;
    if (!lc_sexa_to_rat(&q, x)) s = lc_rat_get_sexa(&q, (unsigned)x->places, LC_ROUND_FLOOR);
    lc_rat_clear(&q);
    return s;
}
