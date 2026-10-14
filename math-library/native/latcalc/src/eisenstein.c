/* latcalc -- hexagonal lattice and flower tilings. */
#include <stdlib.h>
#include <math.h>
#include "latcalc/eisenstein.h"

void lc_eis_init(lc_eis *z) { lc_int_init(&z->a); lc_int_init(&z->b); }
void lc_eis_clear(lc_eis *z) { lc_int_clear(&z->a); lc_int_clear(&z->b); }

int lc_eis_copy(lc_eis *r, const lc_eis *z)
{
    int e = lc_int_copy(&r->a, &z->a);
    if (!e) e = lc_int_copy(&r->b, &z->b);
    return e;
}

int lc_eis_set_i64(lc_eis *r, int64_t a, int64_t b)
{
    int e = lc_int_set_i64(&r->a, a);
    if (!e) e = lc_int_set_i64(&r->b, b);
    return e;
}

int lc_eis_equal(const lc_eis *x, const lc_eis *y)
{
    return lc_int_cmp(&x->a, &y->a) == 0 && lc_int_cmp(&x->b, &y->b) == 0;
}

int lc_eis_add(lc_eis *r, const lc_eis *x, const lc_eis *y)
{
    int e = lc_int_add(&r->a, &x->a, &y->a);
    if (!e) e = lc_int_add(&r->b, &x->b, &y->b);
    return e;
}

int lc_eis_sub(lc_eis *r, const lc_eis *x, const lc_eis *y)
{
    int e = lc_int_sub(&r->a, &x->a, &y->a);
    if (!e) e = lc_int_sub(&r->b, &x->b, &y->b);
    return e;
}

int lc_eis_mul(lc_eis *r, const lc_eis *x, const lc_eis *y)
{
    lc_int ac, bd, ad, bc; lc_int_init(&ac); lc_int_init(&bd); lc_int_init(&ad); lc_int_init(&bc);
    int e = lc_int_mul(&ac, &x->a, &y->a);
    if (!e) e = lc_int_mul(&bd, &x->b, &y->b);
    if (!e) e = lc_int_mul(&ad, &x->a, &y->b);
    if (!e) e = lc_int_mul(&bc, &x->b, &y->a);
    if (!e) e = lc_int_sub(&r->a, &ac, &bd);
    if (!e) e = lc_int_add(&ad, &ad, &bc);
    if (!e) e = lc_int_sub(&r->b, &ad, &bd);
    lc_int_clear(&ac); lc_int_clear(&bd); lc_int_clear(&ad); lc_int_clear(&bc);
    return e;
}

int lc_eis_conj(lc_eis *r, const lc_eis *z)
{
    lc_int t; lc_int_init(&t);
    int e = lc_int_sub(&t, &z->a, &z->b);
    if (!e) e = lc_int_neg(&r->b, &z->b);
    if (!e) lc_int_swap(&r->a, &t);
    lc_int_clear(&t);
    return e;
}

int lc_eis_norm(lc_int *r, const lc_eis *z)
{
    lc_int aa, ab, bb; lc_int_init(&aa); lc_int_init(&ab); lc_int_init(&bb);
    int e = lc_int_mul(&aa, &z->a, &z->a);
    if (!e) e = lc_int_mul(&ab, &z->a, &z->b);
    if (!e) e = lc_int_mul(&bb, &z->b, &z->b);
    if (!e) e = lc_int_sub(&aa, &aa, &ab);
    if (!e) e = lc_int_add(r, &aa, &bb);
    lc_int_clear(&aa); lc_int_clear(&ab); lc_int_clear(&bb);
    return e;
}

int lc_eis_pow_ui(lc_eis *r, const lc_eis *z, unsigned long ex)
{
    lc_eis base, acc; lc_eis_init(&base); lc_eis_init(&acc);
    int e = lc_eis_copy(&base, z);
    if (!e) e = lc_eis_set_i64(&acc, 1, 0);
    while (!e && ex) {
        if (ex & 1) e = lc_eis_mul(&acc, &acc, &base);
        ex >>= 1;
        if (!e && ex) e = lc_eis_mul(&base, &base, &base);
    }
    if (!e) e = lc_eis_copy(r, &acc);
    lc_eis_clear(&base); lc_eis_clear(&acc);
    return e;
}

void lc_eis_to_complex(const lc_eis *z, double *re, double *im)
{
    double a = lc_int_get_double(&z->a), b = lc_int_get_double(&z->b);
    *re = a - 0.5 * b;
    *im = b * (sqrt(3.0) / 2.0);
}

int lc_eis_hexdist(lc_int *r, const lc_eis *z)
{
    lc_int x, y, d;
    lc_int_init(&x); lc_int_init(&y); lc_int_init(&d);
    int e = lc_int_abs(&x, &z->a);
    if (!e) e = lc_int_abs(&y, &z->b);
    if (!e) e = lc_int_sub(&d, &z->a, &z->b);
    if (!e) e = lc_int_abs(&d, &d);
    if (!e) {
        const lc_int *m = lc_int_cmp(&x, &y) > 0 ? &x : &y;
        if (lc_int_cmp(&d, m) > 0) m = &d;
        e = lc_int_copy(r, m);
    }
    lc_int_clear(&x); lc_int_clear(&y); lc_int_clear(&d);
    return e;
}

uint64_t lc_eis_hexdist_u64(int64_t a, int64_t b)
{
    /* Unsigned subtraction is defined even at INT64_MIN/MAX. The largest
       mathematical |a-b| is UINT64_MAX, so every input pair fits this ABI. */
    uint64_t ua = (uint64_t)a, ub = (uint64_t)b;
    uint64_t x = a < 0 ? UINT64_C(0) - ua : ua;
    uint64_t y = b < 0 ? UINT64_C(0) - ub : ub;
    uint64_t d = a >= b ? ua - ub : ub - ua;
    uint64_t m = x > y ? x : y;
    return m > d ? m : d;
}

int64_t lc_eis_hexdist_i64(int64_t a, int64_t b)
{
    uint64_t distance = lc_eis_hexdist_u64(a, b);
    return distance <= INT64_MAX ? (int64_t)distance : -1;
}

/* ------------------------------------------------------------------ */

static int64_t mod64(int64_t a, int64_t m) { int64_t r = a % m; return r < 0 ? r + m : r; }

static int64_t inv_mod(int64_t a, int64_t m)
{
    int64_t g = m, x = 0, x1 = 1, a1 = mod64(a, m);
    while (a1) { int64_t q = g / a1, t = g - q * a1; g = a1; a1 = t; t = x - q * x1; x = x1; x1 = t; }
    return g == 1 ? mod64(x, m) : -1;
}

int lc_hexbase_init(lc_hexbase *hb, unsigned k)
{
    hb->k = k; hb->digit = NULL;
    lc_eis_init(&hb->beta); lc_eis_init(&hb->beta_conj);
    if (k == 0 || k > 20000) return LC_EDOMAIN;
    int64_t N = 3 * (int64_t)k * k + 3 * (int64_t)k + 1;
    hb->N = (uint32_t)N;
    int64_t kinv = inv_mod((int64_t)k, N);
    if (kinv < 0) return LC_EDOMAIN;
    int64_t r = mod64(-(int64_t)(2 * k + 1) * kinv, N);
    if (mod64(r * r + r + 1, N) != 0) return LC_EDOMAIN;
    hb->root = (uint32_t)r;
    hb->digit = malloc((size_t)N * sizeof *hb->digit);
    char *seen = calloc((size_t)N, 1);
    if (!hb->digit || !seen) { free(hb->digit); free(seen); hb->digit = NULL; return LC_ENOMEM; }
    int64_t K = (int64_t)k;
    size_t count = 0;
    int ok = 1;
    for (int64_t a = -K; a <= K && ok; a++)
        for (int64_t b = -K; b <= K && ok; b++) {
            if (lc_eis_hexdist_i64(a, b) > K) continue;
            int64_t res = mod64(a + b * r, N);
            if (seen[res]) { ok = 0; break; }
            seen[res] = 1;
            hb->digit[res][0] = (int32_t)a; hb->digit[res][1] = (int32_t)b;
            count++;
        }
    free(seen);
    if (!ok || count != (size_t)N) { free(hb->digit); hb->digit = NULL; return LC_EDOMAIN; }
    int e = lc_eis_set_i64(&hb->beta, 2 * K + 1, K);
    if (!e) e = lc_eis_conj(&hb->beta_conj, &hb->beta);
    return e;
}

void lc_hexbase_clear(lc_hexbase *hb)
{
    free(hb->digit); hb->digit = NULL;
    lc_eis_clear(&hb->beta); lc_eis_clear(&hb->beta_conj);
}

uint32_t lc_hexbase_residue(const lc_hexbase *hb, const lc_eis *z)
{
    uint64_t a = lc_int_mod_u32(&z->a, hb->N), b = lc_int_mod_u32(&z->b, hb->N);
    return (uint32_t)((a + b * hb->root) % hb->N);
}

int lc_hexbase_split(const lc_hexbase *hb, const lc_eis *z, int32_t d[2], lc_eis *w)
{
    uint32_t res = lc_hexbase_residue(hb, z);
    int32_t da = hb->digit[res][0], db = hb->digit[res][1];
    lc_eis t, dd; lc_eis_init(&t); lc_eis_init(&dd);
    int e = lc_eis_set_i64(&dd, da, db);
    if (!e) e = lc_eis_sub(&t, z, &dd);
    if (!e) e = lc_eis_mul(&t, &t, &hb->beta_conj);      /* (z - d) * conj(beta) = N * w */
    lc_int Nn; lc_int_init(&Nn);
    if (!e) e = lc_int_set_u64(&Nn, hb->N);
    if (!e) e = lc_int_divexact(&w->a, &t.a, &Nn);
    if (!e) e = lc_int_divexact(&w->b, &t.b, &Nn);
    if (!e) { d[0] = da; d[1] = db; }
    lc_int_clear(&Nn); lc_eis_clear(&t); lc_eis_clear(&dd);
    return e;
}

int lc_hexbase_address(const lc_hexbase *hb, const lc_eis *z, size_t n, int32_t (*digits)[2],
                       lc_eis *rem)
{
    lc_eis cur; lc_eis_init(&cur);
    int e = lc_eis_copy(&cur, z);
    for (size_t i = 0; !e && i < n; i++) e = lc_hexbase_split(hb, &cur, digits[i], &cur);
    if (!e) e = lc_eis_copy(rem, &cur);
    lc_eis_clear(&cur);
    return e;
}

int lc_hexbase_from_address(const lc_hexbase *hb, lc_eis *z, size_t n, const int32_t (*digits)[2],
                            const lc_eis *rem)
{
    lc_eis cur, d; lc_eis_init(&cur); lc_eis_init(&d);
    int e = lc_eis_copy(&cur, rem);
    for (size_t i = n; !e && i-- > 0;) {
        e = lc_eis_mul(&cur, &cur, &hb->beta);
        if (!e) e = lc_eis_set_i64(&d, digits[i][0], digits[i][1]);
        if (!e) e = lc_eis_add(&cur, &cur, &d);
    }
    if (!e) e = lc_eis_copy(z, &cur);
    lc_eis_clear(&cur); lc_eis_clear(&d);
    return e;
}
