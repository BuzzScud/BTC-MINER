/* latcalc -- exact rationals. */
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include "latcalc/rational.h"
#include "strbuf.h"

void lc_rat_init(lc_rat *q) { lc_int_init(&q->num); lc_int_init(&q->den); lc_int_set_i64(&q->den, 1); }
void lc_rat_clear(lc_rat *q) { lc_int_clear(&q->num); lc_int_clear(&q->den); }

int lc_rat_copy(lc_rat *r, const lc_rat *q)
{
    int e = lc_int_copy(&r->num, &q->num);
    if (!e) e = lc_int_copy(&r->den, &q->den);
    return e;
}

/* bring (num, den) to lowest terms with den > 0 */
static int normalise(lc_rat *r)
{
    if (lc_int_is_zero(&r->den)) return LC_EDIVZERO;
    if (lc_int_sign(&r->den) < 0) { lc_int_neg(&r->num, &r->num); lc_int_neg(&r->den, &r->den); }
    if (lc_int_is_zero(&r->num)) return lc_int_set_i64(&r->den, 1);
    lc_int g; lc_int_init(&g);
    int e = lc_int_gcd(&g, &r->num, &r->den);
    if (!e && !lc_int_is_one(&g)) {
        e = lc_int_divexact(&r->num, &r->num, &g);
        if (!e) e = lc_int_divexact(&r->den, &r->den, &g);
    }
    lc_int_clear(&g);
    return e;
}

int lc_rat_set_int(lc_rat *r, const lc_int *n)
{
    int e = lc_int_copy(&r->num, n);
    if (!e) e = lc_int_set_i64(&r->den, 1);
    return e;
}

int lc_rat_set_frac(lc_rat *r, const lc_int *num, const lc_int *den)
{
    if (lc_int_is_zero(den)) return LC_EDIVZERO;
    lc_rat t; lc_rat_init(&t);
    int e = lc_int_copy(&t.num, num);
    if (!e) e = lc_int_copy(&t.den, den);
    if (!e) e = normalise(&t);
    if (!e) { lc_int_swap(&r->num, &t.num); lc_int_swap(&r->den, &t.den); }
    lc_rat_clear(&t);
    return e;
}

int lc_rat_set_i64(lc_rat *r, int64_t num, int64_t den)
{
    if (den == 0) return LC_EDIVZERO;
    int e = lc_int_set_i64(&r->num, num);
    if (!e) e = lc_int_set_i64(&r->den, den);
    if (!e) e = normalise(r);
    return e;
}

int lc_rat_set_double(lc_rat *r, double x)
{
    if (isnan(x) || isinf(x)) return LC_ERANGE;
    if (x == 0.0) return lc_rat_set_i64(r, 0, 1);
    int ex;
    double f = frexp(fabs(x), &ex);
    int64_t m = (int64_t)ldexp(f, 53);         /* exact */
    ex -= 53;
    int e = lc_int_set_i64(&r->num, x < 0 ? -m : m);
    if (!e) e = lc_int_set_i64(&r->den, 1);
    if (!e && ex > 0) e = lc_int_shl(&r->num, &r->num, (size_t)ex);
    if (!e && ex < 0) e = lc_int_shl(&r->den, &r->den, (size_t)(-ex));
    if (!e) e = normalise(r);
    return e;
}

double lc_rat_get_double(const lc_rat *q)
{
    if (lc_int_is_zero(&q->num)) return 0.0;
    lc_int n, d, Q, R; lc_int_init(&n); lc_int_init(&d); lc_int_init(&Q); lc_int_init(&R);
    lc_int_abs(&n, &q->num);
    lc_int_copy(&d, &q->den);
    long shift = 65 - ((long)lc_int_bitlen(&n) - (long)lc_int_bitlen(&d));
    if (shift > 0) lc_int_shl(&n, &n, (size_t)shift);
    else if (shift < 0) lc_int_shl(&d, &d, (size_t)(-shift));
    lc_int_tdivmod(&Q, &R, &n, &d);            /* 2^64 <= Q < 2^66 */
    int sticky = !lc_int_is_zero(&R);
    while (lc_int_bitlen(&Q) > 64) {
        if (!lc_int_is_even(&Q)) sticky = 1;
        lc_int_shr(&Q, &Q, 1);
        shift--;
    }
    uint64_t v = 0;
    lc_int_get_u64(&Q, &v);
    if (sticky) v |= 1;                         /* round-to-odd: the next rounding is correct */
    double res = ldexp((double)v, (int)-shift);
    lc_int_clear(&n); lc_int_clear(&d); lc_int_clear(&Q); lc_int_clear(&R);
    return lc_int_sign(&q->num) < 0 ? -res : res;
}

/* ------------------------------------------------------------------ */
/* arithmetic                                                          */
/* ------------------------------------------------------------------ */

int lc_rat_add(lc_rat *r, const lc_rat *a, const lc_rat *b)
{
    lc_rat t; lc_rat_init(&t);
    lc_int x; lc_int_init(&x);
    int e = lc_int_mul(&t.num, &a->num, &b->den);
    if (!e) e = lc_int_mul(&x, &b->num, &a->den);
    if (!e) e = lc_int_add(&t.num, &t.num, &x);
    if (!e) e = lc_int_mul(&t.den, &a->den, &b->den);
    if (!e) e = normalise(&t);
    if (!e) { lc_int_swap(&r->num, &t.num); lc_int_swap(&r->den, &t.den); }
    lc_rat_clear(&t); lc_int_clear(&x);
    return e;
}

int lc_rat_neg(lc_rat *r, const lc_rat *a)
{
    int e = lc_rat_copy(r, a);
    if (!e) e = lc_int_neg(&r->num, &r->num);
    return e;
}

int lc_rat_abs(lc_rat *r, const lc_rat *a)
{
    int e = lc_rat_copy(r, a);
    if (!e) e = lc_int_abs(&r->num, &r->num);
    return e;
}

int lc_rat_sub(lc_rat *r, const lc_rat *a, const lc_rat *b)
{
    lc_rat nb; lc_rat_init(&nb);
    int e = lc_rat_neg(&nb, b);
    if (!e) e = lc_rat_add(r, a, &nb);
    lc_rat_clear(&nb);
    return e;
}

int lc_rat_mul(lc_rat *r, const lc_rat *a, const lc_rat *b)
{
    lc_rat t; lc_rat_init(&t);
    int e = lc_int_mul(&t.num, &a->num, &b->num);
    if (!e) e = lc_int_mul(&t.den, &a->den, &b->den);
    if (!e) e = normalise(&t);
    if (!e) { lc_int_swap(&r->num, &t.num); lc_int_swap(&r->den, &t.den); }
    lc_rat_clear(&t);
    return e;
}

int lc_rat_inv(lc_rat *r, const lc_rat *a)
{
    if (lc_int_is_zero(&a->num)) return LC_EDIVZERO;
    lc_rat t; lc_rat_init(&t);
    int e = lc_int_copy(&t.num, &a->den);
    if (!e) e = lc_int_copy(&t.den, &a->num);
    if (!e) e = normalise(&t);
    if (!e) { lc_int_swap(&r->num, &t.num); lc_int_swap(&r->den, &t.den); }
    lc_rat_clear(&t);
    return e;
}

int lc_rat_div(lc_rat *r, const lc_rat *a, const lc_rat *b)
{
    lc_rat ib; lc_rat_init(&ib);
    int e = lc_rat_inv(&ib, b);
    if (!e) e = lc_rat_mul(r, a, &ib);
    lc_rat_clear(&ib);
    return e;
}

int lc_rat_pow_si(lc_rat *r, const lc_rat *a, long ex)
{
    lc_rat t; lc_rat_init(&t);
    unsigned long m = ex < 0 ? (unsigned long)(-(ex + 1)) + 1 : (unsigned long)ex;
    int e = lc_int_pow_ui(&t.num, &a->num, m);
    if (!e) e = lc_int_pow_ui(&t.den, &a->den, m);
    if (!e && ex < 0) {
        if (lc_int_is_zero(&t.num)) e = LC_EDIVZERO;
        else { lc_int_swap(&t.num, &t.den); e = normalise(&t); }
    }
    if (!e) { lc_int_swap(&r->num, &t.num); lc_int_swap(&r->den, &t.den); }
    lc_rat_clear(&t);
    return e;
}

int lc_rat_cmp(const lc_rat *a, const lc_rat *b)
{
    lc_int x, y; lc_int_init(&x); lc_int_init(&y);
    lc_int_mul(&x, &a->num, &b->den);
    lc_int_mul(&y, &b->num, &a->den);
    int c = lc_int_cmp(&x, &y);
    lc_int_clear(&x); lc_int_clear(&y);
    return c;
}

int lc_rat_sign(const lc_rat *a) { return lc_int_sign(&a->num); }
int lc_rat_is_int(const lc_rat *a) { return lc_int_is_one(&a->den); }

int lc_rat_round(lc_int *out, const lc_rat *q, lc_round mode)
{
    lc_int fl, rem, twice; lc_int_init(&fl); lc_int_init(&rem); lc_int_init(&twice);
    int e = lc_int_fdivmod(&fl, &rem, &q->num, &q->den);   /* q = fl + rem/den, 0 <= rem < den */
    if (e) goto done;
    if (lc_int_is_zero(&rem)) { e = lc_int_copy(out, &fl); goto done; }
    int up = 0;
    switch (mode) {
    case LC_ROUND_FLOOR: up = 0; break;
    case LC_ROUND_CEIL:  up = 1; break;
    case LC_ROUND_TRUNC: up = lc_int_sign(&q->num) < 0; break;
    case LC_ROUND_HALF_EVEN:
    case LC_ROUND_HALF_UP: {
        e = lc_int_shl(&twice, &rem, 1);
        if (e) goto done;
        int c = lc_int_cmp(&twice, &q->den);
        if (c > 0) up = 1;
        else if (c < 0) up = 0;
        else if (mode == LC_ROUND_HALF_EVEN) up = !lc_int_is_even(&fl);
        else up = lc_int_sign(&q->num) > 0;                /* away from zero */
        break;
    }
    }
    if (up) e = lc_int_add_i64(&fl, &fl, 1);
    if (!e) e = lc_int_copy(out, &fl);
done:
    lc_int_clear(&fl); lc_int_clear(&rem); lc_int_clear(&twice);
    return e;
}

int lc_rat_round_places(lc_int *out, const lc_rat *q, unsigned base, unsigned k, lc_round mode)
{
    lc_rat t; lc_rat_init(&t);
    lc_int p; lc_int_init(&p);
    int e = lc_int_ui_pow_ui(&p, base, k);
    if (!e) e = lc_int_mul(&t.num, &q->num, &p);
    if (!e) e = lc_int_copy(&t.den, &q->den);
    if (!e) e = lc_rat_round(out, &t, mode);
    lc_rat_clear(&t); lc_int_clear(&p);
    return e;
}

/* ------------------------------------------------------------------ */
/* base structure                                                      */
/* ------------------------------------------------------------------ */

int lc_rat_is_finite_in_base(const lc_rat *q, unsigned base)
{
    if (base < 2) return 0;                 /* bases 0 and 1 have no positional expansion */
    lc_int d, g, b; lc_int_init(&d); lc_int_init(&g); lc_int_init(&b);
    lc_int_copy(&d, &q->den);
    lc_int_set_u64(&b, base);
    int e = 0;
    for (;;) {
        e = lc_int_gcd(&g, &d, &b);
        if (e || lc_int_is_one(&g)) break;
        e = lc_int_divexact(&d, &d, &g);
        if (e) break;
    }
    int res = e ? 0 : lc_int_is_one(&d);
    lc_int_clear(&d); lc_int_clear(&g); lc_int_clear(&b);
    return res;
}

int lc_rat_expansion_shape(const lc_rat *q, unsigned base, size_t max_period,
                           size_t *pre, size_t *period)
{
    if (base < 2) return LC_EINVAL;
    lc_int d1, d2, g, b, r;
    lc_int_init(&d1); lc_int_init(&d2); lc_int_init(&g); lc_int_init(&b); lc_int_init(&r);
    int e = lc_int_copy(&d2, &q->den);
    if (!e) e = lc_int_set_u64(&b, base);
    /* d2 = den with every prime of the base removed */
    while (!e) {
        e = lc_int_gcd(&g, &d2, &b);
        if (e || lc_int_is_one(&g)) break;
        e = lc_int_divexact(&d2, &d2, &g);
    }
    /* preperiod: steps to exhaust d1 = den / d2 */
    size_t k = 0;
    if (!e) e = lc_int_divexact(&d1, &q->den, &d2);
    while (!e && !lc_int_is_one(&d1)) {
        e = lc_int_gcd(&g, &d1, &b);
        if (!e) e = lc_int_divexact(&d1, &d1, &g);
        k++;
    }
    size_t t = 0;
    if (!e && !lc_int_is_one(&d2)) {
        /* period = multiplicative order of base mod d2 */
        e = lc_int_edivmod(NULL, &r, &b, &d2);
        t = 1;
        while (!e && !lc_int_is_one(&r)) {
            if (t >= max_period) { e = LC_ERANGE; break; }
            e = lc_int_mul(&r, &r, &b);
            if (!e) e = lc_int_edivmod(NULL, &r, &r, &d2);
            t++;
        }
    }
    if (!e) { *pre = k; *period = t; }
    lc_int_clear(&d1); lc_int_clear(&d2); lc_int_clear(&g); lc_int_clear(&b); lc_int_clear(&r);
    return e;
}

/* ------------------------------------------------------------------ */
/* output                                                              */
/* ------------------------------------------------------------------ */

char *lc_rat_get_str(const lc_rat *q)
{
    char *n = lc_int_get_str(&q->num, 10);
    if (!n) return NULL;
    if (lc_int_is_one(&q->den)) return n;
    char *d = lc_int_get_str(&q->den, 10);
    if (!d) { free(n); return NULL; }
    char *s = malloc(strlen(n) + strlen(d) + 2);
    if (s) sprintf(s, "%s/%s", n, d);
    free(n); free(d);
    return s;
}

char *lc_rat_get_decimal(const lc_rat *q, unsigned digits, lc_round mode)
{
    lc_int N; lc_int_init(&N);
    if (lc_rat_round_places(&N, q, 10, digits, mode)) { lc_int_clear(&N); return NULL; }
    int neg = lc_int_sign(&N) < 0;
    lc_int_abs(&N, &N);
    char *s = lc_int_get_str(&N, 10);
    lc_int_clear(&N);
    if (!s) return NULL;
    size_t L = strlen(s);
    lc_strbuf sb; lc_sb_init(&sb);
    if (neg) lc_sb_putc(&sb, '-');
    if (L <= digits) {
        lc_sb_puts(&sb, "0");
        if (digits) { lc_sb_putc(&sb, '.'); for (size_t i = L; i < digits; i++) lc_sb_putc(&sb, '0'); lc_sb_puts(&sb, s); }
    } else {
        for (size_t i = 0; i < L - digits; i++) lc_sb_putc(&sb, s[i]);
        if (digits) { lc_sb_putc(&sb, '.'); lc_sb_puts(&sb, s + L - digits); }
    }
    free(s);
    return lc_sb_finish(&sb);
}

/* append the base-b digits of n >= 0, comma separated (b > 36) or packed (b <= 36) */
static int put_whole(lc_strbuf *sb, const lc_int *n, unsigned base)
{
    if (base <= 36) {
        char *s = lc_int_get_str(n, (int)base);
        if (!s) return LC_ENOMEM;
        lc_sb_puts(sb, s); free(s);
        return LC_OK;
    }
    /* collect digits least significant first */
    size_t cap = 16, cnt = 0;
    uint32_t *ds = malloc(cap * sizeof *ds);
    if (!ds) return LC_ENOMEM;
    lc_int t; lc_int_init(&t); lc_int_copy(&t, n);
    while (!lc_int_is_zero(&t)) {
        uint32_t r;
        lc_int_divmod_u32(&t, &r, &t, base);
        if (cnt == cap) { cap *= 2; uint32_t *p = realloc(ds, cap * sizeof *ds); if (!p) { free(ds); lc_int_clear(&t); return LC_ENOMEM; } ds = p; }
        ds[cnt++] = r;
    }
    lc_int_clear(&t);
    if (cnt == 0) lc_sb_putc(sb, '0');
    for (size_t i = cnt; i-- > 0;) {
        lc_sb_printf(sb, "%u", ds[i]);
        if (i) lc_sb_putc(sb, ',');
    }
    free(ds);
    return LC_OK;
}

static void put_place(lc_strbuf *sb, uint32_t d, unsigned base, int first)
{
    static const char digs[] = "0123456789abcdefghijklmnopqrstuvwxyz";
    if (base <= 36) { lc_sb_putc(sb, digs[d]); return; }
    if (!first) lc_sb_putc(sb, ',');
    unsigned w = 1; for (unsigned b = base - 1; b >= 10; b /= 10) w++;
    lc_sb_printf(sb, "%0*u", (int)w, d);
}

char *lc_rat_get_sexa(const lc_rat *q, unsigned places, lc_round mode)
{
    lc_int N, P, W, F; lc_int_init(&N); lc_int_init(&P); lc_int_init(&W); lc_int_init(&F);
    char *res = NULL;
    if (lc_rat_round_places(&N, q, 60, places, mode)) goto done;
    int neg = lc_int_sign(&N) < 0;
    lc_int_abs(&N, &N);
    lc_int_ui_pow_ui(&P, 60, places);
    lc_int_tdivmod(&W, &F, &N, &P);
    lc_strbuf sb; lc_sb_init(&sb);
    if (neg) lc_sb_putc(&sb, '-');
    put_whole(&sb, &W, 60);
    if (places) {
        lc_sb_putc(&sb, ';');
        uint32_t *ds = malloc(places * sizeof *ds);
        if (!ds) { lc_sb_free(&sb); goto done; }
        for (unsigned i = places; i-- > 0;) { uint32_t r; lc_int_divmod_u32(&F, &r, &F, 60); ds[i] = r; }
        for (unsigned i = 0; i < places; i++) put_place(&sb, ds[i], 60, i == 0);
        free(ds);
    }
    res = lc_sb_finish(&sb);
done:
    lc_int_clear(&N); lc_int_clear(&P); lc_int_clear(&W); lc_int_clear(&F);
    return res;
}

char *lc_rat_get_expansion(const lc_rat *q, unsigned base, size_t max_digits)
{
    if (base < 2 || base > 3600) return NULL;
    size_t pre = 0, per = 0;
    int truncated = 0;
    int e = lc_rat_expansion_shape(q, base, max_digits + 1, &pre, &per);
    if (e == LC_ERANGE) { truncated = 1; per = 0; }
    else if (e) return NULL;
    if (pre + per > max_digits) { truncated = 1; }
    lc_int W, R, B; lc_int_init(&W); lc_int_init(&R); lc_int_init(&B);
    lc_int absn; lc_int_init(&absn);
    lc_int_abs(&absn, &q->num);
    lc_int_tdivmod(&W, &R, &absn, &q->den);
    lc_int_set_u64(&B, base);
    lc_strbuf sb; lc_sb_init(&sb);
    if (lc_int_sign(&q->num) < 0) lc_sb_putc(&sb, '-');
    put_whole(&sb, &W, base);
    size_t total = truncated ? max_digits : pre + per;
    if (total > 0 || per > 0) lc_sb_putc(&sb, base <= 36 ? '.' : ';');
    int first = 1;
    for (size_t i = 0; i < total; i++) {
        if (!truncated && i == pre && per) {
            if (pre > 0 && base > 36) lc_sb_putc(&sb, ',');
            lc_sb_putc(&sb, '(');
            first = 1;
        }
        lc_int_mul(&R, &R, &B);
        lc_int dq; lc_int_init(&dq);
        lc_int_tdivmod(&dq, &R, &R, &q->den);
        uint64_t dv = 0; lc_int_get_u64(&dq, &dv);
        lc_int_clear(&dq);
        put_place(&sb, (uint32_t)dv, base, first);
        first = 0;
    }
    if (!truncated && per) lc_sb_putc(&sb, ')');
    if (truncated) lc_sb_puts(&sb, "...");
    lc_int_clear(&W); lc_int_clear(&R); lc_int_clear(&B); lc_int_clear(&absn);
    return lc_sb_finish(&sb);
}

/* ------------------------------------------------------------------ */
/* input                                                               */
/* ------------------------------------------------------------------ */

/* q = W + P/B^k + R/(B^k (B^t - 1)); digits given as arrays */
static int assemble(lc_rat *out, int neg, const lc_int *W, const uint32_t *pd, size_t k,
                    const uint32_t *rd, size_t t, unsigned base)
{
    lc_rat acc, term; lc_rat_init(&acc); lc_rat_init(&term);
    lc_int P, Bk, x; lc_int_init(&P); lc_int_init(&Bk); lc_int_init(&x);
    int e = lc_rat_set_int(&acc, W);
    for (size_t i = 0; !e && i < k; i++) { e = lc_int_mul_i64(&P, &P, base); if (!e) e = lc_int_add_i64(&P, &P, pd[i]); }
    if (!e) e = lc_int_ui_pow_ui(&Bk, base, (unsigned long)k);
    if (!e) e = lc_rat_set_frac(&term, &P, &Bk);
    if (!e) e = lc_rat_add(&acc, &acc, &term);
    if (!e && t > 0) {
        lc_int_set_i64(&P, 0);
        for (size_t i = 0; !e && i < t; i++) { e = lc_int_mul_i64(&P, &P, base); if (!e) e = lc_int_add_i64(&P, &P, rd[i]); }
        if (!e) e = lc_int_ui_pow_ui(&x, base, (unsigned long)t);
        if (!e) e = lc_int_add_i64(&x, &x, -1);
        if (!e) e = lc_int_mul(&x, &x, &Bk);
        if (!e) e = lc_rat_set_frac(&term, &P, &x);
        if (!e) e = lc_rat_add(&acc, &acc, &term);
    }
    if (!e && neg) e = lc_rat_neg(&acc, &acc);
    if (!e) e = lc_rat_copy(out, &acc);
    lc_rat_clear(&acc); lc_rat_clear(&term);
    lc_int_clear(&P); lc_int_clear(&Bk); lc_int_clear(&x);
    return e;
}

typedef struct { uint32_t *v; size_t n, cap; } u32vec;
static int vpush(u32vec *a, uint32_t x)
{
    if (a->n == a->cap) {
        size_t nc = a->cap ? 2 * a->cap : 16;
        uint32_t *p = realloc(a->v, nc * sizeof *p);
        if (!p) return LC_ENOMEM;
        a->v = p; a->cap = nc;
    }
    a->v[a->n++] = x;
    return LC_OK;
}

/* parse "d,d,d" (decimal numbers < 60) from s up to end; stops at ')' too */
static int parse_sexa_digits(const char **ps, const char *end, u32vec *out)
{
    const char *s = *ps;
    int expect = 1;
    while (s < end && *s != ')' && *s != '(') {
        if (*s == ',') { if (expect) return LC_EPARSE; expect = 1; s++; continue; }
        if (!isdigit((unsigned char)*s)) return LC_EPARSE;
        if (!expect) return LC_EPARSE;
        unsigned long v = 0;
        while (s < end && isdigit((unsigned char)*s)) { v = v * 10 + (unsigned long)(*s - '0'); if (v >= 60) return LC_EPARSE; s++; }
        int e = vpush(out, (uint32_t)v);
        if (e) return e;
        expect = 0;
    }
    if (expect && out->n && (s >= end || *s != '(')) return LC_EPARSE;   /* trailing comma */
    *ps = s;
    return LC_OK;
}

static int parse_sexa(lc_rat *r, const char *s, const char *end, int neg)
{
    const char *semi = memchr(s, ';', (size_t)(end - s));
    u32vec whole = {0}, pre = {0}, rep = {0};
    int e = LC_OK;
    const char *p = s;
    if (!semi) semi = end;                       /* "1,0,1": a base-60 integer */
    e = parse_sexa_digits(&p, semi, &whole);
    if (!e && p != semi) e = LC_EPARSE;
    p = semi < end ? semi + 1 : end;
    if (!e) e = parse_sexa_digits(&p, end, &pre);
    if (!e && p < end && *p == '(') {
        if (pre.n && p[-1] != ',') e = LC_EPARSE;
        p++;
        if (!e) e = parse_sexa_digits(&p, end, &rep);
        if (!e && (p >= end || *p != ')' || rep.n == 0)) e = LC_EPARSE;
        else if (!e) p++;
    }
    if (!e && p != end) e = LC_EPARSE;
    if (!e && whole.n == 0 && pre.n == 0 && rep.n == 0) e = LC_EPARSE;
    if (!e) {
        lc_int W; lc_int_init(&W);
        for (size_t i = 0; !e && i < whole.n; i++) { e = lc_int_mul_i64(&W, &W, 60); if (!e) e = lc_int_add_i64(&W, &W, whole.v[i]); }
        if (!e) e = assemble(r, neg, &W, pre.v, pre.n, rep.v, rep.n, 60);
        lc_int_clear(&W);
    }
    free(whole.v); free(pre.v); free(rep.v);
    return e;
}

static int parse_decimal(lc_rat *r, const char *s, const char *end, int neg)
{
    u32vec pre = {0}, rep = {0};
    lc_int W; lc_int_init(&W);
    int e = LC_OK, any = 0;
    const char *p = s;
    while (p < end && (isdigit((unsigned char)*p) || *p == '_')) {
        if (*p != '_') { e = lc_int_mul_i64(&W, &W, 10); if (!e) e = lc_int_add_i64(&W, &W, *p - '0'); any = 1; }
        if (e) break;
        p++;
    }
    if (!e && p < end && *p == '.') {
        p++;
        while (!e && p < end && isdigit((unsigned char)*p)) { e = vpush(&pre, (uint32_t)(*p - '0')); any = 1; p++; }
        if (!e && p < end && *p == '(') {
            p++;
            while (!e && p < end && isdigit((unsigned char)*p)) { e = vpush(&rep, (uint32_t)(*p - '0')); p++; }
            if (!e && (p >= end || *p != ')' || rep.n == 0)) e = LC_EPARSE;
            else if (!e) { p++; any = 1; }
        }
    }
    long ex = 0;
    if (!e && p < end && (*p == 'e' || *p == 'E')) {
        p++;
        int eneg = 0;
        if (p < end && (*p == '+' || *p == '-')) { eneg = *p == '-'; p++; }
        if (p >= end || !isdigit((unsigned char)*p)) e = LC_EPARSE;
        while (!e && p < end && isdigit((unsigned char)*p)) {
            ex = ex * 10 + (*p - '0');
            if (ex > 100000000L) e = LC_ERANGE;
            p++;
        }
        if (eneg) ex = -ex;
    }
    if (!e && (p != end || !any)) e = LC_EPARSE;
    if (!e) e = assemble(r, neg, &W, pre.v, pre.n, rep.v, rep.n, 10);
    if (!e && ex) {
        lc_rat t; lc_rat_init(&t);
        e = lc_rat_set_i64(&t, 10, 1);
        if (!e) e = lc_rat_pow_si(&t, &t, ex);
        if (!e) e = lc_rat_mul(r, r, &t);
        lc_rat_clear(&t);
    }
    free(pre.v); free(rep.v); lc_int_clear(&W);
    return e;
}

int lc_rat_set_str(lc_rat *r, const char *str)
{
    if (!str) return LC_EINVAL;
    const char *s = str, *end = str + strlen(str);
    while (s < end && isspace((unsigned char)*s)) s++;
    while (end > s && isspace((unsigned char)end[-1])) end--;
    int neg = 0;
    if (s < end && (*s == '+' || *s == '-')) { neg = *s == '-'; s++; }
    if (s >= end) return LC_EPARSE;
    lc_rat t; lc_rat_init(&t);
    int e;
    if (memchr(s, ';', (size_t)(end - s)) || memchr(s, ',', (size_t)(end - s))) e = parse_sexa(&t, s, end, neg);
    else if (memchr(s, '/', (size_t)(end - s))) {
        const char *slash = memchr(s, '/', (size_t)(end - s));
        size_t ln = (size_t)(slash - s), ld = (size_t)(end - slash - 1);
        char *a = malloc(ln + 1), *b = malloc(ld + 1);
        if (!a || !b) { free(a); free(b); lc_rat_clear(&t); return LC_ENOMEM; }
        memcpy(a, s, ln); a[ln] = 0; memcpy(b, slash + 1, ld); b[ld] = 0;
        lc_int n, d; lc_int_init(&n); lc_int_init(&d);
        e = lc_int_set_str(&n, a, 10);
        if (!e) e = lc_int_set_str(&d, b, 10);
        if (!e && neg) e = lc_int_neg(&n, &n);
        if (!e) e = lc_rat_set_frac(&t, &n, &d);
        lc_int_clear(&n); lc_int_clear(&d); free(a); free(b);
    } else e = parse_decimal(&t, s, end, neg);
    if (!e) e = lc_rat_copy(r, &t);
    lc_rat_clear(&t);
    return e;
}
