/*
 * latcalc -- arbitrary-precision integers.
 *
 * Magnitudes are little-endian arrays of 32-bit limbs; 64-bit intermediates carry.
 * Multiplication switches from schoolbook to Karatsuba above KARATSUBA_THRESHOLD limbs.
 * Division is Knuth's Algorithm D (TAOCP vol. 2, 4.3.1).
 */
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include "latcalc/bigint.h"

#define KARATSUBA_THRESHOLD 32

typedef uint32_t limb;
typedef uint64_t dlimb;

/* ------------------------------------------------------------------ */
/* storage                                                             */
/* ------------------------------------------------------------------ */

void lc_int_init(lc_int *a) { a->sign = 0; a->len = 0; a->cap = 0; a->d = NULL; }

void lc_int_clear(lc_int *a) { free(a->d); lc_int_init(a); }

static int reserve(lc_int *a, size_t n)
{
    if (n <= a->cap) return LC_OK;
    size_t nc = a->cap ? a->cap : 4;
    while (nc < n) nc *= 2;
    limb *p = realloc(a->d, nc * sizeof(limb));
    if (!p) return LC_ENOMEM;
    a->d = p; a->cap = nc;
    return LC_OK;
}

static void trim(lc_int *a)
{
    while (a->len > 0 && a->d[a->len - 1] == 0) a->len--;
    if (a->len == 0) a->sign = 0;
}

static size_t mag_len(const limb *d, size_t n) { while (n > 0 && d[n - 1] == 0) n--; return n; }

int lc_int_copy(lc_int *r, const lc_int *a)
{
    if (r == a) return LC_OK;
    int e = reserve(r, a->len);
    if (e) return e;
    if (a->len) memcpy(r->d, a->d, a->len * sizeof(limb));
    r->len = a->len; r->sign = a->sign;
    return LC_OK;
}

void lc_int_swap(lc_int *a, lc_int *b) { lc_int t = *a; *a = *b; *b = t; }

/* ------------------------------------------------------------------ */
/* C integer conversion                                                */
/* ------------------------------------------------------------------ */

int lc_int_set_u64(lc_int *r, uint64_t v)
{
    int e = reserve(r, 2);
    if (e) return e;
    r->d[0] = (limb)v; r->d[1] = (limb)(v >> 32);
    r->len = 2; r->sign = 1; trim(r);
    return LC_OK;
}

int lc_int_set_i64(lc_int *r, int64_t v)
{
    uint64_t m = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    int e = lc_int_set_u64(r, m);
    if (e) return e;
    if (v < 0) r->sign = -1;
    return LC_OK;
}

int lc_int_get_u64(const lc_int *a, uint64_t *out)
{
    if (a->sign < 0 || a->len > 2) return LC_ERANGE;
    uint64_t v = 0;
    if (a->len > 0) v = a->d[0];
    if (a->len > 1) v |= (uint64_t)a->d[1] << 32;
    *out = v;
    return LC_OK;
}

int lc_int_get_i64(const lc_int *a, int64_t *out)
{
    if (a->len > 2) return LC_ERANGE;
    uint64_t v = 0;
    if (a->len > 0) v = a->d[0];
    if (a->len > 1) v |= (uint64_t)a->d[1] << 32;
    if (a->sign >= 0) {
        if (v > (uint64_t)INT64_MAX) return LC_ERANGE;
        *out = (int64_t)v;
    } else {
        if (v > (uint64_t)INT64_MAX + 1) return LC_ERANGE;
        *out = v == (uint64_t)INT64_MAX + 1 ? INT64_MIN : -(int64_t)v;
    }
    return LC_OK;
}

int lc_int_fits_i64(const lc_int *a) { int64_t t; return lc_int_get_i64(a, &t) == LC_OK; }

int lc_int_set_double(lc_int *r, double x)
{
    if (isnan(x) || isinf(x)) return LC_ERANGE;
    double ip;
    if (modf(x, &ip) != 0.0) return LC_EINEXACT;
    int neg = x < 0;
    if (neg) x = -x;
    if (x == 0.0) { r->len = 0; r->sign = 0; return LC_OK; }
    int ex;
    double f = frexp(x, &ex);                 /* x = f * 2^ex, 0.5 <= f < 1 */
    uint64_t m = (uint64_t)ldexp(f, 53);      /* exact: 53-bit mantissa */
    int shift = ex - 53;
    int e = lc_int_set_u64(r, m);
    if (e) return e;
    if (shift > 0) e = lc_int_shl(r, r, (size_t)shift);
    else if (shift < 0) e = lc_int_shr(r, r, (size_t)(-shift)); /* exact since x integral */
    if (e) return e;
    if (neg && r->len) r->sign = -1;
    return LC_OK;
}

double lc_int_get_double(const lc_int *a)
{
    if (a->len == 0) return 0.0;
    size_t bl = lc_int_bitlen(a);
    lc_int t; lc_int_init(&t);
    double res;
    if (bl <= 64) {
        uint64_t v = a->d[0] | (a->len > 1 ? (uint64_t)a->d[1] << 32 : 0);
        res = (double)v;
    } else {
        lc_int_abs(&t, a);
        lc_int_shr(&t, &t, bl - 64);
        uint64_t v = t.d[0] | ((uint64_t)t.d[1] << 32);
        res = ldexp((double)v, (int)(bl - 64));
    }
    lc_int_clear(&t);
    return a->sign < 0 ? -res : res;
}

/* ------------------------------------------------------------------ */
/* queries                                                             */
/* ------------------------------------------------------------------ */

int lc_int_sign(const lc_int *a) { return a->sign; }
int lc_int_is_zero(const lc_int *a) { return a->len == 0; }
int lc_int_is_one(const lc_int *a) { return a->sign == 1 && a->len == 1 && a->d[0] == 1; }
int lc_int_is_even(const lc_int *a) { return a->len == 0 || (a->d[0] & 1) == 0; }

static int mag_cmp(const limb *a, size_t an, const limb *b, size_t bn)
{
    if (an != bn) return an < bn ? -1 : 1;
    for (size_t i = an; i-- > 0;)
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}

int lc_int_cmp_abs(const lc_int *a, const lc_int *b) { return mag_cmp(a->d, a->len, b->d, b->len); }

int lc_int_cmp(const lc_int *a, const lc_int *b)
{
    if (a->sign != b->sign) return a->sign < b->sign ? -1 : 1;
    int c = lc_int_cmp_abs(a, b);
    return a->sign >= 0 ? c : -c;
}

int lc_int_cmp_i64(const lc_int *a, int64_t v)
{
    lc_int t; lc_int_init(&t);
    if (lc_int_set_i64(&t, v)) { lc_int_clear(&t); return 0; }
    int c = lc_int_cmp(a, &t);
    lc_int_clear(&t);
    return c;
}

size_t lc_int_bitlen(const lc_int *a)
{
    if (a->len == 0) return 0;
    limb top = a->d[a->len - 1];
    size_t b = 0;
    while (top) { b++; top >>= 1; }
    return (a->len - 1) * 32 + b;
}

/* ------------------------------------------------------------------ */
/* magnitude kernels                                                   */
/* ------------------------------------------------------------------ */

/* r[0..max(an,bn)] = a + b; r must hold max(an,bn)+1 limbs. Returns length. */
static size_t mag_add(limb *r, const limb *a, size_t an, const limb *b, size_t bn)
{
    if (an < bn) { const limb *t = a; a = b; b = t; size_t tn = an; an = bn; bn = tn; }
    dlimb c = 0;
    size_t i = 0;
    for (; i < bn; i++) { c += (dlimb)a[i] + b[i]; r[i] = (limb)c; c >>= 32; }
    for (; i < an; i++) { c += a[i]; r[i] = (limb)c; c >>= 32; }
    r[an] = (limb)c;
    return mag_len(r, an + 1);
}

/* r = a - b with a >= b; r holds an limbs. Returns length. */
static size_t mag_sub(limb *r, const limb *a, size_t an, const limb *b, size_t bn)
{
    int64_t br = 0;
    size_t i = 0;
    for (; i < bn; i++) {
        int64_t t = (int64_t)a[i] - b[i] - br;
        br = t < 0; r[i] = (limb)(t + (br ? ((int64_t)1 << 32) : 0));
    }
    for (; i < an; i++) {
        int64_t t = (int64_t)a[i] - br;
        br = t < 0; r[i] = (limb)(t + (br ? ((int64_t)1 << 32) : 0));
    }
    return mag_len(r, an);
}

/* r[0..an+bn) = a * b (schoolbook). r must not overlap a or b. */
static void mag_mul_school(limb *r, const limb *a, size_t an, const limb *b, size_t bn)
{
    memset(r, 0, (an + bn) * sizeof(limb));
    for (size_t i = 0; i < an; i++) {
        dlimb c = 0, ai = a[i];
        if (ai == 0) continue;
        for (size_t j = 0; j < bn; j++) {
            c += ai * b[j] + r[i + j];
            r[i + j] = (limb)c; c >>= 32;
        }
        r[i + bn] = (limb)c;
    }
}

/* r += a (length an) starting at limb offset off; r has room up to rn limbs. */
static void mag_add_at(limb *r, size_t rn, const limb *a, size_t an, size_t off)
{
    dlimb c = 0;
    size_t i = 0;
    for (; i < an; i++) { c += (dlimb)r[off + i] + a[i]; r[off + i] = (limb)c; c >>= 32; }
    for (size_t k = off + an; c && k < rn; k++) { c += r[k]; r[k] = (limb)c; c >>= 32; }
}

/* r -= a at offset off (the result is known to stay nonnegative). */
static void mag_sub_at(limb *r, size_t rn, const limb *a, size_t an, size_t off)
{
    int64_t br = 0;
    size_t i = 0;
    for (; i < an; i++) {
        int64_t t = (int64_t)r[off + i] - a[i] - br;
        br = t < 0; r[off + i] = (limb)(t + (br ? ((int64_t)1 << 32) : 0));
    }
    for (size_t k = off + an; br && k < rn; k++) {
        int64_t t = (int64_t)r[k] - br;
        br = t < 0; r[k] = (limb)(t + (br ? ((int64_t)1 << 32) : 0));
    }
}

/* r[0..an+bn) = a * b by Karatsuba. Returns LC_OK or LC_ENOMEM. */
static int mag_mul_kara(limb *r, const limb *a, size_t an, const limb *b, size_t bn)
{
    if (an < bn) { const limb *t = a; a = b; b = t; size_t tn = an; an = bn; bn = tn; }
    if (bn < KARATSUBA_THRESHOLD) { mag_mul_school(r, a, an, b, bn); return LC_OK; }
    if (bn <= an / 2) {
        /* unbalanced: cut a into pieces of bn limbs */
        memset(r, 0, (an + bn) * sizeof(limb));
        limb *tmp = malloc(2 * bn * sizeof(limb));
        if (!tmp) return LC_ENOMEM;
        for (size_t i = 0; i < an; i += bn) {
            size_t pn = an - i < bn ? an - i : bn;
            int e = mag_mul_kara(tmp, a + i, pn, b, bn);
            if (e) { free(tmp); return e; }
            mag_add_at(r, an + bn, tmp, pn + bn, i);
        }
        free(tmp);
        return LC_OK;
    }
    size_t m = an / 2;                       /* bn > m */
    const limb *a0 = a, *a1 = a + m, *b0 = b, *b1 = b + m;
    size_t a0n = mag_len(a0, m), a1n = an - m, b0n = mag_len(b0, m), b1n = bn - m;
    size_t sn = (a1n > m ? a1n : m) + 1, tn = (b1n > m ? b1n : m) + 1;
    limb *s = calloc(sn, sizeof(limb)), *t = calloc(tn, sizeof(limb));
    limb *z1 = calloc(sn + tn, sizeof(limb));
    if (!s || !t || !z1) { free(s); free(t); free(z1); return LC_ENOMEM; }
    size_t sl = mag_add(s, a0, a0n, a1, a1n);
    size_t tl = mag_add(t, b0, b0n, b1, b1n);
    memset(r, 0, (an + bn) * sizeof(limb));
    int e = LC_OK;
    /* z0 = a0*b0 into r[0..), z2 = a1*b1 into r[2m..) */
    if (a0n && b0n) e = mag_mul_kara(r, a0, a0n, b0, b0n);
    if (!e) e = mag_mul_kara(r + 2 * m, a1, a1n, b1, b1n);
    if (!e && sl && tl) e = mag_mul_kara(z1, s, sl, t, tl);
    if (e) { free(s); free(t); free(z1); return e; }
    size_t z1n = mag_len(z1, sl + tl);
    /* z1 -= z0 + z2 */
    size_t z0n = mag_len(r, a0n + b0n);
    size_t z2n = mag_len(r + 2 * m, a1n + b1n);
    mag_sub_at(z1, z1n, r, z0n, 0);
    mag_sub_at(z1, z1n, r + 2 * m, z2n, 0);
    z1n = mag_len(z1, z1n);
    mag_add_at(r, an + bn, z1, z1n, m);
    free(s); free(t); free(z1);
    return LC_OK;
}

/* ------------------------------------------------------------------ */
/* signed arithmetic                                                   */
/* ------------------------------------------------------------------ */

int lc_int_neg(lc_int *r, const lc_int *a)
{
    int e = lc_int_copy(r, a);
    if (e) return e;
    r->sign = -r->sign;
    return LC_OK;
}

int lc_int_abs(lc_int *r, const lc_int *a)
{
    int e = lc_int_copy(r, a);
    if (e) return e;
    if (r->sign < 0) r->sign = 1;
    return LC_OK;
}

/* r = a + s*b where s = +1 or -1 */
static int addsub(lc_int *r, const lc_int *a, const lc_int *b, int s)
{
    int bs = b->sign * s;
    if (b->len == 0) return lc_int_copy(r, a);
    if (a->len == 0) { int e = lc_int_copy(r, b); if (!e) r->sign = bs; return e; }
    lc_int t; lc_int_init(&t);
    size_t n = (a->len > b->len ? a->len : b->len) + 1;
    int e = reserve(&t, n);
    if (e) return e;
    if (a->sign == bs) {
        t.len = mag_add(t.d, a->d, a->len, b->d, b->len);
        t.sign = a->sign;
    } else {
        int c = lc_int_cmp_abs(a, b);
        if (c == 0) { t.len = 0; t.sign = 0; }
        else if (c > 0) { t.len = mag_sub(t.d, a->d, a->len, b->d, b->len); t.sign = a->sign; }
        else { t.len = mag_sub(t.d, b->d, b->len, a->d, a->len); t.sign = bs; }
    }
    trim(&t);
    lc_int_swap(r, &t);
    lc_int_clear(&t);
    return LC_OK;
}

int lc_int_add(lc_int *r, const lc_int *a, const lc_int *b) { return addsub(r, a, b, 1); }
int lc_int_sub(lc_int *r, const lc_int *a, const lc_int *b) { return addsub(r, a, b, -1); }

static int mul_impl(lc_int *r, const lc_int *a, const lc_int *b, int school)
{
    if (a->len == 0 || b->len == 0) { r->len = 0; r->sign = 0; return LC_OK; }
    lc_int t; lc_int_init(&t);
    int e = reserve(&t, a->len + b->len);
    if (e) return e;
    if (school) mag_mul_school(t.d, a->d, a->len, b->d, b->len);
    else e = mag_mul_kara(t.d, a->d, a->len, b->d, b->len);
    if (e) { lc_int_clear(&t); return e; }
    t.len = a->len + b->len;
    t.sign = a->sign * b->sign;
    trim(&t);
    lc_int_swap(r, &t);
    lc_int_clear(&t);
    return LC_OK;
}

int lc_int_mul(lc_int *r, const lc_int *a, const lc_int *b) { return mul_impl(r, a, b, 0); }
int lc_int_mul_schoolbook(lc_int *r, const lc_int *a, const lc_int *b) { return mul_impl(r, a, b, 1); }

int lc_int_add_i64(lc_int *r, const lc_int *a, int64_t v)
{
    lc_int t; lc_int_init(&t);
    int e = lc_int_set_i64(&t, v);
    if (!e) e = lc_int_add(r, a, &t);
    lc_int_clear(&t);
    return e;
}

int lc_int_mul_i64(lc_int *r, const lc_int *a, int64_t v)
{
    lc_int t; lc_int_init(&t);
    int e = lc_int_set_i64(&t, v);
    if (!e) e = lc_int_mul(r, a, &t);
    lc_int_clear(&t);
    return e;
}

int lc_int_shl(lc_int *r, const lc_int *a, size_t bits)
{
    if (a->len == 0) { r->len = 0; r->sign = 0; return LC_OK; }
    size_t w = bits / 32, s = bits % 32;
    lc_int t; lc_int_init(&t);
    int e = reserve(&t, a->len + w + 1);
    if (e) return e;
    memset(t.d, 0, (a->len + w + 1) * sizeof(limb));
    for (size_t i = 0; i < a->len; i++) {
        dlimb v = (dlimb)a->d[i] << s;
        t.d[i + w] |= (limb)v;
        t.d[i + w + 1] |= (limb)(v >> 32);
    }
    t.len = a->len + w + 1; t.sign = a->sign;
    trim(&t);
    lc_int_swap(r, &t); lc_int_clear(&t);
    return LC_OK;
}

int lc_int_shr(lc_int *r, const lc_int *a, size_t bits)
{
    /* floor division by 2^bits */
    if (a->len == 0) { r->len = 0; r->sign = 0; return LC_OK; }
    size_t w = bits / 32, s = bits % 32;
    int lost = 0;
    if (a->sign < 0) {
        for (size_t i = 0; i < w && i < a->len; i++) if (a->d[i]) { lost = 1; break; }
        if (!lost && w < a->len && s && (a->d[w] & (((limb)1 << s) - 1))) lost = 1;
    }
    if (w >= a->len) {
        if (a->sign < 0) return lc_int_set_i64(r, -1);
        r->len = 0; r->sign = 0; return LC_OK;
    }
    lc_int t; lc_int_init(&t);
    size_t n = a->len - w;
    int e = reserve(&t, n);
    if (e) return e;
    for (size_t i = 0; i < n; i++) {
        dlimb lo = a->d[i + w];
        dlimb hi = (i + w + 1 < a->len) ? a->d[i + w + 1] : 0;
        t.d[i] = s ? (limb)((lo >> s) | (hi << (32 - s))) : (limb)lo;
    }
    t.len = n; t.sign = a->sign;
    trim(&t);
    if (lost) { e = lc_int_add_i64(&t, &t, -1); if (e) { lc_int_clear(&t); return e; } }
    lc_int_swap(r, &t); lc_int_clear(&t);
    return LC_OK;
}

int lc_int_pow_ui(lc_int *r, const lc_int *a, unsigned long ex)
{
    lc_int base, acc; lc_int_init(&base); lc_int_init(&acc);
    int e = lc_int_copy(&base, a);
    if (!e) e = lc_int_set_i64(&acc, 1);
    while (!e && ex) {
        if (ex & 1) e = lc_int_mul(&acc, &acc, &base);
        ex >>= 1;
        if (!e && ex) e = lc_int_mul(&base, &base, &base);
    }
    if (!e) lc_int_swap(r, &acc);
    lc_int_clear(&base); lc_int_clear(&acc);
    return e;
}

int lc_int_ui_pow_ui(lc_int *r, unsigned long b, unsigned long ex)
{
    lc_int t; lc_int_init(&t);
    int e = lc_int_set_u64(&t, b);
    if (!e) e = lc_int_pow_ui(r, &t, ex);
    lc_int_clear(&t);
    return e;
}

/* ------------------------------------------------------------------ */
/* division                                                            */
/* ------------------------------------------------------------------ */

int lc_int_divmod_u32(lc_int *q, uint32_t *rem, const lc_int *a, uint32_t b)
{
    if (b == 0) return LC_EDIVZERO;
    lc_int t; lc_int_init(&t);
    int e = reserve(&t, a->len ? a->len : 1);
    if (e) return e;
    dlimb r = 0;
    for (size_t i = a->len; i-- > 0;) {
        r = (r << 32) | a->d[i];
        t.d[i] = (limb)(r / b);
        r %= b;
    }
    t.len = a->len; t.sign = a->sign;
    trim(&t);
    if (rem) *rem = (uint32_t)r;
    if (q) lc_int_swap(q, &t);
    lc_int_clear(&t);
    return LC_OK;
}

uint32_t lc_int_mod_u32(const lc_int *a, uint32_t m)
{
    if (m == 0) return 0;                   /* undefined input: avoid division by zero */
    dlimb r = 0;
    for (size_t i = a->len; i-- > 0;) r = ((r << 32) | a->d[i]) % m;
    if (a->sign < 0 && r) r = m - r;
    return (uint32_t)r;
}

static int clz32(limb x) { int n = 0; if (!x) return 32; while (!(x & 0x80000000u)) { x <<= 1; n++; } return n; }

/* Truncating division of magnitudes: q = |a| / |b|, r = |a| mod |b|. */
static int mag_divmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b)
{
    size_t n = b->len, m;
    if (mag_cmp(a->d, a->len, b->d, b->len) < 0) {
        if (r) { int e = lc_int_abs(r, a); if (e) return e; }
        if (q) { q->len = 0; q->sign = 0; }
        return LC_OK;
    }
    if (n == 1) {
        uint32_t rr; lc_int tq; lc_int_init(&tq);
        int e = lc_int_divmod_u32(&tq, &rr, a, b->d[0]);
        if (e) { lc_int_clear(&tq); return e; }
        if (tq.sign < 0) tq.sign = 1;
        if (q) lc_int_swap(q, &tq);
        lc_int_clear(&tq);
        if (r) return lc_int_set_u64(r, rr);
        return LC_OK;
    }
    m = a->len - n;
    int s = clz32(b->d[n - 1]);
    limb *u = calloc(a->len + 1, sizeof(limb));
    limb *v = calloc(n, sizeof(limb));
    limb *qd = calloc(m + 1, sizeof(limb));
    if (!u || !v || !qd) { free(u); free(v); free(qd); return LC_ENOMEM; }
    /* normalise */
    for (size_t i = 0; i < n; i++) {
        dlimb x = (dlimb)b->d[i] << s;
        v[i] |= (limb)x;
        if (i + 1 < n) v[i + 1] |= (limb)(x >> 32);
    }
    for (size_t i = 0; i < a->len; i++) {
        dlimb x = (dlimb)a->d[i] << s;
        u[i] |= (limb)x;
        u[i + 1] |= (limb)(x >> 32);
    }
    const dlimb B = (dlimb)1 << 32;
    for (size_t jj = m + 1; jj-- > 0;) {
        size_t j = jj;
        dlimb num = ((dlimb)u[j + n] << 32) | u[j + n - 1];
        dlimb qhat = num / v[n - 1];
        dlimb rhat = num % v[n - 1];
        while (qhat >= B || qhat * v[n - 2] > ((rhat << 32) | u[j + n - 2])) {
            qhat--; rhat += v[n - 1];
            if (rhat >= B) break;
        }
        /* multiply and subtract */
        int64_t borrow = 0;
        dlimb carry = 0;
        for (size_t i = 0; i < n; i++) {
            dlimb p = qhat * v[i] + carry;
            carry = p >> 32;
            int64_t t = (int64_t)u[i + j] - (int64_t)(limb)p - borrow;
            borrow = t < 0;
            u[i + j] = (limb)(t + (borrow ? (int64_t)B : 0));
        }
        int64_t t = (int64_t)u[j + n] - (int64_t)carry - borrow;
        borrow = t < 0;
        u[j + n] = (limb)(t + (borrow ? (int64_t)B : 0));
        if (borrow) {
            qhat--;
            dlimb c = 0;
            for (size_t i = 0; i < n; i++) {
                c += (dlimb)u[i + j] + v[i];
                u[i + j] = (limb)c; c >>= 32;
            }
            u[j + n] = (limb)((dlimb)u[j + n] + c);
        }
        qd[j] = (limb)qhat;
    }
    int e = LC_OK;
    if (q) {
        e = reserve(q, m + 1);
        if (!e) { memcpy(q->d, qd, (m + 1) * sizeof(limb)); q->len = m + 1; q->sign = 1; trim(q); }
    }
    if (!e && r) {
        e = reserve(r, n);
        if (!e) {
            for (size_t i = 0; i < n; i++) {
                dlimb lo = u[i] >> s;
                dlimb hi = s ? ((dlimb)u[i + 1] << (32 - s)) & 0xffffffffu : 0;
                r->d[i] = (limb)(lo | hi);
            }
            r->len = n; r->sign = 1; trim(r);
        }
    }
    free(u); free(v); free(qd);
    return e;
}

int lc_int_tdivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b)
{
    if (b->len == 0) return LC_EDIVZERO;
    lc_int tq, tr; lc_int_init(&tq); lc_int_init(&tr);
    int e = mag_divmod(&tq, &tr, a, b);
    if (!e) {
        if (tq.len) tq.sign = a->sign * b->sign;
        if (tr.len) tr.sign = a->sign;
        if (q) lc_int_swap(q, &tq);
        if (r) lc_int_swap(r, &tr);
    }
    lc_int_clear(&tq); lc_int_clear(&tr);
    return e;
}

int lc_int_fdivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b)
{
    lc_int tq, tr; lc_int_init(&tq); lc_int_init(&tr);
    int e = lc_int_tdivmod(&tq, &tr, a, b);
    if (!e && tr.len && tr.sign != b->sign) {
        e = lc_int_add_i64(&tq, &tq, -1);
        if (!e) e = lc_int_add(&tr, &tr, b);
    }
    if (!e) { if (q) lc_int_swap(q, &tq); if (r) lc_int_swap(r, &tr); }
    lc_int_clear(&tq); lc_int_clear(&tr);
    return e;
}

int lc_int_edivmod(lc_int *q, lc_int *r, const lc_int *a, const lc_int *b)
{
    lc_int tq, tr; lc_int_init(&tq); lc_int_init(&tr);
    int e = lc_int_tdivmod(&tq, &tr, a, b);
    if (!e && tr.sign < 0) {
        if (b->sign > 0) { e = lc_int_add_i64(&tq, &tq, -1); if (!e) e = lc_int_add(&tr, &tr, b); }
        else { e = lc_int_add_i64(&tq, &tq, 1); if (!e) e = lc_int_sub(&tr, &tr, b); }
    }
    if (!e) { if (q) lc_int_swap(q, &tq); if (r) lc_int_swap(r, &tr); }
    lc_int_clear(&tq); lc_int_clear(&tr);
    return e;
}

int lc_int_divexact(lc_int *q, const lc_int *a, const lc_int *b)
{
    lc_int tq, tr; lc_int_init(&tq); lc_int_init(&tr);
    int e = lc_int_tdivmod(&tq, &tr, a, b);
    if (!e && tr.len) e = LC_EINEXACT;
    if (!e) lc_int_swap(q, &tq);
    lc_int_clear(&tq); lc_int_clear(&tr);
    return e;
}

int lc_int_divisible(const lc_int *a, const lc_int *b)
{
    if (b->len == 0) return a->len == 0;
    lc_int tr; lc_int_init(&tr);
    int e = lc_int_tdivmod(NULL, &tr, a, b);
    int res = !e && tr.len == 0;
    lc_int_clear(&tr);
    return res;
}

/* ------------------------------------------------------------------ */
/* text                                                                */
/* ------------------------------------------------------------------ */

static int digit_value(int c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'z') return c - 'a' + 10;
    if (c >= 'A' && c <= 'Z') return c - 'A' + 10;
    return 99;
}

int lc_int_set_str(lc_int *r, const char *s, int base)
{
    if (!s || base < 2 || base > 36) return LC_EINVAL;
    while (isspace((unsigned char)*s)) s++;
    int neg = 0;
    if (*s == '+' || *s == '-') { neg = *s == '-'; s++; }
    lc_int t; lc_int_init(&t);
    int any = 0, e = LC_OK;
    /* accumulate chunks: value = value * base^k + chunk */
    uint32_t chunk = 0, mult = 1;
    for (; *s; s++) {
        if (*s == '_') continue;
        if (isspace((unsigned char)*s)) break;
        int dv = digit_value((unsigned char)*s);
        if (dv >= base) { lc_int_clear(&t); return LC_EPARSE; }
        any = 1;
        chunk = chunk * (uint32_t)base + (uint32_t)dv;
        mult *= (uint32_t)base;
        if (mult > 0xffffffffu / 36u) {
            e = lc_int_mul_i64(&t, &t, mult); if (!e) e = lc_int_add_i64(&t, &t, chunk);
            if (e) { lc_int_clear(&t); return e; }
            chunk = 0; mult = 1;
        }
    }
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s || !any) { lc_int_clear(&t); return LC_EPARSE; }
    if (mult > 1) {
        e = lc_int_mul_i64(&t, &t, mult); if (!e) e = lc_int_add_i64(&t, &t, chunk);
        if (e) { lc_int_clear(&t); return e; }
    }
    if (neg && t.len) t.sign = -1;
    lc_int_swap(r, &t); lc_int_clear(&t);
    return LC_OK;
}

char *lc_int_get_str(const lc_int *a, int base)
{
    if (base < 2 || base > 36) return NULL;
    static const char digs[] = "0123456789abcdefghijklmnopqrstuvwxyz";
    /* chunk base: largest power of base below 2^32 */
    uint32_t cb = (uint32_t)base; int cdig = 1;
    while ((uint64_t)cb * (uint32_t)base <= 0xffffffffu) { cb *= (uint32_t)base; cdig++; }
    size_t maxd = a->len * 32 + 2;  /* generous: >= digits in base 2 */
    char *buf = malloc(maxd + 2);
    if (!buf) return NULL;
    size_t pos = 0;
    lc_int t; lc_int_init(&t);
    if (lc_int_abs(&t, a)) { free(buf); return NULL; }
    if (t.len == 0) buf[pos++] = '0';
    while (t.len) {
        uint32_t rem;
        if (lc_int_divmod_u32(&t, &rem, &t, cb)) { free(buf); lc_int_clear(&t); return NULL; }
        for (int k = 0; k < cdig; k++) {
            if (t.len == 0 && rem == 0) break;
            buf[pos++] = digs[rem % (uint32_t)base];
            rem /= (uint32_t)base;
        }
    }
    lc_int_clear(&t);
    if (a->sign < 0) buf[pos++] = '-';
    buf[pos] = 0;
    for (size_t i = 0, j = pos - 1; i < j; i++, j--) { char c = buf[i]; buf[i] = buf[j]; buf[j] = c; }
    return buf;
}

/* ------------------------------------------------------------------ */
/* number theory                                                       */
/* ------------------------------------------------------------------ */

int lc_int_gcd(lc_int *r, const lc_int *a, const lc_int *b)
{
    lc_int x, y, t; lc_int_init(&x); lc_int_init(&y); lc_int_init(&t);
    int e = lc_int_abs(&x, a);
    if (!e) e = lc_int_abs(&y, b);
    while (!e && y.len) {
        e = lc_int_tdivmod(NULL, &t, &x, &y);
        if (!e) { lc_int_swap(&x, &y); lc_int_swap(&y, &t); }
    }
    if (!e) lc_int_swap(r, &x);
    lc_int_clear(&x); lc_int_clear(&y); lc_int_clear(&t);
    return e;
}

int lc_int_gcdext(lc_int *g, lc_int *x, lc_int *y, const lc_int *a, const lc_int *b)
{
    /* invariant: r0 = a*s0 + b*t0, r1 = a*s1 + b*t1 */
    lc_int r0, r1, s0, s1, t0, t1, q, tmp;
    lc_int *all[] = {&r0, &r1, &s0, &s1, &t0, &t1, &q, &tmp};
    for (int i = 0; i < 8; i++) lc_int_init(all[i]);
    int e = lc_int_copy(&r0, a);
    if (!e) e = lc_int_copy(&r1, b);
    if (!e) e = lc_int_set_i64(&s0, 1);
    if (!e) e = lc_int_set_i64(&t1, 1);
    while (!e && r1.len) {
        e = lc_int_tdivmod(&q, &tmp, &r0, &r1);
        if (e) break;
        lc_int_swap(&r0, &r1); lc_int_swap(&r1, &tmp);          /* r0, r1 = r1, r0 - q r1 */
        e = lc_int_mul(&tmp, &q, &s1); if (e) break;
        e = lc_int_sub(&tmp, &s0, &tmp); if (e) break;
        lc_int_swap(&s0, &s1); lc_int_swap(&s1, &tmp);
        e = lc_int_mul(&tmp, &q, &t1); if (e) break;
        e = lc_int_sub(&tmp, &t0, &tmp); if (e) break;
        lc_int_swap(&t0, &t1); lc_int_swap(&t1, &tmp);
    }
    if (!e && r0.sign < 0) { r0.sign = 1; s0.sign = -s0.sign; t0.sign = -t0.sign; }
    if (!e) {
        if (g) lc_int_swap(g, &r0);
        if (x) lc_int_swap(x, &s0);
        if (y) lc_int_swap(y, &t0);
    }
    for (int i = 0; i < 8; i++) lc_int_clear(all[i]);
    return e;
}

int lc_int_lcm(lc_int *r, const lc_int *a, const lc_int *b)
{
    if (a->len == 0 || b->len == 0) { r->len = 0; r->sign = 0; return LC_OK; }
    lc_int g, t; lc_int_init(&g); lc_int_init(&t);
    int e = lc_int_gcd(&g, a, b);
    if (!e) e = lc_int_divexact(&t, a, &g);
    if (!e) e = lc_int_mul(&t, &t, b);
    if (!e) { if (t.sign < 0) t.sign = 1; lc_int_swap(r, &t); }
    lc_int_clear(&g); lc_int_clear(&t);
    return e;
}

int lc_int_invmod(lc_int *r, const lc_int *a, const lc_int *m)
{
    if (m->sign <= 0) return LC_EDOMAIN;
    lc_int g, x; lc_int_init(&g); lc_int_init(&x);
    int e = lc_int_gcdext(&g, &x, NULL, a, m);
    if (!e && !lc_int_is_one(&g)) e = LC_EDOMAIN;
    if (!e) e = lc_int_edivmod(NULL, r, &x, m);
    lc_int_clear(&g); lc_int_clear(&x);
    return e;
}

int lc_int_powmod_basic(lc_int *r, const lc_int *a, const lc_int *ex, const lc_int *m)
{
    if (m->sign <= 0 || ex->sign < 0) return LC_EDOMAIN;
    lc_int base, acc; lc_int_init(&base); lc_int_init(&acc);
    int e = lc_int_edivmod(NULL, &base, a, m);
    if (!e) e = lc_int_set_i64(&acc, 1);
    if (!e) e = lc_int_edivmod(NULL, &acc, &acc, m);
    size_t bits = lc_int_bitlen(ex);
    for (size_t i = bits; !e && i-- > 0;) {
        e = lc_int_mul(&acc, &acc, &acc);
        if (!e) e = lc_int_edivmod(NULL, &acc, &acc, m);
        if (!e && ((ex->d[i / 32] >> (i % 32)) & 1)) {
            e = lc_int_mul(&acc, &acc, &base);
            if (!e) e = lc_int_edivmod(NULL, &acc, &acc, m);
        }
    }
    if (!e) lc_int_swap(r, &acc);
    lc_int_clear(&base); lc_int_clear(&acc);
    return e;
}

/* ------------------------------------------------------------------ */
/* Montgomery modular exponentiation (odd moduli)                       */
/* ------------------------------------------------------------------ */

#if defined(__SIZEOF_INT128__)
__extension__ typedef unsigned __int128 mlimb2;
typedef uint64_t mlimb;
#define MBITS 64
#else
typedef dlimb mlimb2;
typedef limb mlimb;
#define MBITS 32
#endif

/* r = a * b * 2^(-MBITS n) mod m, for a, b < m (n words each), m odd; t is scratch of n + 2 words.
   CIOS (coarsely integrated operand scanning): interleaves one row of the product with one
   Montgomery reduction step, so no double-length product and no division is ever formed.
   Words are 64-bit when the compiler has a 128-bit type (4x fewer word products). */
static void mont_mul(mlimb *r, const mlimb *a, const mlimb *b, const mlimb *m, size_t n,
                     mlimb minv, mlimb *t)
{
    memset(t, 0, (n + 2) * sizeof(mlimb));
    for (size_t i = 0; i < n; i++) {
        mlimb2 c = 0, ai = a[i];
        for (size_t j = 0; j < n; j++) {
            c += (mlimb2)t[j] + ai * b[j];
            t[j] = (mlimb)c; c >>= MBITS;
        }
        c += t[n]; t[n] = (mlimb)c; t[n + 1] = (mlimb)(c >> MBITS);
        mlimb u = t[0] * minv;
        c = ((mlimb2)t[0] + (mlimb2)u * m[0]) >> MBITS;
        for (size_t j = 1; j < n; j++) {
            c += (mlimb2)t[j] + (mlimb2)u * m[j];
            t[j - 1] = (mlimb)c; c >>= MBITS;
        }
        c += t[n]; t[n - 1] = (mlimb)c; c >>= MBITS;
        t[n] = t[n + 1] + (mlimb)c;
    }
    int ge = t[n] != 0;
    if (!ge) {
        ge = 1;
        for (size_t j = n; j-- > 0;) {
            if (t[j] != m[j]) { ge = t[j] > m[j]; break; }
        }
    }
    if (ge) {
        mlimb bw = 0;
        for (size_t j = 0; j < n; j++) {
            mlimb x = t[j], y = m[j] + bw;
            mlimb nb = (y < bw) || (x < y);
            t[j] = x - y; bw = nb;
        }
    }
    memcpy(r, t, n * sizeof(mlimb));
}

/* lc_int (32-bit limbs) <-> machine words */
static void to_words(mlimb *w, size_t n, const lc_int *a)
{
    memset(w, 0, n * sizeof(mlimb));
    for (size_t i = 0; i < a->len; i++)
        w[i / (MBITS / 32)] |= (mlimb)a->d[i] << (32 * (i % (MBITS / 32)));
}

/* Fixed-window (5-bit) Montgomery ladder; m odd, m > 1. */
static int powmod_mont(lc_int *r, const lc_int *a, const lc_int *ex, const lc_int *m)
{
    enum { W = 5, TS = 1 << W };
    size_t n = (m->len + (MBITS / 32) - 1) / (MBITS / 32);
    mlimb *mw = calloc(n, sizeof(mlimb));
    if (!mw) return LC_ENOMEM;
    to_words(mw, n, m);
    mlimb m0 = mw[0], x = m0;
    for (int k = 0; k < 6; k++) x *= 2 - m0 * x;      /* x = m0^(-1) mod 2^MBITS */
    mlimb minv = (mlimb)0 - x;
    int e = LC_OK;
    lc_int t1; lc_int_init(&t1);
    mlimb *mem = calloc((size_t)(TS + 3) * n + 2, sizeof(mlimb));
    if (!mem) { free(mw); lc_int_clear(&t1); return LC_ENOMEM; }
    mlimb *tab = mem, *acc = mem + (size_t)TS * n, *one = acc + n, *scr = one + n;
    /* tab[1] = a R mod m, tab[0] = R mod m, R = 2^(MBITS n) */
    e = lc_int_edivmod(NULL, &t1, a, m);
    if (!e) e = lc_int_shl(&t1, &t1, (size_t)MBITS * n);
    if (!e) e = lc_int_edivmod(NULL, &t1, &t1, m);
    if (!e) to_words(tab + n, n, &t1);
    if (!e) e = lc_int_set_i64(&t1, 1);
    if (!e) e = lc_int_shl(&t1, &t1, (size_t)MBITS * n);
    if (!e) e = lc_int_edivmod(NULL, &t1, &t1, m);
    if (!e) to_words(tab, n, &t1);
    if (!e) {
        for (int k = 2; k < TS; k++)
            mont_mul(tab + (size_t)k * n, tab + (size_t)(k - 1) * n, tab + n, mw, n, minv, scr);
        size_t bits = lc_int_bitlen(ex);
        memcpy(acc, tab, n * sizeof(mlimb));
        size_t top = bits ? (bits - 1) / W : 0;
        for (size_t blk = top + 1; blk-- > 0;) {
            unsigned w = 0;
            for (int b = W - 1; b >= 0; b--) {
                size_t i = blk * W + (size_t)b;
                w = (w << 1) | (i < bits ? ((ex->d[i / 32] >> (i % 32)) & 1u) : 0u);
            }
            if (blk != top) for (int b = 0; b < W; b++) mont_mul(acc, acc, acc, mw, n, minv, scr);
            if (w) mont_mul(acc, acc, tab + (size_t)w * n, mw, n, minv, scr);
        }
        /* leave Montgomery form: multiply by 1 */
        memset(one, 0, n * sizeof(mlimb)); one[0] = 1;
        mont_mul(acc, acc, one, mw, n, minv, scr);
        size_t n32 = n * (MBITS / 32);
        e = reserve(r, n32);
        if (!e) {
            for (size_t i = 0; i < n32; i++)
                r->d[i] = (limb)(acc[i / (MBITS / 32)] >> (32 * (i % (MBITS / 32))));
            r->len = n32; r->sign = 1; trim(r);
        }
    }
    free(mem); free(mw); lc_int_clear(&t1);
    return e;
}

int lc_int_powmod(lc_int *r, const lc_int *a, const lc_int *ex, const lc_int *m)
{
    if (m->sign <= 0 || ex->sign < 0) return LC_EDOMAIN;
    /* Montgomery pays off for odd moduli of a few limbs and up; otherwise plain square-and-multiply */
    if (m->len >= 2 && (m->d[0] & 1u)) return powmod_mont(r, a, ex, m);
    return lc_int_powmod_basic(r, a, ex, m);
}

int lc_int_sqrt(lc_int *r, const lc_int *a)
{
    if (a->sign < 0) return LC_EDOMAIN;
    if (a->len == 0) { r->len = 0; r->sign = 0; return LC_OK; }
    lc_int x, y; lc_int_init(&x); lc_int_init(&y);
    size_t bl = lc_int_bitlen(a);
    int e = lc_int_set_i64(&x, 1);
    if (!e) e = lc_int_shl(&x, &x, (bl + 1) / 2);      /* x >= sqrt(a) */
    while (!e) {
        e = lc_int_tdivmod(&y, NULL, a, &x);
        if (!e) e = lc_int_add(&y, &y, &x);
        if (!e) e = lc_int_shr(&y, &y, 1);
        if (e) break;
        if (lc_int_cmp(&y, &x) >= 0) break;
        lc_int_swap(&x, &y);
    }
    if (!e) lc_int_swap(r, &x);
    lc_int_clear(&x); lc_int_clear(&y);
    return e;
}

int lc_int_is_probable_prime(const lc_int *a, int rounds)
{
    static const uint32_t small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                                     59, 61, 67, 71, 73, 79, 83, 89, 97};
    const int nsmall = (int)(sizeof small / sizeof small[0]);
    if (a->sign <= 0) return 0;
    if (a->len == 1 && a->d[0] < 2) return 0;
    for (int i = 0; i < nsmall; i++) {
        if (a->len == 1 && a->d[0] == small[i]) return 1;
        if (lc_int_mod_u32(a, small[i]) == 0) return 0;
    }
    if (rounds < 1) rounds = 1;
    if (rounds > nsmall) rounds = nsmall;
    lc_int nm1, dd, x, b; lc_int_init(&nm1); lc_int_init(&dd); lc_int_init(&x); lc_int_init(&b);
    int e = lc_int_add_i64(&nm1, a, -1), result = 1;
    size_t s = 0;
    if (!e) e = lc_int_copy(&dd, &nm1);
    while (!e && lc_int_is_even(&dd)) { e = lc_int_shr(&dd, &dd, 1); s++; }
    for (int i = 0; !e && i < rounds && result; i++) {
        e = lc_int_set_u64(&b, small[i]);
        if (!e) e = lc_int_powmod(&x, &b, &dd, a);
        if (e) break;
        if (lc_int_is_one(&x) || lc_int_cmp(&x, &nm1) == 0) continue;
        int witness = 1;
        for (size_t k = 1; k < s && !e; k++) {
            e = lc_int_mul(&x, &x, &x);
            if (!e) e = lc_int_edivmod(NULL, &x, &x, a);
            if (!e && lc_int_cmp(&x, &nm1) == 0) { witness = 0; break; }
        }
        if (witness) result = 0;
    }
    lc_int_clear(&nm1); lc_int_clear(&dd); lc_int_clear(&x); lc_int_clear(&b);
    return e ? e : result;
}

/* ------------------------------------------------------------------ */
/* deterministic primality                                             */
/* ------------------------------------------------------------------ */

int lc_int_is_prime(const lc_int *a)
{
    if (a->sign <= 0 || lc_int_cmp_i64(a, 2) < 0) return 0;
    lc_int r, d; lc_int_init(&r); lc_int_init(&d);
    int e = lc_int_sqrt(&r, a), result = 1;
    if (!e) e = lc_int_set_i64(&d, 2);
    while (!e && lc_int_cmp(&d, &r) <= 0) {
        if (lc_int_divisible(a, &d)) { result = 0; break; }
        e = lc_int_add_i64(&d, &d, lc_int_cmp_i64(&d, 2) == 0 ? 1 : 2);
    }
    lc_int_clear(&r); lc_int_clear(&d);
    return e ? e : result;
}

static int pratt_line(const lc_pratt_entry *cert, size_t i)
{
    const lc_pratt_entry *en = &cert[i];
    if (lc_int_cmp_i64(&en->p, 2) < 0 || en->a.sign < 0) return 0;
    lc_int pm1, prod, x, k; lc_int_init(&pm1); lc_int_init(&prod); lc_int_init(&x); lc_int_init(&k);
    int e = lc_int_add_i64(&pm1, &en->p, -1), ok = 1;
    if (!e) e = lc_int_set_i64(&prod, 1);
    for (size_t j = 0; !e && j < en->nqs; j++) e = lc_int_mul(&prod, &prod, &en->qs[j]);
    if (!e && lc_int_cmp(&prod, &pm1) != 0) ok = 0;
    for (size_t j = 0; !e && ok && j < en->nqs; j++) {          /* each q certified above */
        int found = 0;
        for (size_t t = 0; t < i && !found; t++) found = lc_int_cmp(&cert[t].p, &en->qs[j]) == 0;
        if (!found) ok = 0;
    }
    if (!e && ok) e = lc_int_powmod(&x, &en->a, &pm1, &en->p);
    if (!e && ok && !lc_int_is_one(&x)) ok = 0;                 /* a^(p-1) = 1 */
    for (size_t j = 0; !e && ok && j < en->nqs; j++) {          /* a^((p-1)/q) != 1 */
        e = lc_int_tdivmod(&k, NULL, &pm1, &en->qs[j]);
        if (!e) e = lc_int_powmod(&x, &en->a, &k, &en->p);
        if (!e && lc_int_is_one(&x)) ok = 0;
    }
    lc_int_clear(&pm1); lc_int_clear(&prod); lc_int_clear(&x); lc_int_clear(&k);
    return e ? e : ok;
}

int lc_int_check_pratt(const lc_pratt_entry *cert, size_t len, const lc_int *n)
{
    int listed = 0;
    for (size_t i = 0; i < len; i++) {
        int r = pratt_line(cert, i);
        if (r != 1) return r;
        if (lc_int_cmp(&cert[i].p, n) == 0) listed = 1;
    }
    return listed;
}
