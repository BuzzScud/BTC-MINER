/* latcalc -- one shared, resident abacus; systems of formulas; rod Montgomery. */
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdatomic.h>
#include <stdint.h>
#include "latcalc/abacus.h"

struct lc_abacus {
    _Atomic unsigned refs;
    size_t     n;
    uint32_t  *m;          /* the rods */
    size_t    *origin;     /* index of each rod in the root */
    lc_abacus *root;       /* root abacus (self for a root); views and merges keep it alive */
    size_t     N;          /* number of rods of the root */
    uint32_t  *ginv;       /* root only: ginv[i*N + j] = m_j^{-1} mod m_i (0 on the diagonal) */
    double     bits;
};

/* ---- small rod arithmetic ------------------------------------------------------------------ */

static inline uint32_t mulmod(uint32_t a, uint32_t b, uint32_t m) { return (uint32_t)((uint64_t)a * b % m); }

static uint32_t powmod32(uint32_t b, uint64_t e, uint32_t m)
{
    uint64_t r = 1 % m, x = b % m;
    while (e) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; }
    return (uint32_t)r;
}

static uint32_t invmod32(uint32_t a, uint32_t m)   /* a coprime to m, m >= 2 */
{
    int64_t t = 0, nt = 1, r = m, nr = a % m;
    while (nr) { int64_t q = r / nr, tmp;
        tmp = t - q * nt; t = nt; nt = tmp;
        tmp = r - q * nr; r = nr; nr = tmp; }
    if (t < 0) t += m;
    return (uint32_t)t;
}

static uint32_t gcd32(uint32_t a, uint32_t b) { while (b) { uint32_t t = a % b; a = b; b = t; } return a; }

static int is_prime32(uint32_t n)
{
    if (n < 2) return 0;
    static const uint32_t sp[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (size_t i = 0; i < 12; i++) { if (n == sp[i]) return 1; if (n % sp[i] == 0) return 0; }
    uint32_t d = n - 1; int s = 0; while (!(d & 1)) { d >>= 1; s++; }
    static const uint32_t bases[] = {2, 7, 61};
    for (size_t i = 0; i < 3; i++) {
        uint64_t x = powmod32(bases[i], d, n);
        if (x == 1 || x == n - 1) continue;
        int ok = 0;
        for (int r = 1; r < s; r++) { x = x * x % n; if (x == n - 1) { ok = 1; break; } }
        if (!ok) return 0;
    }
    return 1;
}

static int64_t smod(int64_t c, uint32_t q) { int64_t r = c % (int64_t)q; return r < 0 ? r + q : r; }

/* ---- construction -------------------------------------------------------------------------- */

static lc_abacus *alloc_abacus(size_t n)
{
    lc_abacus *a = calloc(1, sizeof *a);
    if (!a) return NULL;
    atomic_init(&a->refs, 1); a->n = n;
    a->m = malloc(n * sizeof *a->m);
    a->origin = malloc(n * sizeof *a->origin);
    if (!a->m || !a->origin) { free(a->m); free(a->origin); free(a); return NULL; }
    return a;
}

static void set_bits(lc_abacus *a)
{
    double b = 0; for (size_t i = 0; i < a->n; i++) b += log2((double)a->m[i]); a->bits = b;
}

lc_abacus *lc_abacus_new(const uint32_t *moduli, size_t n, int *err)
{
    int e0; if (!err) err = &e0;
    *err = LC_OK;
    if (!moduli || n == 0 || n > 8192) { *err = LC_EINVAL; return NULL; }
    for (size_t i = 0; i < n; i++) {
        if (moduli[i] < 2 || moduli[i] >= (1u << 31)) { *err = LC_EDOMAIN; return NULL; }
        for (size_t j = 0; j < i; j++) if (gcd32(moduli[i], moduli[j]) != 1) { *err = LC_EDOMAIN; return NULL; }
    }
    lc_abacus *a = alloc_abacus(n);
    if (!a) { *err = LC_ENOMEM; return NULL; }
    a->ginv = malloc(n * n * sizeof *a->ginv);
    if (!a->ginv) { free(a->m); free(a->origin); free(a); *err = LC_ENOMEM; return NULL; }
    for (size_t i = 0; i < n; i++) { a->m[i] = moduli[i]; a->origin[i] = i; }
    for (size_t i = 0; i < n; i++)
        for (size_t j = 0; j < n; j++)
            a->ginv[i * n + j] = (i == j) ? 0 : invmod32(moduli[j] % moduli[i], moduli[i]);
    a->root = a; a->N = n;
    set_bits(a);
    return a;
}

lc_abacus *lc_abacus_primes(size_t n, int *err)
{
    if (n == 0 || n > 8192) { if (err) *err = LC_EINVAL; return NULL; }
    uint32_t *ps = malloc(n * sizeof *ps);
    if (!ps) { if (err) *err = LC_ENOMEM; return NULL; }
    uint32_t c = (1u << 31) - 1; size_t got = 0;
    while (got < n) { if (is_prime32(c)) ps[got++] = c; c -= 2; }
    lc_abacus *a = lc_abacus_new(ps, n, err);
    free(ps);
    return a;
}

lc_abacus *lc_abacus_retain(lc_abacus *a) { if (a) atomic_fetch_add_explicit(&a->refs, 1, memory_order_relaxed); return a; }

void lc_abacus_release(lc_abacus *a)
{
    if (!a || atomic_fetch_sub_explicit(&a->refs, 1, memory_order_acq_rel) != 1) return;
    if (a->root != a) lc_abacus_release(a->root);
    else free(a->ginv);
    free(a->m); free(a->origin); free(a);
}

size_t          lc_abacus_size(const lc_abacus *a) { return a->n; }
const uint32_t *lc_abacus_moduli(const lc_abacus *a) { return a->m; }
double          lc_abacus_capacity_bits(const lc_abacus *a) { return a->bits; }
size_t          lc_abacus_origin(const lc_abacus *a, size_t i) { return a->origin[i]; }

lc_abacus *lc_abacus_view(lc_abacus *a, const size_t *idx, size_t k, int *err)
{
    int e0; if (!err) err = &e0;
    *err = LC_OK;
    if (k == 0) { *err = LC_EINVAL; return NULL; }
    for (size_t i = 0; i < k; i++) {
        if (idx[i] >= a->n) { *err = LC_EINVAL; return NULL; }
        for (size_t j = 0; j < i; j++) if (idx[i] == idx[j]) { *err = LC_EINVAL; return NULL; }
    }
    lc_abacus *v = alloc_abacus(k);
    if (!v) { *err = LC_ENOMEM; return NULL; }
    for (size_t i = 0; i < k; i++) { v->m[i] = a->m[idx[i]]; v->origin[i] = a->origin[idx[i]]; }
    v->root = lc_abacus_retain(a->root); v->N = a->N; v->ginv = a->root->ginv;   /* shared table */
    set_bits(v);
    return v;
}

lc_abacus *lc_abacus_merge(const lc_abacus *a, const lc_abacus *b, int *err)
{
    size_t n = a->n + b->n;
    uint32_t *ms = malloc(n * sizeof *ms);
    if (!ms) { if (err) *err = LC_ENOMEM; return NULL; }
    memcpy(ms, a->m, a->n * sizeof *ms);
    memcpy(ms + a->n, b->m, b->n * sizeof *ms);
    lc_abacus *r = lc_abacus_new(ms, n, err);    /* checks the cross coprimality */
    free(ms);
    return r;
}

/* ---- columns ------------------------------------------------------------------------------- */

static inline uint32_t ginv_of(const lc_abacus *a, size_t i, size_t j)   /* m_j^{-1} mod m_i */
{
    return a->ginv[a->origin[i] * a->N + a->origin[j]];
}

int lc_abacus_encode(const lc_abacus *a, uint32_t *col, const lc_int *x)
{
    for (size_t i = 0; i < a->n; i++) col[i] = lc_int_mod_u32(x, a->m[i]);
    return LC_OK;
}

void lc_abacus_encode_i64(const lc_abacus *a, uint32_t *col, int64_t x)
{
    for (size_t i = 0; i < a->n; i++) col[i] = (uint32_t)smod(x, a->m[i]);
}

int lc_abacus_decode(const lc_abacus *a, lc_int *x, const uint32_t *col)
{
    size_t n = a->n;
    uint32_t *v = malloc(n * sizeof *v);
    if (!v) return LC_ENOMEM;
    /* Garner: mixed-radix digits, all on single rods */
    for (size_t i = 0; i < n; i++) {
        uint32_t q = a->m[i], t = col[i] % q;
        for (size_t j = 0; j < i; j++) {
            uint32_t vj = v[j] % q;
            t = mulmod((t + q - vj) % q, ginv_of(a, i, j), q);
        }
        v[i] = t;
    }
    /* Horner, only now forming the positional number */
    int e = lc_int_set_u64(x, v[n - 1]);
    for (size_t i = n - 1; !e && i-- > 0; ) {
        e = lc_int_mul_i64(x, x, a->m[i]);
        if (!e) e = lc_int_add_i64(x, x, v[i]);
    }
    free(v);
    return e;
}

int lc_abacus_decode_signed(const lc_abacus *a, lc_int *x, const uint32_t *col)
{
    /* x > M/2 iff the reversed-complement column decodes below M/2: use M - x comparison */
    int e = lc_abacus_decode(a, x, col);
    if (e) return e;
    lc_int M, twice; lc_int_init(&M); lc_int_init(&twice);
    e = lc_int_set_u64(&M, 1);
    for (size_t i = 0; !e && i < a->n; i++) e = lc_int_mul_i64(&M, &M, a->m[i]);
    if (!e) e = lc_int_shl(&twice, x, 1);
    if (!e && lc_int_cmp(&twice, &M) > 0) e = lc_int_sub(x, x, &M);
    lc_int_clear(&M); lc_int_clear(&twice);
    return e;
}

int lc_abacus_col_equal(const lc_abacus *a, const uint32_t *c1, const uint32_t *c2)
{
    for (size_t i = 0; i < a->n; i++) if (c1[i] != c2[i]) return 0;
    return 1;
}

/* ---- programs ------------------------------------------------------------------------------ */

int lc_abacus_run(const lc_abacus *a, const lc_aop *ops, size_t nops, uint32_t *const *slots,
                  size_t nslots)
{
    for (size_t t = 0; t < nops; t++) {
        const lc_aop *o = &ops[t];
        if (o->dst < 0 || (size_t)o->dst >= nslots) return LC_EINVAL;
        int na = (o->kind == LC_AOP_CONST) ? 0 :
                 (o->kind == LC_AOP_ADD || o->kind == LC_AOP_SUB || o->kind == LC_AOP_MUL) ? 2 : 1;
        if (na >= 1 && (o->a < 0 || (size_t)o->a >= nslots)) return LC_EINVAL;
        if (na >= 2 && (o->b < 0 || (size_t)o->b >= nslots)) return LC_EINVAL;
        if (o->kind < LC_AOP_CONST || o->kind > LC_AOP_ADDC) return LC_EINVAL;
    }
    /* rod by rod: the whole system advances on one rod, independently of the other rods */
    for (size_t i = 0; i < a->n; i++) {
        uint32_t q = a->m[i];
        for (size_t t = 0; t < nops; t++) {
            const lc_aop *o = &ops[t];
            uint32_t x = (o->kind == LC_AOP_CONST) ? 0 : slots[o->a][i];
            uint32_t r;
            switch (o->kind) {
            case LC_AOP_CONST: r = (uint32_t)smod(o->c, q); break;
            case LC_AOP_COPY:  r = x; break;
            case LC_AOP_ADD:   r = (uint32_t)(((uint64_t)x + slots[o->b][i]) % q); break;
            case LC_AOP_SUB:   r = (uint32_t)(((uint64_t)x + q - slots[o->b][i]) % q); break;
            case LC_AOP_MUL:   r = mulmod(x, slots[o->b][i], q); break;
            case LC_AOP_POW:   r = powmod32(x, o->e, q); break;
            case LC_AOP_MULC:  r = mulmod(x, (uint32_t)smod(o->c, q), q); break;
            default:           r = (uint32_t)(((uint64_t)x + (uint64_t)smod(o->c, q)) % q); break;
            }
            slots[o->dst][i] = r;
        }
    }
    return LC_OK;
}

/* ---- jumps ---------------------------------------------------------------------------------- */

static void matmul_mod(uint64_t *r, const uint64_t *x, const uint64_t *y, size_t d, uint64_t q)
{
    uint64_t t[64];
    for (size_t i = 0; i < d; i++)
        for (size_t j = 0; j < d; j++) {
            uint64_t s = 0;
            for (size_t k = 0; k < d; k++) s = (s + x[i * d + k] * y[k * d + j]) % q;
            t[i * d + j] = s;
        }
    memcpy(r, t, d * d * sizeof *t);
}

int lc_abacus_linrec(const lc_abacus *a, uint32_t *col, const int64_t *c, const int64_t *init,
                     size_t d, uint64_t N)
{
    if (d == 0 || d > 8) return LC_EINVAL;
    for (size_t i = 0; i < a->n; i++) {
        uint32_t q = a->m[i];
        if (N < d) { col[i] = (uint32_t)smod(init[N], q); continue; }
        /* state (u_{n}, u_{n-1}, ..., u_{n-d+1}); companion matrix T */
        uint64_t T[64], R[64];
        memset(T, 0, sizeof T); memset(R, 0, sizeof R);
        for (size_t j = 0; j < d; j++) T[j] = (uint64_t)smod(c[j], q);
        for (size_t r = 1; r < d; r++) T[r * d + r - 1] = 1;
        for (size_t r = 0; r < d; r++) R[r * d + r] = 1 % q;
        uint64_t e = N - (d - 1);
        while (e) { if (e & 1) matmul_mod(R, R, T, d, q); matmul_mod(T, T, T, d, q); e >>= 1; }
        uint64_t s = 0;
        for (size_t j = 0; j < d; j++) s = (s + R[j] * (uint64_t)smod(init[d - 1 - j], q)) % q;
        col[i] = (uint32_t)s;
    }
    return LC_OK;
}

/* ---- rod Montgomery ------------------------------------------------------------------------ */

struct lc_rmont {
    lc_abacus *ab;
    size_t k, l;
    const uint32_t *a, *b;
    uint32_t r;
    lc_int p;
    uint32_t *negpinv, *cinvA, *cAb, *cAr, *mAinvB, mAinvR;
    uint32_t *cinvB, *cBa, *cBr, mBinvR, *mBa, *pb, pr;
    uint32_t *t1, *t2, *one, *base, *acc, *sig;   /* work columns (k + l + 1) */
};

static int testbit(const lc_int *e, size_t i)
{
    return (i / 32 < e->len) ? (int)((e->d[i / 32] >> (i % 32)) & 1u) : 0;
}

/* prod_{i != skip} v[i] mod d (skip = n for no skip) */
static uint32_t prod_mod(const uint32_t *v, size_t n, size_t skip, uint32_t d)
{
    uint64_t r = 1 % d;
    for (size_t i = 0; i < n; i++) if (i != skip) r = r * (v[i] % d) % d;
    return (uint32_t)r;
}

static int big_prod(lc_int *M, const uint32_t *v, size_t n)
{
    int e = lc_int_set_u64(M, 1);
    for (size_t i = 0; !e && i < n; i++) e = lc_int_mul_i64(M, M, v[i]);
    return e;
}

/* conditions (C p)^2 + k MA p <= MB MA and <= C p MA with C = 2k + 2 */
static int rmont_fits(const uint32_t *a, size_t k, const uint32_t *b, size_t l, const lc_int *p)
{
    lc_int MA, MB, Cp, lhs, t, rhs; lc_int_init(&MA); lc_int_init(&MB); lc_int_init(&Cp);
    lc_int_init(&lhs); lc_int_init(&t); lc_int_init(&rhs);
    int ok = 0;
    if (!big_prod(&MA, a, k) && !big_prod(&MB, b, l) &&
        !lc_int_mul_i64(&Cp, p, (int64_t)(2 * k + 2)) &&
        !lc_int_mul(&lhs, &Cp, &Cp) && !lc_int_mul(&t, &MA, p) && !lc_int_mul_i64(&t, &t, (int64_t)k) &&
        !lc_int_add(&lhs, &lhs, &t)) {
        if (!lc_int_mul(&rhs, &MB, &MA) && lc_int_cmp(&lhs, &rhs) <= 0 &&
            !lc_int_mul(&rhs, &Cp, &MA) && lc_int_cmp(&lhs, &rhs) <= 0) ok = 1;
    }
    lc_int_clear(&MA); lc_int_clear(&MB); lc_int_clear(&Cp); lc_int_clear(&lhs);
    lc_int_clear(&t); lc_int_clear(&rhs);
    return ok;
}

size_t lc_rmont_fit(const lc_abacus *ab, const lc_int *p)
{
    for (size_t k = 1; 2 * k + 1 <= ab->n; k++)
        if (ab->m[2 * k] >= k && rmont_fits(ab->m, k, ab->m + k, k, p)) return k;
    return 0;
}

void lc_rmont_free(lc_rmont *c)
{
    if (!c) return;
    free(c->negpinv); free(c->cinvA); free(c->cAb); free(c->cAr); free(c->mAinvB);
    free(c->cinvB); free(c->cBa); free(c->cBr); free(c->mBa); free(c->pb);
    free(c->t1); free(c->t2); free(c->one); free(c->base); free(c->acc); free(c->sig);
    lc_int_clear(&c->p);
    lc_abacus_release(c->ab);
    free(c);
}

lc_rmont *lc_rmont_new(lc_abacus *ab, size_t k, size_t l, const lc_int *p, int *err)
{
    int e0; if (!err) err = &e0;
    *err = LC_OK;
    if (k == 0 || l == 0 || k + l + 1 > ab->n || lc_int_sign(p) <= 0 || lc_int_is_even(p)) {
        *err = LC_EINVAL; return NULL;
    }
    const uint32_t *a = ab->m, *b = ab->m + k; uint32_t r = ab->m[k + l];
    if (r < l || !rmont_fits(a, k, b, l, p)) { *err = LC_EDOMAIN; return NULL; }
    for (size_t i = 0; i < k; i++) if (gcd32(lc_int_mod_u32(p, a[i]), a[i]) != 1) { *err = LC_EDOMAIN; return NULL; }
    lc_rmont *c = calloc(1, sizeof *c);
    if (!c) { *err = LC_ENOMEM; return NULL; }
    c->ab = lc_abacus_retain(ab); c->k = k; c->l = l; c->a = a; c->b = b; c->r = r;
    lc_int_init(&c->p);
    size_t w = k + l + 1;
    c->negpinv = malloc(k * 4); c->cinvA = malloc(k * 4); c->cAb = malloc(k * l * 4);
    c->cAr = malloc(k * 4); c->mAinvB = malloc(l * 4); c->cinvB = malloc(l * 4);
    c->cBa = malloc(k * l * 4); c->cBr = malloc(l * 4); c->mBa = malloc(k * 4); c->pb = malloc(l * 4);
    c->t1 = malloc(w * 4); c->t2 = malloc(w * 4); c->one = malloc(w * 4); c->base = malloc(w * 4);
    c->acc = malloc(w * 4); c->sig = malloc((k > l ? k : l) * 4);
    if (!c->negpinv || !c->cinvA || !c->cAb || !c->cAr || !c->mAinvB || !c->cinvB || !c->cBa ||
        !c->cBr || !c->mBa || !c->pb || !c->t1 || !c->t2 || !c->one || !c->base || !c->acc ||
        !c->sig || lc_int_copy(&c->p, p)) { lc_rmont_free(c); *err = LC_ENOMEM; return NULL; }
    /* all tables are small-rod computations */
    for (size_t i = 0; i < k; i++) {
        uint32_t pi = lc_int_mod_u32(p, a[i]);
        c->negpinv[i] = (a[i] - invmod32(pi, a[i])) % a[i];
        c->cinvA[i] = invmod32(prod_mod(a, k, i, a[i]), a[i]);
        c->cAr[i] = prod_mod(a, k, i, r);
        c->mBa[i] = prod_mod(b, l, l, a[i]);
    }
    for (size_t j = 0; j < l; j++) {
        c->mAinvB[j] = invmod32(prod_mod(a, k, k, b[j]), b[j]);
        c->cinvB[j] = invmod32(prod_mod(b, l, j, b[j]), b[j]);
        c->cBr[j] = prod_mod(b, l, j, r);
        c->pb[j] = lc_int_mod_u32(p, b[j]);
        for (size_t i = 0; i < k; i++) {
            c->cAb[j * k + i] = prod_mod(a, k, i, b[j]);
            c->cBa[i * l + j] = prod_mod(b, l, j, a[i]);
        }
    }
    c->mAinvR = invmod32(prod_mod(a, k, k, r), r);
    c->mBinvR = invmod32(prod_mod(b, l, l, r), r);
    c->pr = lc_int_mod_u32(p, r);
    return c;
}

/* sum_i s[i] * t[i] mod d, with s, t < 2^31: four products fit in 64 bits before a reduction */
static uint32_t dot_mod(const uint32_t *s, const uint32_t *t, size_t n, uint32_t d)
{
    uint64_t acc = 0; size_t i = 0;
    for (; i + 4 <= n; i += 4) {
        uint64_t u = (uint64_t)s[i] * t[i] + (uint64_t)s[i + 1] * t[i + 1];
        uint64_t v = (uint64_t)s[i + 2] * t[i + 2] + (uint64_t)s[i + 3] * t[i + 3];
        acc = (acc + u % d + v % d) % d;
    }
    for (; i < n; i++) acc = (acc + (uint64_t)s[i] * t[i] % d) % d;
    return (uint32_t)acc;
}

/* z = montMul(x, y): exactly the steps of RodMont.montMul (z may alias x or y) */
static void rmont_mul(lc_rmont *c, uint32_t *z, const uint32_t *x, const uint32_t *y)
{
    size_t k = c->k, l = c->l;
    const uint32_t *a = c->a, *b = c->b; uint32_t r = c->r;
    uint32_t *sig = c->sig, *Rb = c->t2;
    for (size_t i = 0; i < k; i++) {                   /* quotient digits and sigma on A */
        uint32_t qa = mulmod(mulmod(x[i], y[i], a[i]), c->negpinv[i], a[i]);
        sig[i] = mulmod(qa, c->cinvA[i], a[i]);
    }
    for (size_t j = 0; j < l; j++) {                   /* extend to B, divide by M_A */
        uint32_t qb = dot_mod(sig, c->cAb + j * k, k, b[j]);
        uint64_t t = ((uint64_t)mulmod(x[k + j], y[k + j], b[j]) + (uint64_t)qb * c->pb[j]) % b[j];
        Rb[j] = mulmod((uint32_t)t, c->mAinvB[j], b[j]);
    }
    uint32_t qr = dot_mod(sig, c->cAr, k, r);
    uint64_t tr = ((uint64_t)mulmod(x[k + l], y[k + l], r) + (uint64_t)qr * c->pr) % r;
    uint32_t Rr = mulmod((uint32_t)tr, c->mAinvR, r);
    for (size_t j = 0; j < l; j++) sig[j] = mulmod(Rb[j], c->cinvB[j], b[j]);   /* back to A */
    uint32_t Sr = dot_mod(sig, c->cBr, l, r);
    uint32_t beta = mulmod((uint32_t)(((uint64_t)Sr + r - Rr) % r), c->mBinvR, r);
    for (size_t i = 0; i < k; i++) {
        uint32_t Sa = dot_mod(sig, c->cBa + i * l, l, a[i]);
        z[i] = (uint32_t)(((uint64_t)Sa + a[i] - mulmod(beta, c->mBa[i], a[i])) % a[i]);
    }
    memcpy(z + k, Rb, l * sizeof *z);
    z[k + l] = Rr;
}

int lc_rmont_powmod(lc_rmont *c, lc_int *res, const lc_int *bse, const lc_int *e)
{
    if (lc_int_sign(bse) < 0 || lc_int_sign(e) < 0) return LC_EDOMAIN;
    size_t k = c->k, l = c->l, w = k + l + 1;
    const uint32_t *rods = c->ab->m;
    /* input conversion: Montgomery forms of 1 and of the base (the only long arithmetic
       besides the final read-back) */
    lc_int MA, t; lc_int_init(&MA); lc_int_init(&t);
    int err = big_prod(&MA, c->a, k);
    if (!err) err = lc_int_edivmod(NULL, &t, &MA, &c->p);
    for (size_t i = 0; !err && i < w; i++) c->one[i] = lc_int_mod_u32(&t, rods[i]);
    if (!err) err = lc_int_mul(&t, bse, &MA);
    if (!err) err = lc_int_edivmod(NULL, &t, &t, &c->p);
    for (size_t i = 0; !err && i < w; i++) c->base[i] = lc_int_mod_u32(&t, rods[i]);
    if (err) { lc_int_clear(&MA); lc_int_clear(&t); return err; }
    /* square and multiply on the rods, most significant bit first */
    memcpy(c->acc, c->one, w * sizeof *c->acc);
    long nb = (long)lc_int_bitlen(e);
    for (long i = nb - 1; i >= 0; i--) {
        rmont_mul(c, c->acc, c->acc, c->acc);
        if (testbit(e, (size_t)i)) rmont_mul(c, c->acc, c->acc, c->base);
    }
    /* leave the Montgomery form: multiply by 1 */
    for (size_t i = 0; i < w; i++) c->t1[i] = 1 % rods[i];
    rmont_mul(c, c->acc, c->acc, c->t1);
    /* output: read back on the rods used (value < (k+1) p) and reduce mod p */
    lc_abacus *ab = c->ab;
    size_t *idx = malloc(w * sizeof *idx);
    if (!idx) { lc_int_clear(&MA); lc_int_clear(&t); return LC_ENOMEM; }
    for (size_t i = 0; i < w; i++) idx[i] = i;
    lc_abacus *v = lc_abacus_view(ab, idx, w, &err);
    free(idx);
    if (!err) err = lc_abacus_decode(v, res, c->acc);
    if (!err) err = lc_int_edivmod(NULL, res, res, &c->p);
    lc_abacus_release(v);
    lc_int_clear(&MA); lc_int_clear(&t);
    return err;
}
