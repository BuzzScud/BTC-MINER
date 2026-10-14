/*
 * Rod sieves: excluding powers b^j along the orbit of a 2x2 integer matrix.  See rodsieve.h.
 */
#include <stdlib.h>
#include <string.h>
#include "latcalc/rodsieve.h"
#include "latcalc/rns.h"
#include "latcalc/common.h"

typedef struct { uint64_t a[2][2]; } mat2;

static uint64_t md(int64_t x, uint64_t m) { int64_t r = x % (int64_t)m; return (uint64_t)(r < 0 ? r + (int64_t)m : r); }
static uint64_t mulm(uint64_t x, uint64_t y, uint64_t m) { return (x % m) * (y % m) % m; }  /* m < 2^32 */

static mat2 matmul(mat2 X, mat2 Y, uint64_t m)
{
    mat2 R;
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++)
        R.a[i][j] = (mulm(X.a[i][0], Y.a[0][j], m) + mulm(X.a[i][1], Y.a[1][j], m)) % m;
    return R;
}

static mat2 matpow(const int64_t F[2][2], uint64_t n, uint64_t m)
{
    mat2 B, R;
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { B.a[i][j] = md(F[i][j], m); R.a[i][j] = (i == j) % m; }
    while (n) { if (n & 1) R = matmul(R, B, m); B = matmul(B, B, m); n >>= 1; }
    return R;
}

static int is_identity(mat2 X, uint64_t m) { return X.a[0][0] == 1 % m && X.a[1][1] == 1 % m && X.a[0][1] == 0 && X.a[1][0] == 0; }

static int isprime32(uint32_t n)
{
    if (n < 2) return 0;
    for (uint32_t d = 2; (uint64_t)d * d <= n; d++) if (n % d == 0) return 0;
    return 1;
}

static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

/* z_r mod m for one start */
static uint64_t zmod(const int64_t F[2][2], const int64_t s[2], int coord, uint64_t r, uint64_t m)
{
    uint64_t v0 = md(s[0], m), v1 = md(s[1], m);
    for (uint64_t k = 0; k < r; k++) {
        uint64_t n0 = (mulm(md(F[0][0], m), v0, m) + mulm(md(F[0][1], m), v1, m)) % m;
        uint64_t n1 = (mulm(md(F[1][0], m), v0, m) + mulm(md(F[1][1], m), v1, m)) % m;
        v0 = n0; v1 = n1;
    }
    return coord ? v1 : v0;
}

/* per-rod discrete log table of b */
typedef struct { uint32_t p, ord; int32_t *lg; } rodlog;

static int rodlog_init(rodlog *R, uint32_t p, uint32_t b)
{
    R->p = p; R->lg = malloc(sizeof(int32_t) * p);
    if (!R->lg) return LC_ENOMEM;
    for (uint32_t i = 0; i < p; i++) R->lg[i] = -1;
    uint64_t x = 1; uint32_t j = 0;
    do { R->lg[x] = (int32_t)j; x = x * b % p; j++; } while (x != 1);
    R->ord = j;
    return LC_OK;
}

/* is there j with j = lg_i (mod ord_i) for all chosen rods? (CRT compatibility) */
static int class_survives(const rodlog *R, const uint64_t *z, size_t n)
{
    uint64_t r = 0, M = 1;
    for (size_t i = 0; i < n; i++) {
        int32_t l = R[i].lg[z[i]];
        if (l < 0) return 0;
        uint64_t o = R[i].ord, g = gcd64(M, o);
        uint64_t a = (uint64_t)l;
        if ((a % g + g - r % g) % g != 0) return 0;
        /* combine x = r (mod M), x = a (mod o) */
        uint64_t Mg = M / g, og = o / g, t = 0;
        if (og > 1) {
            /* t = ((a - r)/g) * inv(Mg) mod og */
            int64_t diff = (int64_t)((a % o + o - r % o) % o) / (int64_t)g;
            int64_t x0 = 0, x1 = 1, a0 = (int64_t)og, a1 = (int64_t)(Mg % og);
            while (a1) { int64_t q = a0 / a1, tt = a0 - q * a1; a0 = a1; a1 = tt; tt = x0 - q * x1; x0 = x1; x1 = tt; }
            int64_t inv = ((x0 % (int64_t)og) + (int64_t)og) % (int64_t)og;
            t = (uint64_t)(((diff % (int64_t)og) * inv) % (int64_t)og);
        }
        uint64_t Ml = Mg * o;
        r = (r + M * t) % Ml; M = Ml;
        if (M > ((uint64_t)1 << 40)) return 1;   /* treat as surviving: too large to decide */
    }
    return 1;
}

int lc_rodsieve_find(lc_rodsieve_cert *cert, const int64_t F[2][2], const int64_t (*starts)[2],
                     size_t nstarts, int coord, uint32_t b, uint32_t e,
                     uint32_t Lmult_max, uint32_t pmax, uint64_t Qmax)
{
    if (!cert || !F || !starts || nstarts == 0 || (coord != 0 && coord != 1) || !isprime32(b) || e == 0)
        return LC_EINVAL;
    uint64_t bpow = 1;
    for (uint32_t i = 0; i < e; i++) { bpow *= b; if (bpow > 0xffffffffu) return LC_EINVAL; }
    /* period of F on the b^e rod */
    uint64_t L0 = 0;
    {
        mat2 X; for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) X.a[i][j] = (i == j) % bpow;
        mat2 B; for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) B.a[i][j] = md(F[i][j], bpow);
        for (uint64_t t = 1; t <= 4 * bpow * bpow + 8; t++) { X = matmul(X, B, bpow); if (is_identity(X, bpow)) { L0 = t; break; } }
        if (!L0) return LC_EDOMAIN;
    }
    for (uint32_t mult = 1; mult <= Lmult_max; mult++) {
        uint64_t L = L0 * mult;
        if (L > 100000) break;
        /* classes (start, r) with z_r = 0 on the b^e rod */
        size_t ncls = 0;
        uint32_t *cs = malloc(sizeof(uint32_t) * nstarts * L), *cr = malloc(sizeof(uint32_t) * nstarts * L);
        if (!cs || !cr) { free(cs); free(cr); return LC_ENOMEM; }
        for (size_t s = 0; s < nstarts; s++)
            for (uint64_t r = 0; r < L; r++)
                if (zmod(F, starts[s], coord, r, bpow) == 0) { cs[ncls] = (uint32_t)s; cr[ncls] = (uint32_t)r; ncls++; }
        if (ncls == 0) {
            memset(cert, 0, sizeof *cert);
            cert->b = b; cert->e = e; cert->bpow = (uint32_t)bpow; cert->L = (uint32_t)L; cert->Q = 1;
            free(cs); free(cr); return LC_OK;
        }
        rodlog R[LC_RODSIEVE_MAXRODS]; size_t nr = 0; uint64_t Q = 1;
        uint64_t *zv = malloc(sizeof(uint64_t) * ncls * LC_RODSIEVE_MAXRODS);
        if (!zv) { free(cs); free(cr); return LC_ENOMEM; }
        int done = 0;
        for (uint32_t p = 3; p <= pmax && !done && nr < LC_RODSIEVE_MAXRODS; p += 2) {
            if (p == b || !isprime32(p)) continue;
            if (!is_identity(matpow(F, L, p), p)) continue;
            rodlog cand;
            if (rodlog_init(&cand, p, b % p) != LC_OK) { free(cs); free(cr); free(zv); return LC_ENOMEM; }
            uint64_t Qn = Q / gcd64(Q, cand.ord) * cand.ord;
            if (Qn > Qmax) { free(cand.lg); continue; }
            R[nr] = cand;
            for (size_t c = 0; c < ncls; c++) zv[c * LC_RODSIEVE_MAXRODS + nr] = zmod(F, starts[cs[c]], coord, cr[c], p);
            nr++; Q = Qn;
            size_t surv = 0;
            for (size_t c = 0; c < ncls; c++) surv += (size_t)class_survives(R, &zv[c * LC_RODSIEVE_MAXRODS], nr);
            if (surv == 0) done = 1;
        }
        if (done) {
            memset(cert, 0, sizeof *cert);
            cert->b = b; cert->e = e; cert->bpow = (uint32_t)bpow; cert->L = (uint32_t)L; cert->Q = Q;
            cert->nrods = nr;
            for (size_t i = 0; i < nr; i++) cert->rods[i] = R[i].p;
        }
        for (size_t i = 0; i < nr; i++) free(R[i].lg);
        free(cs); free(cr); free(zv);
        if (done) return LC_OK;
    }
    return LC_EDOMAIN;
}

int lc_rodsieve_modulus(lc_int *M, const lc_rodsieve_cert *cert)
{
    int rc = lc_int_set_i64(M, cert->bpow);
    for (size_t i = 0; i < cert->nrods && rc == LC_OK; i++) rc = lc_int_mul_i64(M, M, cert->rods[i]);
    return rc;
}

int lc_rodsieve_verify(const lc_rodsieve_cert *cert, const int64_t F[2][2],
                       const int64_t (*starts)[2], size_t nstarts, int coord)
{
    if (!cert || !F || !starts || !nstarts || (coord != 0 && coord != 1) ||
        cert->nrods > LC_RODSIEVE_MAXRODS || cert->b < 2 ||
        cert->e == 0 || cert->e > 31 || cert->L == 0 || cert->Q == 0)
        return LC_EINVAL;
    uint64_t expected_bpow = 1;
    for (uint32_t i = 0; i < cert->e; i++) {
        expected_bpow *= cert->b;
        if (expected_bpow > UINT32_MAX) return LC_EINVAL;
    }
    if (expected_bpow != cert->bpow) return LC_EINVAL;
    /* Bounds protect the embedded verifier, independently of its Python API. */
    if (nstarts > 64 || cert->L > 10000 || cert->Q > 10000 ||
        (uint64_t)nstarts * cert->L * cert->Q > 2000000) return LC_EINVAL;
    for (size_t i = 0; i < cert->nrods; i++) {
        if (cert->rods[i] < 2 || gcd64(cert->bpow, cert->rods[i]) != 1)
            return LC_EINVAL;
        for (size_t j = 0; j < i; j++)
            if (gcd64(cert->rods[i], cert->rods[j]) != 1) return LC_EINVAL;
    }
    int ok = 1, rc;
    lc_int M, Mp, t, e2, one, a[2][2], x[2][2], u, v, nv, w, y, z;
    lc_int_init(&M); lc_int_init(&Mp); lc_int_init(&t); lc_int_init(&e2); lc_int_init(&one);
    lc_int_init(&u); lc_int_init(&v); lc_int_init(&nv); lc_int_init(&w); lc_int_init(&y); lc_int_init(&z);
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { lc_int_init(&a[i][j]); lc_int_init(&x[i][j]); }
    lc_rodsieve_modulus(&M, cert);
    lc_int_set_i64(&Mp, 1);
    for (size_t i = 0; i < cert->nrods; i++) lc_int_mul_i64(&Mp, &Mp, cert->rods[i]);
    /* (a) F^L = I mod M, by square-and-multiply on big integers */
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { lc_int_set_i64(&a[i][j], F[i][j]); lc_int_set_i64(&x[i][j], i == j); }
    for (uint64_t n = cert->L; n; n >>= 1) {
        lc_int tmp[2][2];
        for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) lc_int_init(&tmp[i][j]);
        if (n & 1) {
            for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) {
                lc_int_mul(&u, &x[i][0], &a[0][j]); lc_int_mul(&v, &x[i][1], &a[1][j]);
                lc_int_add(&u, &u, &v); lc_int_fdivmod(NULL, &tmp[i][j], &u, &M);
            }
            for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) lc_int_copy(&x[i][j], &tmp[i][j]);
        }
        for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) {
            lc_int_mul(&u, &a[i][0], &a[0][j]); lc_int_mul(&v, &a[i][1], &a[1][j]);
            lc_int_add(&u, &u, &v); lc_int_fdivmod(NULL, &tmp[i][j], &u, &M);
        }
        for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { lc_int_copy(&a[i][j], &tmp[i][j]); lc_int_clear(&tmp[i][j]); }
    }
    lc_int_fdivmod(NULL, &u, &x[0][0], &M); lc_int_fdivmod(NULL, &v, &x[1][1], &M);
    lc_int_set_i64(&t, 1); lc_int_fdivmod(NULL, &t, &t, &M);
    if (lc_int_cmp(&u, &t) || lc_int_cmp(&v, &t)) ok = 0;
    lc_int_fdivmod(NULL, &u, &x[0][1], &M); lc_int_fdivmod(NULL, &v, &x[1][0], &M);
    if (!lc_int_is_zero(&u) || !lc_int_is_zero(&v)) ok = 0;
    /* (b) b^Q = 1 mod M' */
    lc_int_set_i64(&t, cert->b); lc_int_set_u64(&e2, cert->Q);
    lc_int_set_i64(&one, 1); lc_int_fdivmod(NULL, &one, &one, &Mp);
    lc_int_powmod(&u, &t, &e2, &Mp);
    if (lc_int_cmp(&u, &one)) ok = 0;
    /* (c) read z_r on the rod abacus and compare with the powers of b */
    uint32_t mods[LC_RODSIEVE_MAXRODS + 1]; size_t nm = 0;
    mods[nm++] = cert->bpow;
    for (size_t i = 0; i < cert->nrods; i++) mods[nm++] = cert->rods[i];
    lc_rns ab;
    rc = lc_rns_init(&ab, mods, nm);
    if (rc != LC_OK) ok = 0;
    uint32_t res[LC_RODSIEVE_MAXRODS + 1], pw[LC_RODSIEVE_MAXRODS + 1];
    for (size_t s = 0; s < nstarts && ok; s++) {
        lc_int_set_i64(&y, starts[s][0]); lc_int_set_i64(&z, starts[s][1]);
        for (uint32_t r = 0; r < cert->L && ok; r++) {
            lc_int_fdivmod(NULL, &w, coord ? &z : &y, &M);
            lc_rns_encode(&ab, res, &w);
            if (res[0] == 0) {
                for (size_t i = 1; i < nm; i++) pw[i] = 1 % mods[i];
                for (uint64_t j = 0; j < cert->Q && ok; j++) {
                    int same = 1;
                    for (size_t i = 1; i < nm && same; i++) if (pw[i] != res[i]) same = 0;
                    if (same) ok = 0;
                    for (size_t i = 1; i < nm; i++) pw[i] = (uint32_t)((uint64_t)pw[i] * cert->b % mods[i]);
                }
            }
            /* step: (y, z) <- F (y, z), kept reduced mod M */
            lc_int_mul_i64(&u, &y, F[0][0]); lc_int_mul_i64(&v, &z, F[0][1]); lc_int_add(&nv, &u, &v);
            lc_int_mul_i64(&u, &y, F[1][0]); lc_int_mul_i64(&v, &z, F[1][1]); lc_int_add(&w, &u, &v);
            lc_int_fdivmod(NULL, &y, &nv, &M); lc_int_fdivmod(NULL, &z, &w, &M);
        }
    }
    if (rc == LC_OK) lc_rns_clear(&ab);
    lc_int_clear(&M); lc_int_clear(&Mp); lc_int_clear(&t); lc_int_clear(&e2); lc_int_clear(&one);
    lc_int_clear(&u); lc_int_clear(&v); lc_int_clear(&nv); lc_int_clear(&w); lc_int_clear(&y); lc_int_clear(&z);
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { lc_int_clear(&a[i][j]); lc_int_clear(&x[i][j]); }
    return ok;
}
