/* Order splitting.  Lean model: LatticeCalc/Verified/OrderSplit.lean (see ordersplit.h). */
#include "latcalc/ordersplit.h"
#include <math.h>

#define TRY(e) do { int rc_ = (e); if (rc_ < 0) { ret = rc_; goto done; } } while (0)

/* check: g = gcd(x + n - 1, n); 1 if 1 < g < n. */
static int check(lc_int *g, const lc_int *n, const lc_int *x, lc_int *tmp)
{
    int rc;
    if ((rc = lc_int_add(tmp, x, n)) < 0) return rc;
    if ((rc = lc_int_add_i64(tmp, tmp, -1)) < 0) return rc;
    if ((rc = lc_int_gcd(g, tmp, n)) < 0) return rc;
    return lc_int_cmp_i64(g, 1) > 0 && lc_int_cmp(g, n) < 0;
}

int lc_int_order_split(lc_int *g, const lc_int *n, const lc_int *a, const lc_int *E,
                       const uint32_t *rs, size_t nrs, size_t *steps)
{
    if (!g || !n || !a || !E || (nrs && !rs)) return LC_EINVAL;
    if (lc_int_sign(n) <= 0 || lc_int_sign(E) < 0) return LC_EDOMAIN;
    int ret = 0;
    size_t count = 0;
    lc_int m, x, rr, tmp, q;
    lc_int_init(&m); lc_int_init(&x); lc_int_init(&rr); lc_int_init(&tmp); lc_int_init(&q);
    for (size_t i = 0; i < nrs && ret == 0; i++) {
        uint32_t r = rs[i];
        if (r < 2) { ret = LC_EDOMAIN; goto done; }
        /* strip: E = r^v * m, r does not divide m */
        TRY(lc_int_copy(&m, E));
        unsigned long v = 0;
        for (;;) {
            uint32_t rem;
            if (lc_int_is_zero(&m)) break;
            TRY(lc_int_divmod_u32(&q, &rem, &m, r));
            if (rem != 0) break;
            lc_int_swap(&m, &q);
            v++;
        }
        TRY(lc_int_set_u64(&rr, r));
        TRY(lc_int_powmod(&x, a, &m, n));          /* x = a^m mod n */
        for (unsigned long t = 0; t <= v; t++) {  /* scan */
            count++;
            int c = check(g, n, &x, &tmp);
            if (c < 0) { ret = c; goto done; }
            if (c) { ret = 1; goto done; }
            if (t < v) TRY(lc_int_powmod(&x, &x, &rr, n));
        }
    }
done:
    if (steps) *steps = count;
    lc_int_clear(&m); lc_int_clear(&x); lc_int_clear(&rr); lc_int_clear(&tmp); lc_int_clear(&q);
    return ret;
}

int lc_int_qtok(lc_int *g, lc_int *h, lc_int *k, const lc_int *n, const lc_int *a,
                const lc_int *E, const uint32_t *rs, size_t nrs, size_t *steps)
{
    if (!h || !k) return LC_EINVAL;
    int ret = lc_int_order_split(g, n, a, E, rs, nrs, steps);
    if (ret != 1) return ret;
    lc_int g1, h1;
    lc_int_init(&g1); lc_int_init(&h1);
    TRY(lc_int_divexact(h, n, g));
    TRY(lc_int_add_i64(&g1, g, -1));
    TRY(lc_int_add_i64(&h1, h, -1));
    TRY(lc_int_lcm(k, &g1, &h1));
    ret = 1;
done:
    lc_int_clear(&g1); lc_int_clear(&h1);
    return ret;
}

int lc_int_check_lucas_pow(const lc_int *p, const lc_int *a, const uint32_t *qs,
                           const unsigned long *es, size_t nq)
{
    if (!p || !a || (nq && (!qs || !es))) return LC_EINVAL;
    if (lc_int_cmp_i64(p, 1) <= 0) return 0;
    int ret = 0;
    lc_int pm1, prod, t, e, x;
    lc_int_init(&pm1); lc_int_init(&prod); lc_int_init(&t); lc_int_init(&e); lc_int_init(&x);
    TRY(lc_int_add_i64(&pm1, p, -1));
    TRY(lc_int_set_u64(&prod, 1));
    for (size_t i = 0; i < nq; i++) {
        TRY(lc_int_ui_pow_ui(&t, qs[i], es[i]));
        TRY(lc_int_mul(&prod, &prod, &t));
    }
    if (lc_int_cmp(&prod, &pm1) != 0) goto done;
    /* Shared base: with Q = product of the distinct q_i (all with e_i >= 1), every exponent
       (p-1)/q_i is a multiple of d = (p-1)/Q, so ONE full-size power x = a^d gives
       a^(p-1) = x^Q and a^((p-1)/q_i) = x^(Q/q_i) with tiny exponents.  Same answers as the
       direct test, about (nq + 1) times cheaper for large p. */
    {
        int shared = 1;
        TRY(lc_int_set_u64(&prod, 1));                 /* prod := Q */
        for (size_t i = 0; i < nq && shared; i++) {
            int dup = 0;
            for (size_t j = 0; j < i; j++) if (qs[j] == qs[i]) dup = 1;
            if (es[i] == 0 || qs[i] < 2) shared = 0;
            else if (!dup) TRY(lc_int_mul_i64(&prod, &prod, (int64_t)qs[i]));
        }
        if (shared) {
            lc_int d, y, E; lc_int_init(&d); lc_int_init(&y); lc_int_init(&E);
            int rc = lc_int_divexact(&d, &pm1, &prod);
            if (!rc) rc = lc_int_powmod(&x, a, &d, p);          /* x = a^((p-1)/Q) */
            if (!rc) rc = lc_int_powmod(&y, &x, &prod, p);      /* a^(p-1) = x^Q */
            int ok = !rc && lc_int_is_one(&y);
            for (size_t i = 0; ok && i < nq; i++) {
                uint32_t r;
                rc = lc_int_divmod_u32(&E, &r, &prod, qs[i]);  /* Q / q_i */
                if (!rc) rc = lc_int_powmod(&y, &x, &E, p);
                if (rc || lc_int_is_one(&y)) ok = 0;
            }
            lc_int_clear(&d); lc_int_clear(&y); lc_int_clear(&E);
            if (rc < 0) { ret = rc; goto done; }
            if (!ok) goto done;
            ret = 1;
            goto done;
        }
    }
    TRY(lc_int_powmod(&x, a, &pm1, p));
    if (!lc_int_is_one(&x)) goto done;
    for (size_t i = 0; i < nq; i++) {
        uint32_t r;
        TRY(lc_int_divmod_u32(&e, &r, &pm1, qs[i]));
        TRY(lc_int_powmod(&x, a, &e, p));
        if (lc_int_is_one(&x)) goto done;
    }
    ret = 1;
done:
    lc_int_clear(&pm1); lc_int_clear(&prod); lc_int_clear(&t); lc_int_clear(&e);
    lc_int_clear(&x);
    return ret;
}

static int qt_sieve(const lc_int *p, lc_int *q)
{
    static const uint32_t sp[] = {7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
                                  71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137};
    for (size_t i = 0; i < sizeof sp / sizeof sp[0]; i++) {
        uint32_t r;
        if (lc_int_divmod_u32(q, &r, p, sp[i]) < 0) return -1;
        if (r == 0) return 0;
    }
    return 1;
}

long lc_int_qtower_prime(lc_int *p, unsigned long bits, unsigned long start, unsigned long e[3],
                         unsigned long *witness)
{
    static const uint32_t R3[3] = {2, 3, 5};
    if (!p || !e || !witness) return LC_EINVAL;
    if (bits < 16 || bits > (1UL << 28)) return LC_EDOMAIN;
    long ret = LC_EDOMAIN;
    lc_int a, t, q;
    lc_int_init(&a); lc_int_init(&t); lc_int_init(&q);
    for (unsigned long s = start;; s++) {
        unsigned long b = (s * 7919UL) % (bits / 3), c = (s * 104729UL) % (bits / 5);
        double used = (double)b * log2(3.0) + (double)c * log2(5.0);
        if (used + 1 >= (double)bits) continue;
        unsigned long ea = bits - 1 - (unsigned long)used;
        if (lc_int_ui_pow_ui(p, 2, ea) < 0 || lc_int_ui_pow_ui(&t, 3, b) < 0 ||
            lc_int_mul(p, p, &t) < 0 || lc_int_ui_pow_ui(&t, 5, c) < 0 ||
            lc_int_mul(p, p, &t) < 0 || lc_int_add_i64(p, p, 1) < 0) { ret = LC_ENOMEM; break; }
        if (lc_int_bitlen(p) != bits) continue;
        int sv = qt_sieve(p, &q);
        if (sv < 0) { ret = LC_ENOMEM; break; }
        if (!sv || lc_int_is_probable_prime(p, 2) != 1) continue;
        unsigned long es[3] = {ea, b, c};
        int found = 0;
        for (unsigned long w = 2; w < 1000 && !found; w++) {
            lc_int_set_u64(&a, w);
            if (lc_int_check_lucas_pow(p, &a, R3, es, 3) == 1) {
                e[0] = ea; e[1] = b; e[2] = c; *witness = w; found = 1;
            }
        }
        if (found) { ret = (long)s; break; }
    }
    lc_int_clear(&a); lc_int_clear(&t); lc_int_clear(&q);
    return ret;
}

long lc_int_find_lucas_witness(const lc_int *p, const uint32_t *qs, const unsigned long *es,
                               size_t nq, long wmax)
{
    if (!p || !qs || !es || wmax < 3) return LC_EINVAL;
    lc_int a; lc_int_init(&a);
    long found = 0;
    for (long w = 2; w < wmax && !found; w++) {
        int rc = lc_int_set_i64(&a, w);
        if (rc != LC_OK) { lc_int_clear(&a); return rc; }
        rc = lc_int_check_lucas_pow(p, &a, qs, es, nq);
        if (rc < 0) { lc_int_clear(&a); return rc; }
        if (rc == 1) found = w;
    }
    lc_int_clear(&a);
    return found;
}
