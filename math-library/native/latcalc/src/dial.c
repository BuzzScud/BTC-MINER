/* latcalc -- modular dial arithmetic. */
#include "latcalc/dial.h"

uint64_t lc_gcd_u64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

uint32_t lc_mulmod_u32(uint32_t a, uint32_t b, uint32_t N) { return N ? (uint32_t)(((uint64_t)a * b) % N) : 0; }

uint32_t lc_powmod_u32(uint32_t a, uint64_t e, uint32_t N)
{
    if (N == 0) return 0;
    uint64_t r = 1 % N, b = a % N;
    while (e) { if (e & 1) r = r * b % N; b = b * b % N; e >>= 1; }
    return (uint32_t)r;
}

uint32_t lc_dial_poly(const int64_t *coef, size_t deg, uint32_t x, uint32_t N)
{
    uint64_t acc = 0;
    if (N == 0) return 0;
    for (size_t i = deg + 1; i-- > 0;) {
        int64_t c = coef[i] % (int64_t)N;
        if (c < 0) c += N;
        acc = (acc * x + (uint64_t)c) % N;
    }
    return (uint32_t)acc;
}

int lc_dial_chords(const int64_t *coef, size_t deg, uint32_t N, uint32_t *out)
{
    if (N == 0) return LC_EDOMAIN;
    for (uint32_t x = 0; x < N; x++) out[x] = lc_dial_poly(coef, deg, x, N);
    return LC_OK;
}

uint64_t lc_dial_star_cycles(uint64_t N, uint64_t k) { return N ? lc_gcd_u64(N, k % N) : k; }

uint64_t lc_dial_order(uint32_t a, uint32_t N)
{
    if (N == 1) return 1;
    if (N == 0 || lc_gcd_u64(a, N) != 1) return 0;
    uint64_t x = a % N, k = 1;
    while (x != 1) { x = x * a % N; k++; }
    return k;
}

size_t lc_dial_sqrt_one(uint32_t N, uint32_t *out, size_t cap)
{
    size_t n = 0;
    for (uint32_t x = 0; x < N; x++)
        if (((uint64_t)x * x) % N == 1 % N) { if (n < cap) out[n] = x; n++; }
    return n;
}

int lc_dial_is_symmetry(uint32_t m, uint32_t N) { return lc_gcd_u64(m, N) == 1; }
