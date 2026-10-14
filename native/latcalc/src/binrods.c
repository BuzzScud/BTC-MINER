/* latcalc -- binary (Mersenne) rods and the universal twelve-dial 65520 = 2^4 (2^12 - 1). */
#include "latcalc/binrods.h"

uint64_t lc_mersenne_mod(uint64_t x, unsigned w)
{
    if (w == 0 || w > 63) return 0;
    uint64_t mask = ((uint64_t)1 << w) - 1;
    while (x > mask) x = (x & mask) + (x >> w);      /* 2^w = 1 on this rod */
    return x == mask ? 0 : x;
}

uint64_t lc_rotl(uint64_t x, unsigned w)
{
    if (w == 0 || w > 63) return 0;
    uint64_t mask = ((uint64_t)1 << w) - 1;
    x &= mask;
    return ((x << 1) & mask) | (x >> (w - 1));
}

void lc_dial12_split(uint32_t x, uint32_t *lo4, uint32_t *r12)
{
    *lo4 = x & 15u;
    *r12 = (uint32_t)lc_mersenne_mod(x, 12);
}

uint32_t lc_dial12_join(uint32_t lo4, uint32_t r12)
{
    return r12 + 4095u * ((r12 + 16u - lo4) & 15u);  /* 4095 = -1 mod 16 */
}

uint32_t lc_dial12_mul(uint32_t a, uint32_t b)
{
    return (uint32_t)(((uint64_t)(a % LC_DIAL12) * (b % LC_DIAL12)) % LC_DIAL12);
}

uint32_t lc_dial12_pow(uint32_t a, uint64_t e)
{
    uint32_t r = 1, b = a % LC_DIAL12;
    while (e) { if (e & 1) r = lc_dial12_mul(r, b); b = lc_dial12_mul(b, b); e >>= 1; }
    return r;
}

uint32_t lc_dial12_inv(uint32_t a)
{
    uint32_t x = a % LC_DIAL12;
    /* gcd(x, 65520) = 1 iff x is odd and prime to 3, 5, 7, 13 */
    if (!(x & 1) || x % 3 == 0 || x % 5 == 0 || x % 7 == 0 || x % 13 == 0) return 0;
    return lc_dial12_pow(x, 11);
}
