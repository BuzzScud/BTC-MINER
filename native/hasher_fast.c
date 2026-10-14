/*
 * hasher_fast.c — High-performance Bitcoin double-SHA256 batch nonce scanner.
 *
 * Uses ARM SHA-256 hardware intrinsics (NEON Crypto Extensions) available on
 * Apple M1/M2/M3 and other ARMv8.2+ processors with the SHA-2 extension.
 *
 * Key optimization: midstate.  The Bitcoin block header is 80 bytes.
 * SHA-256 processes data in 64-byte blocks.  The first 64 bytes of the header
 * (version + prev_hash + first 28 bytes of merkle_root) do NOT change when
 * only the nonce (bytes 76-79) is varied.  We pre-compute the SHA-256
 * internal state after processing the first 64-byte block ("midstate") once,
 * then each nonce needs the inner tail block and the outer digest block:
 * two compression calls instead of three (an ideal 1.5x compression-count gain).
 *
 * Build:
 *   clang -O3 -march=native -shared -fPIC -o libhasher_fast.dylib hasher_fast.c
 */

#include <stdint.h>
#include <string.h>

#ifdef __aarch64__
#include <arm_neon.h>
#endif

/* SHA-256 round constants */
static const uint32_t K256[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
};

static const uint32_t SHA256_INIT[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
};

/* --------------------------------------------------------------------------
 * Portable (non-NEON) SHA-256 implementation — used as fallback
 * -------------------------------------------------------------------------- */

static inline uint32_t rotr32(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));
}

static inline uint32_t be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
           ((uint32_t)p[2] << 8)  | (uint32_t)p[3];
}

static inline void put_be32(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)(v >> 24);
    p[1] = (uint8_t)(v >> 16);
    p[2] = (uint8_t)(v >>  8);
    p[3] = (uint8_t)(v);
}

static void sha256_compress_portable(uint32_t state[8], const uint8_t block[64]) {
    uint32_t W[64];
    for (int i = 0; i < 16; i++)
        W[i] = be32(block + 4 * i);
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr32(W[i-15], 7) ^ rotr32(W[i-15], 18) ^ (W[i-15] >> 3);
        uint32_t s1 = rotr32(W[i-2], 17) ^ rotr32(W[i-2], 19) ^ (W[i-2] >> 10);
        W[i] = W[i-16] + s0 + W[i-7] + s1;
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + S1 + ch + K256[i] + W[i];
        uint32_t S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

/* --------------------------------------------------------------------------
 * ARM NEON SHA-256 implementation using hardware crypto extensions
 * -------------------------------------------------------------------------- */

#ifdef __aarch64__

static void sha256_compress_arm(uint32_t state[8], const uint8_t block[64]) {
    uint32x4_t ABCD_save, EFGH_save;
    uint32x4_t ABCD, EFGH, TMP0, TMP1, TMP2;
    uint32x4_t MSG0, MSG1, MSG2, MSG3;

    ABCD = vld1q_u32(&state[0]);
    EFGH = vld1q_u32(&state[4]);

    ABCD_save = ABCD;
    EFGH_save = EFGH;

    MSG0 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block +  0)));
    MSG1 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block + 16)));
    MSG2 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block + 32)));
    MSG3 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block + 48)));

    /* Rounds 0-3 */
    TMP0 = vaddq_u32(MSG0, vld1q_u32(&K256[0]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG0 = vsha256su0q_u32(MSG0, MSG1);

    /* Rounds 4-7 */
    TMP1 = vaddq_u32(MSG1, vld1q_u32(&K256[4]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG0 = vsha256su1q_u32(MSG0, MSG2, MSG3);
    MSG1 = vsha256su0q_u32(MSG1, MSG2);

    /* Rounds 8-11 */
    TMP0 = vaddq_u32(MSG2, vld1q_u32(&K256[8]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG1 = vsha256su1q_u32(MSG1, MSG3, MSG0);
    MSG2 = vsha256su0q_u32(MSG2, MSG3);

    /* Rounds 12-15 */
    TMP1 = vaddq_u32(MSG3, vld1q_u32(&K256[12]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG2 = vsha256su1q_u32(MSG2, MSG0, MSG1);
    MSG3 = vsha256su0q_u32(MSG3, MSG0);

    /* Rounds 16-19 */
    TMP0 = vaddq_u32(MSG0, vld1q_u32(&K256[16]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG3 = vsha256su1q_u32(MSG3, MSG1, MSG2);
    MSG0 = vsha256su0q_u32(MSG0, MSG1);

    /* Rounds 20-23 */
    TMP1 = vaddq_u32(MSG1, vld1q_u32(&K256[20]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG0 = vsha256su1q_u32(MSG0, MSG2, MSG3);
    MSG1 = vsha256su0q_u32(MSG1, MSG2);

    /* Rounds 24-27 */
    TMP0 = vaddq_u32(MSG2, vld1q_u32(&K256[24]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG1 = vsha256su1q_u32(MSG1, MSG3, MSG0);
    MSG2 = vsha256su0q_u32(MSG2, MSG3);

    /* Rounds 28-31 */
    TMP1 = vaddq_u32(MSG3, vld1q_u32(&K256[28]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG2 = vsha256su1q_u32(MSG2, MSG0, MSG1);
    MSG3 = vsha256su0q_u32(MSG3, MSG0);

    /* Rounds 32-35 */
    TMP0 = vaddq_u32(MSG0, vld1q_u32(&K256[32]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG3 = vsha256su1q_u32(MSG3, MSG1, MSG2);
    MSG0 = vsha256su0q_u32(MSG0, MSG1);

    /* Rounds 36-39 */
    TMP1 = vaddq_u32(MSG1, vld1q_u32(&K256[36]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG0 = vsha256su1q_u32(MSG0, MSG2, MSG3);
    MSG1 = vsha256su0q_u32(MSG1, MSG2);

    /* Rounds 40-43 */
    TMP0 = vaddq_u32(MSG2, vld1q_u32(&K256[40]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG1 = vsha256su1q_u32(MSG1, MSG3, MSG0);
    MSG2 = vsha256su0q_u32(MSG2, MSG3);

    /* Rounds 44-47 */
    TMP1 = vaddq_u32(MSG3, vld1q_u32(&K256[44]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);
    MSG2 = vsha256su1q_u32(MSG2, MSG0, MSG1);
    MSG3 = vsha256su0q_u32(MSG3, MSG0);

    /* Rounds 48-51 */
    TMP0 = vaddq_u32(MSG0, vld1q_u32(&K256[48]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);
    MSG3 = vsha256su1q_u32(MSG3, MSG1, MSG2);

    /* Rounds 52-55 */
    TMP1 = vaddq_u32(MSG1, vld1q_u32(&K256[52]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);

    /* Rounds 56-59 */
    TMP0 = vaddq_u32(MSG2, vld1q_u32(&K256[56]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP0);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP0);

    /* Rounds 60-63 */
    TMP1 = vaddq_u32(MSG3, vld1q_u32(&K256[60]));
    TMP2 = ABCD;
    ABCD = vsha256hq_u32(ABCD, EFGH, TMP1);
    EFGH = vsha256h2q_u32(EFGH, TMP2, TMP1);

    ABCD = vaddq_u32(ABCD, ABCD_save);
    EFGH = vaddq_u32(EFGH, EFGH_save);

    vst1q_u32(&state[0], ABCD);
    vst1q_u32(&state[4], EFGH);
}

#endif /* __aarch64__ */

/* Dispatch to ARM or portable */
static inline void sha256_compress(uint32_t state[8], const uint8_t block[64]) {
#ifdef __aarch64__
    sha256_compress_arm(state, block);
#else
    sha256_compress_portable(state, block);
#endif
}

/* --------------------------------------------------------------------------
 * Full SHA-256 for an arbitrary-length message (used for the outer hash)
 * -------------------------------------------------------------------------- */

static void sha256_full(const uint8_t *msg, size_t len, uint8_t out[32]) {
    uint32_t state[8];
    memcpy(state, SHA256_INIT, 32);

    size_t blocks = len / 64;
    for (size_t i = 0; i < blocks; i++)
        sha256_compress(state, msg + i * 64);

    /* Final block with padding */
    uint8_t pad[128];
    size_t rem = len % 64;
    memcpy(pad, msg + blocks * 64, rem);
    pad[rem] = 0x80;
    memset(pad + rem + 1, 0, 128 - rem - 1);

    size_t pad_blocks;
    if (rem < 56) {
        uint64_t bitlen = (uint64_t)len * 8;
        put_be32(pad + 56, (uint32_t)(bitlen >> 32));
        put_be32(pad + 60, (uint32_t)(bitlen));
        pad_blocks = 1;
    } else {
        uint64_t bitlen = (uint64_t)len * 8;
        put_be32(pad + 120, (uint32_t)(bitlen >> 32));
        put_be32(pad + 124, (uint32_t)(bitlen));
        pad_blocks = 2;
    }

    for (size_t i = 0; i < pad_blocks; i++)
        sha256_compress(state, pad + i * 64);

    for (int i = 0; i < 8; i++)
        put_be32(out + 4 * i, state[i]);
}

/* --------------------------------------------------------------------------
 * Bitcoin double-SHA256 with midstate optimization
 *
 * Header layout (80 bytes, all little-endian):
 *   [0..3]   version
 *   [4..35]  prev_block_hash
 *   [36..67] merkle_root
 *   [68..71] time
 *   [72..75] bits
 *   [76..79] nonce  <-- only this changes per candidate
 *
 * First SHA-256 block (bytes 0-63): version + prev_hash + first 28 of merkle
 * Second SHA-256 block: last 4 of merkle + time + bits + nonce + padding
 *   (16 data bytes + 1 byte 0x80 + 47 zero bytes + 8 byte length = 64 bytes)
 *
 * Midstate = SHA-256 internal state after processing block 0.
 * For each nonce, copy midstate, process block 1 (with nonce patched),
 * then SHA-256 the 32-byte result (outer hash).
 * -------------------------------------------------------------------------- */

/* Pre-build the padded second block template (bytes 64-79 of header + SHA padding).
 * Nonce at offset 12 in this 64-byte block (byte 76 - 64 = 12). */
static void build_tail_block(uint8_t tail[64], const uint8_t header[80]) {
    memset(tail, 0, 64);
    memcpy(tail, header + 64, 16);       /* last 4 merkle + time + bits + nonce */
    tail[16] = 0x80;                      /* SHA-256 padding bit */
    /* Length of 80-byte message in bits = 640 = 0x280, big-endian at offset 62 */
    tail[62] = 0x02;
    tail[63] = 0x80;
}

/* Pre-build the outer hash block: SHA-256 of a 32-byte inner hash.
 * 32 data bytes + 0x80 + 23 zero bytes + 8 byte length = 64 bytes. */
static void build_outer_pad(uint8_t outer[64], const uint8_t inner_hash[32]) {
    memset(outer, 0, 64);
    memcpy(outer, inner_hash, 32);
    outer[32] = 0x80;
    /* Length = 256 bits = 0x100, big-endian at offset 62 */
    outer[62] = 0x01;
    outer[63] = 0x00;
}

/* --------------------------------------------------------------------------
 * Public API: batch nonce scanning
 * -------------------------------------------------------------------------- */

/*
 * scan_nonces_batch: Scan a contiguous range [start_nonce, start_nonce+count)
 * for a nonce whose double-SHA256 hash is <= target (little-endian).
 *
 * Returns 1 if found (writes to *winning_nonce), 0 if exhausted.
 *
 * target is 32 bytes little-endian (same byte order as Bitcoin hash comparison).
 */
int scan_nonces_batch(
    const uint8_t header_template[80],
    const uint8_t target[32],
    uint32_t start_nonce,
    uint32_t count,
    uint32_t *winning_nonce
) {
    /* Compute midstate from the first 64 bytes */
    uint32_t midstate[8];
    memcpy(midstate, SHA256_INIT, 32);
    sha256_compress(midstate, header_template);

    /* Build the tail block template */
    uint8_t tail[64];
    build_tail_block(tail, header_template);

    for (uint32_t i = 0; i < count; i++) {
        uint32_t nonce = start_nonce + i;

        /* Patch nonce into tail block at offset 12 (little-endian) */
        tail[12] = (uint8_t)(nonce);
        tail[13] = (uint8_t)(nonce >> 8);
        tail[14] = (uint8_t)(nonce >> 16);
        tail[15] = (uint8_t)(nonce >> 24);

        /* Inner SHA-256: midstate + tail block */
        uint32_t inner_state[8];
        memcpy(inner_state, midstate, 32);
        sha256_compress(inner_state, tail);

        /* Convert inner state to bytes (big-endian per SHA-256 spec) */
        uint8_t inner_hash[32];
        for (int j = 0; j < 8; j++)
            put_be32(inner_hash + 4 * j, inner_state[j]);

        /* Outer SHA-256: hash of the 32-byte inner hash */
        uint8_t outer_block[64];
        build_outer_pad(outer_block, inner_hash);

        uint32_t outer_state[8];
        memcpy(outer_state, SHA256_INIT, 32);
        sha256_compress(outer_state, outer_block);

        uint8_t final_hash[32];
        for (int j = 0; j < 8; j++)
            put_be32(final_hash + 4 * j, outer_state[j]);

        /* Target comparison (LE 256-bit integers).
         * Python: int.from_bytes(hash_bytes, 'little') <= target
         * Both final_hash and target are raw byte arrays where the MSB of
         * the LE integer is at index 31.  Compare from MSB (index 31) down. */
        int found = 1;
        for (int j = 31; j >= 0; j--) {
            uint8_t h_byte = final_hash[j];
            uint8_t t_byte = target[j];
            if (h_byte < t_byte) {
                found = 1;
                break;
            }
            if (h_byte > t_byte) {
                found = 0;
                break;
            }
        }

        if (found) {
            *winning_nonce = nonce;
            return 1;
        }
    }

    return 0;
}

/*
 * scan_nonces_list: Scan a list of specific nonce values (thesis candidates).
 * Same semantics as scan_nonces_batch but takes an array of nonces instead of
 * a contiguous range.
 */
int scan_nonces_list(
    const uint8_t header_template[80],
    const uint8_t target[32],
    const uint32_t *nonce_list,
    uint32_t list_len,
    uint32_t *winning_nonce
) {
    uint32_t midstate[8];
    memcpy(midstate, SHA256_INIT, 32);
    sha256_compress(midstate, header_template);

    uint8_t tail[64];
    build_tail_block(tail, header_template);

    for (uint32_t i = 0; i < list_len; i++) {
        uint32_t nonce = nonce_list[i];

        tail[12] = (uint8_t)(nonce);
        tail[13] = (uint8_t)(nonce >> 8);
        tail[14] = (uint8_t)(nonce >> 16);
        tail[15] = (uint8_t)(nonce >> 24);

        uint32_t inner_state[8];
        memcpy(inner_state, midstate, 32);
        sha256_compress(inner_state, tail);

        uint8_t inner_hash[32];
        for (int j = 0; j < 8; j++)
            put_be32(inner_hash + 4 * j, inner_state[j]);

        uint8_t outer_block[64];
        build_outer_pad(outer_block, inner_hash);

        uint32_t outer_state[8];
        memcpy(outer_state, SHA256_INIT, 32);
        sha256_compress(outer_state, outer_block);

        uint8_t final_hash[32];
        for (int j = 0; j < 8; j++)
            put_be32(final_hash + 4 * j, outer_state[j]);

        int found = 1;
        for (int j = 31; j >= 0; j--) {
            uint8_t h_byte = final_hash[j];
            uint8_t t_byte = target[j];
            if (h_byte < t_byte) { found = 1; break; }
            if (h_byte > t_byte) { found = 0; break; }
        }

        if (found) {
            *winning_nonce = nonce;
            return 1;
        }
    }

    return 0;
}

/*
 * double_sha256: Compute Bitcoin double-SHA256 of an 80-byte header.
 * Used for correctness verification from Python.
 */
void double_sha256(const uint8_t data[80], uint8_t out[32]) {
    uint8_t inner[32];
    sha256_full(data, 80, inner);
    sha256_full(inner, 32, out);
}

/*
 * probe: Simple probe function to verify the library loaded correctly.
 * Returns 1 always.
 */
int hasher_fast_probe(void) {
    return 1;
}

/* Preserve the Python THESIS2 tile order while filling a bounded uint32 buffer.
 * cursor counts raw tile positions, including skipped entries in the partial
 * final tile.  uint64 arithmetic prevents nonce wraparound at 2^32. */
/* Reproject a job into an already allocated resident table. The field/step
 * permutations remain loaded across jobs; SHA256d arithmetic is unchanged. */
void fill_traversal_offsets(const uint16_t *residues, uint32_t phase,
                           uint32_t cell_phase, uint32_t prime, uint32_t *out) {
    for (uint32_t i=0;i<400;++i) {
        /* Descriptor primes span uint32; reduce after the exact product. */
        const uint32_t base=360*((cell_phase+(uint64_t)i*prime)%400)+phase;
        for (uint32_t k=0;k<360;++k)
            out[i*360+k]=(base+residues[k])%144000;
    }
}

uint32_t fill_nonce_batch(const uint32_t *offsets, uint32_t width,
                          uint32_t first_tile, uint64_t *cursor,
                          uint32_t capacity, uint32_t *out) {
    if (!width || !capacity) return 0;
    const uint64_t nonce_space = UINT64_C(1) << 32;
    const uint64_t tiles = (nonce_space + width - 1) / width;
    const uint64_t end = tiles * width;
    uint64_t position = *cursor;
    uint32_t filled = 0;
    while (position < end && filled < capacity) {
        const uint64_t turn = position / width;
        const uint64_t tile = (first_tile + turn) % tiles;
        const uint64_t base = tile * width;
        uint32_t index = (uint32_t)(position % width);
        while (index < width && filled < capacity) {
            const uint64_t nonce = base + offsets[index++];
            ++position;
            if (nonce < nonce_space) out[filled++] = (uint32_t)nonce;
        }
    }
    *cursor = position;
    return filled;
}

/* Evaluate the exact offset descriptor without a 144000-entry table. The
 * labels are a checked permutation of 0..359 for either field or flower order.
 * All raw positions are visited, including skipped out-of-uint32 positions in
 * the one partial tile. The cursor never wraps after the final raw position. */
uint32_t fill_factored_nonce_batch(const uint16_t *labels, uint32_t phase,
                                  uint32_t cell_phase, uint32_t prime,
                                  uint32_t first_tile, uint64_t *cursor,
                                  uint32_t capacity, uint32_t *out) {
    const uint64_t width=144000, tiles=29827, end=width*tiles;
    const uint64_t nonce_space=UINT64_C(1)<<32;
    if (!capacity || phase>=width || cell_phase>=400 || first_tile>=tiles) return 0;
    uint64_t position=*cursor;
    uint32_t filled=0;
    while (position<end && filled<capacity) {
        const uint64_t turn=position/width;
        const uint64_t base=((first_tile+turn)%tiles)*width;
        uint32_t index=(uint32_t)(position%width);
        while (index<width && filled<capacity) {
            const uint32_t cell=index/360;
            uint32_t k=index%360;
            /* Scale-graph cell level: 400=2^4*5^2. Each rod is evaluated
             * independently; 225 and 176 are its exact CRT weights. */
            const uint64_t cell_formula=cell_phase+(uint64_t)cell*prime;
            const uint32_t cell_value=(225*(cell_formula%16)+176*(cell_formula%25))%400;
            const uint32_t cell_base=360*cell_value+phase;
            while (k<360 && filled<capacity) {
                /* Deep level (8,2,3): 256*9*125=288000 exceeds the
                 * unwrapped formula bound 287998. Project to (7,2,3),
                 * then read the canonical residue modulo 144000. */
                const uint32_t label=labels[k++];
                const uint32_t r2=((cell_base%256)+(label%256))%256;
                const uint32_t r3=((cell_base%9)+(label%9))%9;
                const uint32_t r5=((cell_base%125)+(label%125))%125;
                const uint32_t offset=(122625*(r2%128)+64000*r3+101376*r5)%144000;
                ++position; ++index;
                const uint64_t nonce=base+offset;
                if (nonce<nonce_space) out[filled++]=(uint32_t)nonce;
            }
        }
    }
    *cursor=position;
    return filled;
}

/* Diagnostic selection does not change which nonces the scanner attempts. */
uint32_t select_sample_nonces(const uint32_t *nonces, uint32_t count,
                              uint32_t step, uint32_t *out) {
    if (!step) return 0;
    uint32_t selected = 0;
    for (uint32_t i = 0; i < count; ++i) {
        if (nonces[i] % step == 0) out[selected++] = nonces[i];
    }
    return selected;
}
