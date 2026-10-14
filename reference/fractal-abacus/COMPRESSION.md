# COMPRESSION: what the rod abacus can and cannot compress

Status: working reference, v3 2026-10-11 (v1 sections 0-13, round-2 atlas in Part II, sections 14-22, round-3 additions and corrections in Part III, sections 23-24). Requested explicitly by the owner (overrides the no-new-md default).
Scope: compression-relevant facts about the coprime-rod (RNS) abacus, the fractal rod tower and its partitions, scale, the residue geometry (flowers, hex shells, conics and spheres over Z/p^j, dials), the `Thesis/math/` library design, the TCMP codec, the variant documents, and the deterministic coding recipes that the geometry formulas give.

Contents. Part I: 0 how to read, 1 the hard limit, 2 objects, 3 two zooms, 4 scale theory, 5 what compresses, 6 TCMP, 7 related maths, 8 variant documents, 9 candidate designs, 10 open problems and experiments, 11 corrections, 12 sources, 13 review status. Part II: 14 residue geometry (the unifying picture), 15 formula atlas, 16 deterministic coding recipes, 17 fractal partition atlas, 18 constants and variables, 19 `Thesis/math/` design map, 20 measured evidence, 21 what the geometry does and does not buy, 22 review status. Part III (round 3): 23 additional formulas by branch of mathematics (23.1 p-adic and unit groups, 23.2 characters, Gauss, Kloosterman, Ramanujan sums, 23.3 FFT and NTT, 23.4 sparse recovery and coprime sampling, 23.5 lattice combinatorics, tilings, Apollonian, walks, 23.6 divisor-lattice enumerations, 23.7 ultrametric, odometer, functional graphs, 23.8 error-control codes, Gray codes, 23.9 information and complexity, 23.10 prime distribution and entropy, 23.11 packing densities and other items), 24 round-3 ledger, Lean verification table, and open items.

Paths are relative to the workspace root `/home/logan/AI_Projects/` unless they start with `AR/`.
`AR/` = `Aristotle/ingest/api_v3/9b854e2d-2ae1-4d55-9b53-bf308b5e3648/extracted_result/output-final_aristotle/`.

## 0. How to read this file

Every claim carries one evidence tag. Nothing without a tag should be trusted.

| Tag | Meaning |
| --- | --- |
| `[PROVED name @file]` | Lean theorem exists with that name. Re-check with the proof build before relying on it. |
| `[VERIFIED]` | Recomputed independently with a throwaway Python/sympy run on 2026-10-11. |
| `[MEASURED log/script]` | Output of a probe or benchmark. Logs under `/tmp` are ephemeral; rerun the named script. |
| `[DERIVED]` | Follows by elementary argument from tagged facts; not separately machine-checked. |
| `[CLAIMED-UNMEASURED]` | Stated in a document; no benchmark, proof, or run backs it. |
| `[OPEN]` | Stated open in the thesis or unresolved here. |
| `[REFUTED]` | Shown false; see section 11. |
| `[DESIGN]` | Proposal. Not built, not measured. |

Governing rules inherited from the thesis: honesty ledger `Thesis/MASTER_PLAN.md:92-95`, authority sources `:96-101`, forbidden patterns FP-1..FP-11, "verify before use" (FP-10).

## 1. The one hard limit

No lossless code shortens every input. `[PROVED no_universal_compression @Thesis/proofs/ThesisProofs/ThesisProofs/BG087CoprimeBranchingTrie.lean]`: there is no injection `Fin (2^n) -> Fin (2^k)` for `k < n`. That lemma covers fixed-length outputs. The variable-length form follows by the same count: only `2^n - 1` strings are shorter than `n` bits, so no injection from the `2^n` n-bit strings into them exists `[DERIVED]`.

Consequences used throughout this file:

1. A residue column is a bijective re-coding of an integer. It adds no information and removes none. `[PROVED BG086CarrierResidueBijection.lean]`, `[PROVED decode_unique @BG087]`. Information content is neutral; stored size is not: residues kept as `ceil(log2 m_i)` bits each cost `sum ceil(log2 m_i) >= log2 M` bits, so padding waste appears unless residues are bit-packed (31-bit rods carrying 30 payload bits give 31/30).
2. So any size gain comes only from three sources: (a) redundancy in the data, (b) a description shorter than the data (generators, formulas), or (c) restricting to a sparse set of values and numbering just that set.
3. Mean output length on uniform n-bit input depends on the code class `[VERIFIED by exhaustive/greedy check for small n, independent reviewer]`:
   - one-to-one (non-singular) codes whose output length is conveyed out of band (e.g. by file size): mean at least `n - 2 + (n+2)/2^n` bits, tight (geofs batch1_information);
   - prefix-free or uniquely decodable codes: mean at least `n` bits (Kraft), tight with fixed length;
   - for any one-to-one code, the fraction of n-bit strings mapped to at most `n-k` bits is below `2^(1-k)`, so typical strings are incompressible by more than a few bits.
   TCMP is one-to-one (length comes from the container) and adds a fixed 24 B header, so random input expands slightly: measured 1.00002x for the best path `[MEASURED geofs auto 1 MiB random: 1048600 B = 1 MiB + 24 B]`.
   The roughly 2 bits of slack in the one-to-one bound are paid for by the out-of-band length; counting the length as information removes it.
4. The RNS contribution is therefore operational (cost of arithmetic, carry-free parallelism, exact precision growth), not a source of entropy savings. Any document that claims RNS itself compresses text is making a (b) or (c) claim in disguise and must be judged as one.

## 2. Objects (what the abacus is)

- A **frame** is an immutable set of pairwise-coprime moduli (rods) `m_i < 2^31`, at most `TM_ROD_MAX = 4096` `[Thesis/math/include/rods/tm_rods.h:41]`. A **column** is the residue vector. Capacity `M = prod m_i`, `capacity_bits = floor(log2 M)`.
- Capacity numbers `[VERIFIED]`: the 4096 largest primes below 2^31 give `log2 M = 126975.878` bits; the largest 3226 give `100005.924` bits. Matches `MASTER_PLAN.md:43`.
- Arithmetic (`+`, `-`, `*`) is independent per rod: carry-free. Read-back (Garner mixed radix) costs `R(R-1)/2` mulmods, `[VERIFIED]` 8,386,560 for R = 4096 and 5,201,925 for R = 3226. Read-back exists only at the I/O boundary and in the oracle.
- Cost classes: `RLOCAL_O1`, `RLOCAL_OLOGN`, `FRAME_OR`, `BOUNDARY_OR2`, `ORACLE_POSITIONAL`. Sign, order, equality-to-threshold, gcd and primality need read-back; no column-local sign decider exists `[OPEN, stated in FractalAbacus notes; GT-005 at Thesis/THESIS.md:1440-1456]`.
- Redundant rods (RRNS) detect or correct faults: with `k` information rods and `r` redundant rods, minimum distance is `r+1` iff every k-subset product of moduli is at least the data range `M_data` (the product of the information moduli) `[DERIVED, geofs batch3_algebra_coding]`. Here `M` elsewhere in this file means the product of all moduli; the two differ when redundant rods exist. Shenoy-Kumaresan base extension costs `3k+2` mulmods against Garner's `k(k-1)/2`: by count the break-even is `k` about 7.5 (21 vs 23 at k = 7, 28 vs 26 at k = 8); measured timings put it nearer 6 `[MEASURED geofs: k=8 18 us vs 55 us; k=64 73 us vs 7584 us]`. `[PROVED RodMont @AR LatticeCalc/Verified]`.

## 3. The two different "zooms" (key distinction)

The repository uses "fractal" and "scale" for two operations that behave differently. Mixing them is the main conceptual trap for compression design.

| | Modulus zoom (tower / Hensel / b-adic) | Magnitude zoom (scale / radix point) |
| --- | --- | --- |
| Data | `x mod b^k`, i.e. the low `k` base-`b` digits | `raw / S` with `S = 19^k` or `60^k`; high digits first |
| Deepening | `k -> k+1` adds one digit; capacity `x b` | exponent grows; addition stays exact |
| Ring structure | `x -> x mod b^k` is a ring homomorphism: `+`, `*` commute with projection | no single `S` is closed under `*` (exact iff `S` divides `raw_x * raw_y`); the union over all levels, `Z[1/30]` for base 60, is a ring and `(raw,k)*(raw',k') = (raw*raw', k+k')` is exact |
| Refinement of the value | refines in the b-adic metric only (not the real metric); also recovers exact rationals `a/c` with `c` coprime to `b` | yes (real approximation) |
| Compression-relevant use | lossless addressing, progressive decode of residues, exact big arithmetic | fixed-point scaling, exact rational ladders, base-60 exponent digits |

Facts:

- Modulus zoom `[PROVED @Thesis/proofs/ThesisProofs/ThesisProofs/BG088FractalRodTower.lean]`: `tower_proj`, `tower_digit` (one level down adds exactly one digit), `tower_fibre` (b children per node), `tower_injective`, `tower_scale` (multiplying by `b^s` prepends `s` zero digits), `mixed_tower_unique` (coprime towers combine), `capacity_deepen_one`, `minimal_depth` (`x < b^(log_b x + 1)`), `zoom60_deepens` (the base-60 zoom is one deepening of all three rods 2, 3, 5).
- Same statements on the library naturals: `FractalAbacus.lean` `proj`, `enc_proj`, `run_proj`, `runProg_proj` (numbers, computations and programs are self-similar across levels), `capacity_deepen`, `card_fibre`, `readBack_enc_eventually`, `arbitrary_precision`, `fraction_eq_eventually` `[PROVED @AR LatticeCalc/Verified/FractalAbacus.lean, 363 lines; verified by grep: structure L110, level L120, proj L129, enc_proj L137, capacity_deepen L195, readBack_enc_eventually L218, arbitrary_precision L231, fraction_eq_eventually L299, card_fibre L320]`.
- Hensel lifting `[PROVED FlowerFractal.lean, SphereHensel.lean @AR; hypotheses not re-read here]`: for a hypersurface in `d` variables at a nonsingular point (gradient nonzero mod `p`), each solution mod `p^(j+1)` lifts to exactly `p^(d-1)` solutions mod `p^(j+2)`, so the count mod `p^(j+1)` is `p^((d-1)j)` times the count mod `p` (the Lean `card_fiber` states the per-rod case); 3-sphere count mod `p^(j+1)` is `p^(3j) * p(p^2-1)`; `orderOf_lift` (period is kept or multiplied by `p`). Exception: `p = 3` on hex rods carries `2 * 3^k`. The nonsingularity hypothesis matters: for `x^2+y^2=1` at `p = 2` the counts mod 2, 4, 8, 16 are 2, 8, 16, 32, not a clean lift `[VERIFIED by reviewer]`.
  `[VERIFIED]` brute force: `x^2+y^2=1` has 8 / 56 solutions mod 7 / 49 and 12 / 132 mod 11 / 121 (predicted `p+1`, `p(p+1)`). Hex form `x^2-xy+y^2=1` has 6 / 42 mod 7 / 49 and 18 / 342 mod 19 / 361.
- A depth-`k` residue identifies `x` only when `x < b^k`; the tower therefore gives no size saving over positional notation `[PROVED minimal_depth]`. What it buys is: exact precision growth without re-encoding, and nested-residue prefixes (`[PROVED nested_residue @BG087]`: a coarser modulus residue is a function of the finer one).
- Completions behind the two zooms `[DERIVED, standard]`: the modulus zoom is the inverse limit of `Z/b^k`, the b-adic ring `Z_b = prod_{p | b} Z_p` (not a field; zero divisors when `b` has two or more prime factors). The magnitude zoom is the colimit `Z[1/30]` inside the reals. `Z[1/30]` is a subring of `Q`, so it sits in every `Q_p`; the exact statements are `Z[1/30]` lies in `Z_p` iff `p` does not divide 30, and `Z[1/30]` is dense in `R`, `Q_2`, `Q_3`, `Q_5` and a discrete cocompact lattice in `R x Q_2 x Q_3 x Q_5` with fundamental domain `[0,1) x Z_2 x Z_3 x Z_5` (S-integers, strong approximation) `[STANDARD]`. That joint picture is the precise form of "the two zooms": the magnitude zoom and the modulus zoom are two coordinates of one adelic object, and no single digit string refines both absolute values. A fixed frame is a finite quotient `Z/M`; deepening and adding rods both move toward the profinite integers. By CRT, `Z/60^d` is three rods `Z/2^(2d) x Z/3^d x Z/5^d`, which is why `zoom60_deepens` deepens three rods. Nested rods `b^k` are not coprime: digit extraction on a tower is division by `b^k`, not Garner mixing.
- Limits `[OPEN]`: no `p^k` rods in the C library (a rod `b^d >= 2^31` is not one machine word; growth is by merging new coprime rods, MASTER_PLAN 5.5 `:590-599`); no modulus at or above `2^31`; no depth vectors; no byte-to-column serialization; no prefix chains; no generic formula evaluator; tower ops absent on the C side (B04c). The universal fractal architecture is open `[OPEN GT-007; bounded recursive kernel PROVED @GT007RecursivePrimeFractal.lean]`.

## 4. Scale theory (19, 361, 60)

`[PROVED @AR Scale361.lean, SCALING_19, FlowerGeneral, Flower19, Base60]` unless noted.

- `Scaled S` stores `raw/S`. Addition is always exact. Multiplication is exact iff `S | raw_x * raw_y`.
- With `S = 361 = 19^2` only denominators `{1, 19, 361}` appear. No fixed `S > 1` is closed under multiplication, so the exponent must grow: `19^k` for the hex flower, `60^k` for base 60.
- `361 = 1 mod m` iff `m | 360`. 19 is the least `n > 1` with `n^2 = 1 mod 360`. There are 16 square roots of 1 mod 360 `[VERIFIED]`: 1, 19, 71, 89, 91, 109, 161, 179, 181, 199, 251, 269, 271, 289, 341, 359. Pell: `19^2 - 360 * 1^2 = 1` `[VERIFIED]`; it is the degenerate case `360 = 6^2 * 10`, i.e. the unit `19 + 6*sqrt(10)` of `Z[sqrt 10]` with `z = 6y`, nothing specific to 360 beyond that `[VERIFIED by reviewer]`.
- Orders of 19 `[VERIFIED]`: mod 360 is 2, mod 7200 is 40, mod 144000 is 800. This matches `19^k = 1 mod T <=> (T/180) divides k`, valid when `360 | T` and `T` is 5-smooth (lifting the exponent for even `k`: `v2(19^k - 1) = 2 + v2(k)` [general form `v2(a^k - 1) = v2(a-1) + v2(a+1) + v2(k) - 1`; the earlier `3 + v2(k)` was wrong, it gives 4 at `k = 2` where `v2(360) = 3`], `v3 = 2 + v3(k)`, `v5 = 1 + v5(k)`; `[VERIFIED(py)]` 99 values of `k`); mod 144000 it needs `k` divisible by 800. Counterexample outside that class: `T = 2520` has order 6 (since `19 = 5 mod 7`), not `T/180 = 14` `[VERIFIED by reviewer]`.
- `pi = 5 + 2*omega` has Eisenstein norm 19; `pi^2 = 21 + 16*omega` scales squared lengths by 361.
- Flower tiling: every `z = d + beta_k * w` with `beta_k = (2k+1) + k*omega`, `N_k = 3k^2 + 3k + 1`. Unique base-`beta_k` addresses; `N_k^n` copies at depth `n`. All prime factors of `N_k` are `1 mod 3` `[VERIFIED k < 2000]`. `N_k` is a power-of-two-minus-one only for `k = 0, 1, 6` i.e. 1, 7, 127 `[VERIFIED k < 100000]`.
- Fractal partition F1..F5: rings refine iff `k | m`; shared spokes `gcd`; `Omega(60) = 4`, `Omega(360) = 6`, `Omega(7200) = 9`, `Omega(144000) = 12` `[VERIFIED]`; 360 has 60 maximal refinement chains; `phi(360 * 60^k) = 96 * 60^k` `[VERIFIED k <= 3]`, open fraction `4/15` (`phi(30)/30 = 8/30`); 7 breaks the pattern: `phi(2520) = 576`, fraction `8/35` `[VERIFIED]`.
- SIC (variant 4) says "scale invariance" but its body uses base-60 exponent digits and exact ratios `p/q`; it does not use `Scale361`, `19^k` or the golden angle `[CLAIMED-UNMEASURED]`, see section 8.

Compression reading `[DERIVED]`: scale theory tells you which fixed-point denominators stay exact (`60^k` finite iff the denominator is 5-smooth). A value whose denominator is 5-smooth costs `(numerator bits, exponent)`; otherwise it needs a rational pair or a larger frame. This is a number-format statement, not an entropy reduction.

## 5. Where real compression can come from (ranked by evidence)

### 5.1 Redundancy in bytes (conventional) `[MEASURED]`
TCMP's transforms (RLE, LZ77, LZBLK, delta+RLE) do the work. Details in section 6. Measured on `Thesis/web/frontend/tcmp.js`:

| Input | `smallest` mode | `auto` (CRT carrier) | Source |
| --- | --- | --- | --- |
| zeros 20 KB | 332 B (0.017) | 8040 B (0.402) | tcmp scaling ladder |
| `tcmp.js` 33 KB | 12594 B (0.371) | 40726 B (1.201) | tcmp-smallest-parity |
| geofs 1 MiB text / JSON / repeated 64 B / zeros | 0.4086 / 0.1797 / 0.02298 / 0.01541 | n/a | geofs auto path |
| devops 8 MiB text | ratio 0.394; compress 2.4 s (3.5 MB/s); decompress 125 ms (67 MB/s) | n/a | devops run |
| random 1 MiB | 1048600 B (1.00002) | n/a | geofs |

Reading: the CRT carrier loses to transforms-only on every measured case; it expands text by 1.2x. `[MEASURED]`

### 5.2 Closed-form descriptors (description beats data)
`Thesis/MASTER_PLAN.md:2262-2310` (section 19.3) defines descriptors for sequences whose value at index `n` is computed from parameters:

- ARITH `S = n*a + d*n(n-1)/2`; GEOM `a(r^n-1)/(r-1)`; FAULHABER sums for powers (header allows `p <= 14`: `Thesis/math/include/rods/tm_rod_series.h:27`; MASTER_PLAN text says `p <= 4`: inconsistent, see section 11); POLY; LINREC `s_N = C^N s_0` (header `d <= 16` at `tm_rods.h:201`; MASTER_PLAN says `d <= 8`; clib `abacus.c:268` says 8: inconsistent); PROD_GEOM `r^(n(n+1)/2)`; MATPOW.
- Jump cost `O(log n)` rod operations by repeated squaring `[PROVED RodJump: powSq_eq, soddy_state]`.
- Affine blocks have one-step residue rules `a + (i+1)d mod p` and period dividing `p` (exactly `p` when `p` does not divide `d`; period 1 when it does), so one period plus `(a, d)` is the whole residue stream `[PROVED affine_residue_step, affine_residue_period @BG087; the exact-period caveat is DERIVED]`.
- Probe `Thesis/web/scripts/tcmp-formula-point-probe.mjs`: all-zero 4 KB -> 5 B, all-zero 100 KB -> 6 B, random 4 KB -> 100.075% of input `[MEASURED]`. This is exactly the Kolmogorov picture: structured input collapses to parameters; random input does not and pays a small header.

Value: strongest and most honest use of the abacus for compression: store parameters, evaluate on demand, jump in `O(log n)`. Limit: only inputs that fit a descriptor family compress; recognizing the family is a search problem outside the abacus `[OPEN]`. Formally, a descriptor gives only an upper bound on Kolmogorov complexity `K(x)` (not computable, only upper-semicomputable); most `n`-bit strings have `K(x) >= n - c` (at least `2^n - 2^(n-c) + 1` strings), and the invariance theorem says the machine-dependent constant does not depend on `x` `[DERIVED, standard]`. Lossless descriptors for noisy data need an explicit integer residual stream; the gain is then `H(residual)` against `H(data)` and can be negative.

### 5.3 Sparse sets of structured integers `[DERIVED]`
If an integer lies in a sparse, enumerable set `S`, `log2 |S ∩ [0, N)|` bits suffice. Rod-native examples:

- 5-smooth numbers (orders of the clock dials). `[VERIFIED by reviewer, exact counts including 1]`:

  | k | #5-smooth <= 2^k | rank-code bits (ceil log2) | fixed-width (a,b,c) | raw |
  | --- | --- | --- | --- | --- |
  | 32 | 1,849 | 11 (10.85) | 15 | 32 |
  | 64 | 13,283 | 14 (13.70) | 18 | 64 |
  | 128 | 100,527 | 17 (16.62) | 21 | 128 |
  | 1024 | 48,977,637 | 26 (25.55) | 30 | 1024 |

  The leading term `k^3 / (6 log2(3) log2(5))` (about `k^3/22.08`) underestimates by 19.7% at k = 32 (1484.0 vs 1849), 10.6% at k = 64, 5.5% at k = 128 and 0.7% at k = 1024 `[VERIFIED(py)]`; the table counts are exact. The saving holds only if the input is promised to be 5-smooth; a stream that mixes smooth and non-smooth values pays at least a 1-bit tag per value. Source of the structure: SMOOTH_SPLIT, and `[PROVED ChainCertificates.lean: layers are 5-smooth, not highly composite]`.
- Single prime powers `p^e`: a prime index plus an exponent.
- Mersenne rods `2^a - 1`: `gcd(2^a-1, 2^b-1) = 2^gcd(a,b)-1`, doubling is a rotation with order `lcm`; the 360 dial fits on 255, 511, 31 (22 bits), the 144000 dial on 128, 9, 125 (262 bits) `[VERIFIED by reviewer: gcds 1, lcm(8,9,5)=360 and lcm(128,9,125)=144000]`.
- Chain primes `18 * 10^k + 1`: for `k < 30` prime at `k = 0, 1, 2, 4, 9, 12, 21` `[VERIFIED]`. Beyond: `k = 55, 307, 332, 388` (below 400), and `820, 1593, 2432, 2438, 3372` `[PROVED ChainCertificates.lean: Lucas test for 5-smooth p-1; 18*10^3372+1 prime]`. A 11,000-bit prime is then described by one integer `k`; the Lucas certificate is needed to verify primality, not to decode.
- Clock primes `p` with `p-1 | 144000`: 38 of them `[VERIFIED]` (includes 2, 3, 5; largest 24001). `[PROVED QCompression.lean @AR RequestProject]`: their 703 pair products admit a lossless 10-bit code and `no_shorter_code` holds. `qK_dvd_144000` is a finite check only.

Limit: this is a code for a set, not a general compressor. It helps only when the data are known to come from that set. `[DERIVED]`

### 5.4 Redundancy engineering (not compression, but size accounting)
- Cell: 8 information rods + 1 redundant rod of 31-bit primes carries 30 B payload in 36 B stored with 4-byte-aligned rods, ratio 36/30 = 1.2 (35 B packed, 1.1667); 8 info rods alone are 32 B aligned (1.0667) `[VERIFIED round 2: 8 rods of 31-bit primes give 247.9999995 bits, so payload is 30 B not 31 B]`; geofs reports the 1.0667 figure for the r = 0 aligned frame `[MEASURED geofs]`. This is expansion by design (fault tolerance); a 25 B input in `auto` became 348 B `[MEASURED smoke]`.
- Byte write behavior: odd rods above 255 change on every write; at most 4 rods stay unchanged `[MEASURED geofs W1-W3]`. Hence "write only the rods that changed" (sparse update) saves little for byte-granular edits.

## 6. TCMP implementation facts (the only built compressor)

Files: `Thesis/web/frontend/tcmp.js`; shared adapter `Thesis/web/shared/coprime-codec.ts`; C: `Thesis/math/include/compat/tm_compression.h` (also `Thesis/math/tm_compression.h`) and `Thesis/math/src/compat/tm_compression.c`.

- Header 24 B: `'TCMP'`, version 1, variant, transform, algorithm, `origLen` u64, FNV-1a-64 (non-standard seed `1469598103934665603`). Worst case is `n + 24` `[MEASURED/DERIVED]`.
- `MAX_INPUT = 1<<30` in the C header; `MASTER_PLAN.md:2910` says the JS codec is capped at 8 MiB. Different caps, not reconciled `[OPEN]`.
- Modes: `auto, network, file, progressive, constellation, fhc, hdc, lbc, sic, otc`.
- Transforms: 0 stored; 1 RLE (literals 1-128, repeats 3-130); 2 LZ77 (32 KiB window, 15-bit hash, min match 4, max 131); 3 LZBLK (64 KiB); 4 delta+RLE.
- CRT payload: 16 B header, flags `PACKED=1, ADAPTIVE_MODSET=2, IMPLICIT_MODSET=4, IMPLICIT_BLOCKLEN=8`; rods up to prime 53; Garner `O(k^2)`.
- `smallest` (transforms only) beats `auto` (carrier) on size in all measured cases.
- Test scripts: `Thesis/web/scripts/` `tcmp-*-probe.mjs`, `tcmp-scaling-ladder`, `tcmp-smallest-parity`, `tcmp-interop-suite`, `tcmp-wire-suite`, `compression-suite`, `coprime-production-suite`.
- Release gate `Thesis/backup/reports/prod_release_gate_status.json` shows PASS (generated 2026-10-11T23:39:58Z). `/tmp/tcmp_interop.log` (386 pass / 120 fail, 10:03) is stale and must not be quoted.
- My probes `[MEASURED]`: whole-integer probe (100 KB zeros -> one integer, `k = 45728`, packed bits 102.7% of N: no gain); fractal-tower probe (zeros 10 KB overhead 0.092-0.096%; 100 KB decode **44.5 s** with naive CRT, needs tree Garner); residue-entropy probe (random: carrier 48 bits, residue 42.75 bits, i.e. the residue is not cheaper to entropy-code, consistent with section 1).
- C bench `c = 8` info rods, 30 B blocks: 130 ns/op (231 MB/s) `[MEASURED]`. Rod Montgomery is about 10x slower than positional `[MASTER_PLAN.md:581]`.

## 7. Related mathematics and where it sits (term -> repo -> status)

| Term | Repo location | Status for compression |
| --- | --- | --- |
| Chinese remainder / RNS | BG006, BG086; MASTER_PLAN 0.2 `:38-57` | `[PROVED]` bijection, size-neutral |
| Garner mixed radix | tm_rods, MASTER_PLAN `:2217` (prefix) | O(R^2); need tree CRT for large R |
| Shenoy-Kumaresan | RodMont; `nt_p2_extension.py:105` | `[PROVED]`; faster read-free base extension |
| Hensel lifting | SphereHensel, FlowerFractal, HYPERDIM_RODS `:165` | `[PROVED]` fibre counts; precision growth |
| Moebius / Ramanujan sums | AR COPRIME_WAVES `:58`, SIGNAL_DIALS `:153` | see below |
| Eisenstein / hex flower | MASTER_PLAN `:604`, GEO-3 `:2302` | tiling addresses `[PROVED]` |
| Descartes/Soddy, Apollonian | MASTER_PLAN `:2306` (`apollonian_mod24`), SODDY_COXETER | companion-matrix jumps `[PROVED RodJump]` |
| Coxeter / Petrie | MASTER_PLAN `:98` (lists SODDY_COXETER.md), AR codex/CODEX.md `:816`; the earlier anchor THESIS `:2797` was not found | structure only |
| Plimpton 322 | AR SCALING_19 `:145`; clib `plimpton322.c` | scale example |
| Good-Thomas / prime-factor FFT | COPRIME_WAVES | `[DERIVED]` no twiddles for coprime sizes |
| Tower collapse | TowerCollapse | `a^(b^c) = a^(b^(c mod F))`; chain 360 -> 12 -> 2 `[PROVED]` |
| Bell numbers | geofs batch (rod split) | number of unordered pairwise-coprime splits of `n` equals `Bell(omega(n))` `[VERIFIED]` for 30, 60, 210, 360: 5, 5, 15, 5 |
| Max coprime sets | geofs | maximum (size `pi(X)`) pairwise-coprime subsets of `[2,X]` are all prime-power sets; their number is `prod floor(log_p X)` `[VERIFIED]` X = 10: 6; X = 20: 8; X = 24: 8. Not the same as maximal under inclusion: X = 10 has 9 maximal sets (sizes 3, 3, 3, 4 x 6) |
| LLL, QAM, harmonic, quasi-crystals, Bravais | variants 2-4 | see section 8; Bravais and Beatty: none in repo |
| Kolmogorov, MDL, residue entropy | none in docs | only my probes (sections 5.2, 6) |

Coprime waves `[PROVED @AR COPRIME_WAVES]`: `c_n(t) = sum_{d | gcd(n,t)} mu(n/d) d`; `c_{mn} = c_m c_n` for coprime `m, n`; zoom `c_{p^{k+1}}(p t) = p c_{p^k}(t)`; `c_n(0) = phi(n)`, `c_n(1) = mu(n)`. A signal that is a sum of Ramanujan sums over coprime moduli would factor across rods; whether real data have such structure is untested `[OPEN]`.

Other facts `[VERIFIED]` in this session: `65520 = 2^4 * 3^2 * 5 * 7 * 13` (120 divisors); `u^12 = 1 mod m` for all `u` coprime to `m` iff `m | 65520`; `65520 = 2^16 - 16`; Leech kissing number `196560 = 3 * 65520`. `lcm(1..7) = 420`, `lcm(1..10) = 2520`; `71^2 - 1 = 5040 = 7!`. Primes below 500 with `p^2 = 1 mod 360`: 19, 71, 89, 109, 179, 181, 199, 251, 269, 271, 359, 379, 431, 449 (14). The count of `n <= 500` with `pi(n) | n` is 16 (2, 4, 6, 8, 27, 30, 33, 96, 100, 120, 330, 335, 340, 350, 355, 360); "exactly 5" is true only when `pi(n)` itself must be prime.

## 8. Variant documents: status

None has a benchmark in the repository. Treat every ratio as `[CLAIMED-UNMEASURED]`.

| Variant | Document(s) | Claim | Judgement |
| --- | --- | --- | --- |
| HDC harmonic decomposition | `HARMONIC_DECOMPOSITION_COMPRESSION_VARIANT2.md` | 35-50% on structured data | Quantizing harmonics is lossy by definition. Its "Theorem 2.4" proof is invalid (reviewer): CRT is exact only for the exact residue vector, a perturbed vector decodes to an unrelated integer, and floating-point `A sin(wt+phi)` is not bit-reproducible. Lossless needs an integer-exact transform (for example an NTT over `F_p` with `p` dividing `q-1` for the needed root of unity) plus a stored integer residual |
| LBC lattice basis | `LATTICE_BASIS_COMPRESSION_VARIANT3.md`, `..._QUICKREF.md` | LLL (delta 0.75, tau 2), 45-70% | Its "Theorem 4.1" is circular (reviewer): it assumes the data lie in a proper integer sublattice, and then coordinates in a basis are unique with no LLL needed. Residues mod different primes do not form a sublattice (CRT is onto). Gain is `log2 det(Lattice)` per vector minus the basis cost; LLL is a unimodular change of basis with unchanged determinant and only shrinks coefficient ranges. Exact relation finding is Hermite/Smith normal form or kernel computation |
| SIC scaling invariant | `SCALING_INVARIANT_COMPRESSION_VARIANT4.md`, `..._QUICK_REFERENCE.md` | `d = s*d'`; power/exponential/geometric/periodic+growth models at R^2 > 0.95; header 10-50 bits | `R^2 > 0.95` leaves 5% variance unexplained; for a Gaussian residual the saving is about `0.5*log2(1/(1-R^2))` bits per sample, 2.16 bits at 0.95, before the header (reviewer). Fits in log space do not measure integer exactness. `d = s*normalize(d/s)` is exact only if `s` divides `d`. Body uses base-60 digits and ratios only; MASTER_PLAN `:2906-2910` records variants 1 and 4 do not compress text |
| META | `META_COMPRESSION_THEORETICAL_ANALYSIS.md` | 7 techniques, Shannon bound 70-110 bits | Bound depends on assumed source |
| CALC synergy | `CALCULATOR_COMPRESSION_SYNERGY_ANALYSIS.md` | harmonic V = 1, Y = 5/4, G = 3/2; 95x projected | Projection only |
| FHC fractal hierarchy | `/tmp/FRACTAL_HIERARCHY_COMPRESSION_FHC.md`, `/tmp/FHC_QUICK_REFERENCE.md` (both exist, dated 2026-10-10, ephemeral; an earlier note here wrongly said they were gone: the file-search tool cannot see `/tmp`, `read_file` with the absolute path can) | primorial hierarchy `P_k` (`P_7 = 9,699,690` is 23.21 bits `[VERIFIED]`, the file's 23.9 is wrong; `P_11 = 7.4T`, 42.75 bits); headline claim 15-40% over flat RNS while another passage says 1.5% | Claims are projections; one table row is wrong; the primorial chain is a divisibility chain, so residues nest (prefix property) but add no entropy gain |
| Five variants | `Thesis/support/generated/COPRIME_COMPRESSION_FIVE_VARIANTS.md` | network, file, progressive (k = 8/16/24/32; M about 9.7M / 614B / 1.22e17 / 4.2e25 with bits 23.9 / 39.2 / 57.0 / 85.0), QAM (lossy under noise), hybrid | Progressive modulus ladders are capacity tables, not compression. The bit counts do not match any prime-product rule: first-k-primes products are 23.21 / 64.82 / 114.19 / 168.49 bits for k = 8 / 16 / 24 / 32 (and 42.75 bits at k = 12) `[VERIFIED round 2]`; the source of the doc's values is unknown |
| Manifolds / unified framework | `COMPRESSION_MANIFOLDS_*.md`, `COMPRESSION_VARIANTS_UNIFIED_FRAMEWORK.md` | Benchmarks-by-Benford at manifold doc `:545` | Unmeasured |

Lean state: `Thesis/proofs/compression_framework.lean` has 9 `sorry`; `Thesis/proofs/compression_variants_formal.lean` has 20 `sorry` occurrences on 18 lines (grep, 2026-10-11; earlier note of 15 was wrong). Lossless claims for the variants are unproved.

## 9. Candidate designs (all `[DESIGN]`, none built)

D1. Descriptor-first container. Header selects `{RAW, TCMP-transform, DESCRIPTOR(family, params), DESCRIPTOR + residual}`; DESCRIPTOR + residual codes `data - descriptor(n)` with the existing transforms. Decision is by exact size comparison (encode all candidates, verify `decode(encode(x)) = x`, keep the smallest, break ties deterministically), so it is lossless if every candidate is a bijection onto its image, and the worst case is `n + c` where `c` is the stored-mode header (24 B in TCMP; information-theoretically about 1 bit for a flag, or `ceil(log2 K)` bits for `K` candidates when lengths come from the container). It cannot beat the counting bounds: on uniform data it gains nothing and pays `c`. Needs a family-recognition step: Berlekamp-Massey gives LINREC order in `O(n^2)` `[DERIVED]`.

D1a. Linear-recurrence detection per rod (standard method): run Berlekamp-Massey mod each prime rod, take the common order `d`, CRT the coefficients and rational-reconstruct them (half-gcd, valid when numerators and denominators are below about `sqrt(M/2)`), then replay all `n` terms to verify. An `n`-term sequence collapses to about `3d` numbers. Falsifier: BM on random data must return order near `n/2`; Fibonacci must return 2 and replay exactly.

D2. Tower-addressed sparse code. For known sparse sets (section 5.3) emit `(set id, index)` where the index is rank in the set. Decoder needs only the enumeration, not the abacus. Value is modest and must be justified per set.

D3. Tree-Garner read-back. Replace `O(R^2)` Garner by subproduct-tree CRT for large `R`; the 44.5 s decode of 100 KB is the measured reason. Needs a tree-shaped frame plan; correctness is the same `decode_unique`.

D4. Depth-vector frame (extension of FractalAbacus to the C library): rods `b_i^{d_i}` with `d` stored in the header, deepening by merging a new coprime prime-power rod rather than widening a word (MASTER_PLAN 5.5). Resolves the `2^31` per-rod cap only when `b^d` fits in 31 bits; beyond that needs multiword rods or new coprime rods.

D5. SK-extended redundant rods for detection only. Add `r` redundant rods, use SK base extension (`3k+2` mulmods) to verify a column without Garner. This is integrity, not size; keep it out of compression ratios.

D6. Scale-aware numeric stream. For streams of fixed-point decimals, store base-60 exponent digits plus numerators; compare against plain delta+RLE on real data before adopting.

D7. Smooth/rough split `x = s * r` with `s` B-smooth by trial division: encode the exponent vector of `s` and the cofactor `r`. Saves about `a - log2(a) - c` bits for `x = 2^a * r`; on uniform random integers the mean length is at least the raw width once the vector length and flag are paid (any gain there would contradict section 1). Standard math; use as a codec is a design proposal.

D8. CRT-separable periodic data. A stream periodic with period `prod p_i` (pairwise coprime) that is additively separable `s(n) = sum f_i(n mod p_i)` is stored as `sum p_i` values minus overlaps instead of `prod p_i` (3*5*7 = 105 becomes 13). Exact test: `f(a,b) - f(a,0) - f(0,b) + f(0,0) = 0` for all `a, b`. Generic periodic data fails it. Good-Thomas index map is standard; the codec use is unmeasured.

Each design needs: (1) a measured baseline against `smallest` mode, (2) a roundtrip property test, (3) a Lean or exhaustive-small check of the bijection, (4) a stated honest failure case.

## 10. Open problems and gaps

1. Compression ratios of variants 2-4, FHC and the manifold documents: no measurements `[OPEN]`.
2. `GT-005` (AP-based prime generation, no O(1) promotion) and `GT-007` (universal fractal architecture) remain open `[OPEN; Thesis/THESIS.md:1440-1456, :1481-1590]`.
3. C library gaps: `p^k` rods, moduli at or above `2^31`, depth vectors, byte-to-column serialization, prefix chains, generic formula evaluator, tower ops (B04c) `[OPEN]`. Capacity is capped below `(2^31)^4096 = 2^126976` (126975.9 bits for the 4096 largest primes).
4. Owner decision D4 (overflow policy: RANGE vs automatic deepening, default RANGE) `[MASTER_PLAN.md:2260]`.
5. Rational reconstruction from rods is not formalized; C library is not linked to Lean.
6. The legacy RNS stack A11 is obsolete (75 symbols, 36 WRONG); do not reuse it.
7. JS cap (8 MiB) vs C cap (1 GiB); tree-Garner for large decode.
8. No test shows that coprime-wave (Ramanujan sum) structure occurs in real data.
9. The FHC files exist in `/tmp` (read with absolute paths; the file-search tool cannot see `/tmp`). Their `P_7` bit count is wrong (23.9 should be 23.21).

### Decisive experiments (all `[DESIGN]`; seeded, offline, each under 5 minutes)

Decision rule: an idea adds value only if it beats `min(TCMP smallest, xz -9e)` on the same bytes with exact round trip, and shows no gain on random and full-rank controls. Python stdlib has `zlib`, `lzma`, `bz2`; `zstandard` is not installed.

| # | Data | Candidate vs baseline | Pass condition | Expected |
| --- | --- | --- | --- | --- |
| E1 Descriptor-first (D1, D1a) | 64-bit streams, n = 10^5: arithmetic progression, cubic polynomial mod 2^64, LINREC d = 4, sum of periodic parts (periods 7, 11, 13) plus 16-bit noise, AP plus +-3 noise, uniform random | D1 vs xz -9e, bz2, TCMP smallest | exact families at most 100 B; noisy families at least 5% below best baseline; random at most `n + 4` B; every round trip hash matches | likely pass for exact families |
| E2 Residue planes | 2 MiB of Python sources and 2 MiB of a binary; 4-byte words split into residues mod (251, 253, 255, 256), one plane per rod | xz on residue planes vs xz raw vs xz on plain byte-plane split | at least 1% below the better control | likely fail (bijection adds no information) |
| E3 Scale / SIC | `361*k` integers; multiples of 1/3600 as CSV; `round(a*n^alpha)` with R^2 about 0.95-0.99 | gcd strip; base-60 numerators plus exponent; fit plus integer residual vs delta+xz | within 5% of `n*log2(s)/8` saving for the first; at least 3% and 5% below control for the others | likely pass for the first two |
| E4 Hex flower walk | 10^6-step walk on the Eisenstein lattice | flower digits vs 3-bit direction codes vs delta+xz vs order-0 arithmetic coding | at least 2% below the best other scheme; entropy floor is `log2 6 = 2.585` bits per step | likely fail |
| E5 LBC | 10^4 vectors in Z^8 generated by a hidden rank-3 integer basis, plus full-rank control and a noisy variant | HNF/kernel relation finding (not LLL alone) vs xz on int32 rows, basis cost included | at most 0.6x baseline at rank 3; no gain on the control; the noisy variant must fall back to raw | pass only for planted structure |

## 11. Corrections ledger (false claims found in the repo)

| Claim | Where | Truth |
| --- | --- | --- |
| "52 primes with `p-1` dividing 864000" | repo docs | 54 `[VERIFIED]` |
| `pi(144001) = 13267` | repo docs | 13343 = 11 * 1213 `[VERIFIED]`; `144001 = 11 * 13 * 19 * 53` |
| Other counts of primes with `p-1` dividing 144000 | repo docs | 38 `[VERIFIED]`; dividing 1008000: 74 (36 new, all with 7 dividing `p-1`) |
| "19^2 = 1 mod 144000" | docs | `19^2 mod 144000 = 361`; `19^k = 1 mod T` iff `T/180` divides `k` |
| "Any prime `p` has `p^2 = 1 mod 360`" | docs | false; only 14 primes below 500 |
| "probability 1e-6 for self-referential primes" | docs | contradicts observed 16/500 |
| geofs "X = 60: size 18, 5040 sets" | geofs report | `pi(60) = 17`; number of maximum pairwise-coprime sets is `5*3*2*2 = 60` `[VERIFIED formula for X = 10, 20, 24]`; the "X = 10: 1 set" example is also wrong (there are 6) |
| `compression_variants_formal.lean` has 15 `sorry` | earlier note in this file | 20 occurrences on 18 lines |
| HDC Theorem 2.4, LBC Theorem 4.1 | variant docs 2 and 3 | proofs invalid or circular, see section 8 |
| PQ ellipse `a = (q+1)/2` | docs | `a = q/2` (Aristotle CORRECTIONS) |
| kissing gap positive | docs | `1/sqrt 2 - 2/sqrt(pi) = -0.421`: circles overlap |
| layers are highly composite | docs | layers are 5-smooth |
| "no 5-fold lattice" | docs | false in dimension 4 |
| Descartes line case equals sphere case | docs | distinct; sphere coefficient is 3 |
| `LINREC d <= 8` vs `d <= 16`; `FAULHABER p <= 4` vs `p <= 14` | MASTER_PLAN `:2262-2310`, `tm_rods.h:201`, `tm_rod_series.h:27` | headers are looser than the plan text; reconcile |
| `/tmp/tcmp_interop.log` 120 failures | stale | newer gate PASS; ignore the old log |

## 12. Source index

- Thesis: `Thesis/THESIS.md` (`:592-649` boundary primes; `:1440-1456` GT-005; `:1481-1590` fractal primary object), `Thesis/MASTER_PLAN.md` (`:38-57`, `:92-101`, `:590-599`, `:2260-2310`, `:2906-2910`).
- Proofs: `Thesis/proofs/ThesisProofs/ThesisProofs/{BG006CRTDecomposition,BG085AdaptiveUsedCountInvariants,BG086CarrierResidueBijection,BG087CoprimeBranchingTrie,BG088FractalRodTower,GT007RecursivePrimeFractal}.lean`.
- Aristotle (`AR/`): `LatticeCalc/Verified/FractalAbacus.lean`, `RodOrders`, `RodsPrinciple`, `RodJump`, `RodMont`, `AbacusPrecision`, `ChainCertificates`, `TowerCollapse`, `FlowerFractal`, `SphereHensel`, `Scale361`, `Flower19`, `FlowerGeneral`, `Base60`, `RequestProject/QCompression.lean`; markdown: COPRIME_WAVES, CORE_PRIMES, DEEPER_LINKS, SEVENTH_RIM, TWELVE_DIAL, RAMANUJAN_LINK, SMOOTH_SPLIT, SODDY_COXETER, SIGNAL_DIALS, HYPERDIM_RODS, RODS_FLOWERS_TOWERS, SCALED_CONSTANTS, SCALING_19, LIBRARY_REDESIGN, OPEN_ITEMS_STATUS, CORRECTIONS, DEEP_FORENSIC.
- Codec: `Thesis/web/frontend/tcmp.js`, `Thesis/web/shared/coprime-codec.ts`, `Thesis/math/include/compat/tm_compression.h`, `Thesis/math/src/compat/tm_compression.c`, `Thesis/web/scripts/tcmp-*.mjs`.
- Rod C library: `Thesis/math/include/rods/tm_rods.h`, `tm_rod_series.h`.
- Variant docs: workspace root `*_COMPRESSION_*.md` files listed in section 8.

## 13. Review status of this file

- R1-R4 (research sweeps) done. R5 (citation and gap review) and R6 (number theory/algebra review; geometry/information-theory review) done on 2026-10-11 and merged: FractalAbacus line anchors corrected, sorry count corrected, Hensel hypotheses added, code-class statement of the counting bound added, completions and CRT-for-prime-powers added, exact 5-smooth table added, variant proof defects recorded, experiments E1-E5 and designs D1a, D7, D8 added.
- Reviewer re-confirmed `[VERIFIED]`: capacities, Garner counts, circle and hex Hensel counts, square roots of 1 mod 360, orders of 19, Omega values, `phi(360*60^k)`, `N_k` prime factors and power-of-two cases, chain-prime exponents (BPSW only for 820 and 1593; no certificate), 38/54/74 prime counts, `pi(144001)`, 65520 facts, 14 primes and 16 values, Mersenne dial sizes (gcds 1, lcm 360 and 144000, 21.95 and 262 bits), norms `19` and `361`, kissing gap `-0.42127`.
- Still unverified: every number tagged `[MEASURED]` that came from `/tmp` logs (rerun the named script before quoting). The Lean hypotheses of `card_fiber` were re-read in round 3: `k >= 1`, `p != 2`, `c` a unit mod `p`, conclusion `p^(d-1)` lifts per point (`AR/RequestProject/SphereHensel.lean:18, :107`). Section 24 is the current ledger.

---

# PART II. RESIDUE GEOMETRY, FRACTAL PARTITIONS, DETERMINISTIC CODES (round 2)

Part II holds the formula atlas the owner asked for. Tags are as in section 0, plus `[VERIFIED(py)]` for numbers recomputed by the round-2 mathematician passes (brute force or exact arithmetic, 2026-10-11) and `[SWEEP]` for a Lean theorem name or `file:line` reported by a sweep agent and not yet re-opened (the citation check in section 22 lists which were re-opened).

## 14. The unifying picture: what "residue geometry" is

One integer, five views, one bijection (`decode_unique`, BG086/BG087 `[PROVED]`):

| View | Object | Size | Geometry |
| --- | --- | --- | --- |
| column | `(x mod m_1, ..., x mod m_R)`, `m_i` pairwise coprime | `M = prod m_i` | point on the torus `prod Z/m_i`, which CRT identifies with `Z/M` |
| dial | `x mod m` as the angle `2 pi x / m` | `m` | the cyclic group `Z/m`; its symmetry group is `(Z/m)*` |
| plane | `(a, b)` in `Z[i]/p^j` or `Z[w]/p^j` | `p^{2j}` | level sets of the norm are circles / hex circles with exact point counts |
| tower | `x mod b^k` | `b^k` | b-adic tree; deeper rod = one more digit; the fibre of `Z/b^{k+1} -> Z/b^k` has `b` elements; the fibre of a solution set `Q = c` over a smooth point has `p^{n-1}` elements in `n` variables (`p` for the plane, `n = 2`) |
| partition | divisor lattice of `144000 = 2^7 3^2 5^3` | 96 divisors | rings, spokes, registers; nested chains; 60 maximal refinement paths for 360 |

Geometry gives six exact, checkable kinds of information about a set of residues. Each one is a cost formula, and each helps only relative to a promise that the data lie in the structured set (section 21):

1. Counting: the size of the structured set is a closed form (hex ball, flower, sphere, norm circle, divisor lattice, reduced residue system). `log2` of that size is the code length of an enumerative code.
2. Group coordinates: the set is a group with known invariants (norm-1 circle is cyclic of order `p^{j-1}(p - eta)` for `p` odd, `p != 3` for the hex form; `(Z/360)*` is `C2 x C2 x C2 x C12`). A point becomes an exponent vector; multiplication becomes addition.
3. Symmetry quotients: `D6` acts on hex rings (orbits `1 + floor(n/2)`), `x -> 19x` acts on the 360-dial; coding orbit plus representative removes a known factor.
4. Self-similarity: digit expansions `z = sum d_j beta^j` and `x = sum v_i P_i` give address codes whose truncation is a coarser view (progressive, scale-addressed).
5. Separability: CRT-additive signals have Fourier support on the rod axes only (`sum m_i - (k-1)` of `prod m_i` coefficients).
6. Descriptors: a sequence generated by a short rule (`ARITH`, `GEOM`, `FAULHABER`, `POLY`, `LINREC`, `PROD_GEOM`, `MATPOW`) is described by `O(d)` rod values, evaluated in `O(log N)` per rod.

None of these changes the entropy of a uniform source (bijection, section 1). They move cost only when the model puts more mass on the structured set than a uniform model does.

## 15. Formula atlas

### 15.1 Hexagonal lattice and Eisenstein integers

| ID | Formula | Status | Source |
| --- | --- | --- | --- |
| GEO-1 | shell `n` has `6n` cells (`n >= 1`); ball radius `n` has `1 + 3n(n+1)`: 7, 19, 37, 61, 91, 127 at `n = 1..6`; at `n = 10^6`: 3,000,003,000,001 | `[VERIFIED(py)]` BFS to `R = 40`; `[PROVED BG009 shellPopulation, cumulative_recurs_by_shell]` | `MASTER_PLAN.md:2300` |
| GEO-1b | other centres: FCC (3D) single `10n^2 + 2`, dual `10n^2 + 6n + 2`; FCC cumulative `(2n+1)(5n^2+5n+3)/3` = 1, 13, 55, 147, 309 `[VERIFIED(py)]` cumulative. The plan's "triangular dual-centre `6n + 2`" could not be reproduced by two reviewers (lattice unidentified): `[UNSURE]`. The C code `tm_shell_layers.c` uses `10n^2 + 2` (CONFLICT-001: that is the 3D shell, not the 2D one) | `[DERIVED]` plan analysis | `MASTER_PLAN.md:2510` |
| GEO-2 | `N_k = 3k^2 + 3k + 1 = (k+1)^3 - k^3 = 1 + 3k(k+1)` (the flower number is the hex ball size); `sum_{k<n} N_k = n^3`; `N_k` = 1, 7, 19, 37, 61, 91, 127, 169, 217, 271, 331 | `[VERIFIED(py)]` `k < 200` | `Flower19`, `FlowerGeneral` `[SWEEP]` |
| GEO-3 | `w^2 + w + 1 = 0`; `(a + b w)(c + d w) = (ac - bd) + (ad + bc - bd) w`; norm `N(a + b w) = a^2 - ab + b^2` | `[VERIFIED(py)]` | `MASTER_PLAN.md` GEO-3 |
| GEO-4 | hex distance in axial coordinates `max(\|a\|, \|b\|, \|a - b\|)` for the norm `a^2 - ab + b^2`. The variant `max(\|a\|, \|b\|, \|a + b\|)` is false for this norm; it belongs to `a^2 + ab + b^2`, whose units are `(+-1, 0), (0, +-1), +-(1, -1)` | `[VERIFIED(py)]` BFS | resolves `MASTER_PLAN.md:2546` pending item |
| GEO-5 | ring cell `cell(n, i) = n u_s + t (u_{s+1} - u_s)`, `s = floor(i/n)`, `t = i mod n`, `u = (1,0), (1,1), (0,1), (-1,0), (-1,-1), (0,-1)` (exactly the six norm-1 units of `a^2 - ab + b^2`, counter-clockwise) | `[VERIFIED(py)]` `n = 1..50`; Lean proof absent | `MASTER_PLAN.md:2304` |
| GEO-5b | rotation by 60 degrees (multiply by `(1,1)`) sends `i -> i + n mod 6n`; conjugation sends `i -> -i mod 6n` | `[VERIFIED(py)]` `n <= 40` | round 2 |
| GEO-6 | `D6` orbits on ring `n`: `1 + floor(n/2)`; orbit size 6 for `i = 0` and for `i = n/2` (n even), 12 otherwise | `[VERIFIED(py)]` `n <= 30` | `MASTER_PLAN.md` GEO-6 |
| GEO-13 | representation numbers `r(n) = #{(a,b): a^2 - ab + b^2 = n} = 6 (d_{1,3}(n) - d_{2,3}(n))`; `r(n)/6 = prod_{p = 1 mod 3} (e_p + 1)`, zero if some `p = 2 mod 3` has odd exponent. `r(1..12) = 6,0,6,6,0,0,12,0,6,0,0,6`. For `a^2 + b^2`: `r_2(n) = 4 (d_{1,4}(n) - d_{3,4}(n))` | `[VERIFIED(py)]` `n <= 200` | round 2 |
| GEO-13b | lattice points of norm `<= 200`: 733 (hex), 633 (square); area estimates give 725.5 and 628.3; 66 of 200 norms occur for the hex form, 79 of 200 for squares | `[VERIFIED(py)]` | round 2 |
| GEO-14 | theta series: `A2`: 1, 6, 6, 6, 12, 6, 6 at norms 0, 1, 3, 4, 7, 9, 12; `D4` (squared norm `2m`): `24 sigma_odd(m)` = 24, 24, 96, 24, 144, 96; `E8`: `240 sigma_3(m)` = 240, 2160, 6720, 17520; kissing numbers 6, 12, 24, 240, 196560 (2D, 3D, 4D, 8D, 24D) | `[VERIFIED(py)]` series; kissing numbers `[STANDARD]` | round 2 |
| GEO-15 | flower addressing: `beta_k = (2k+1) + k w`, `N(beta_k) = N_k`; `Z[w]/beta_k = Z/N_k` with digit map `rho_k(a,b) = a + (3k+1) b mod N_k`; the `k`-ball is a complete digit set; `A_n = {sum_{j<n} d_j beta^j} = A_{n-1} + beta^{n-1} D` is a union of `N_k` copies of `beta A_{n-1}`; the `N_k^n` addresses are distinct (`k = 1`, `n <= 5`; `k = 2`, `n <= 3`; `k = 3`, `n <= 3`); the ball is a complete residue system for `k <= 8` | `[VERIFIED(py)]`; `[PROVED addressB_exists AR/LatticeCalc/FlowerGeneral.lean:181, addressB_unique :197]` | `FlowerGeneral` |
| GEO-15b | address length `n ~ log_{N_k}(norm) + O(1)` (norms 13..109 need 3 digits, 73..819 four, 471..5881 five for `k = 1`; the earlier upper bound 2997 was the test bound); termination holds for all points with norm `<= 3000` (`k = 1, 2`) and `<= 1500` (`k = 3..6`), not proved in general | `[VERIFIED(py)]` | round 2 |
| GEO-15c | the largest disc contained in `A_n` holds a fraction 0.878, 0.738, 0.713 of `N_1^n` points (`n = 2, 3, 4`) and 0.867, 0.836 of `N_2^n` (`n = 2, 3`) | `[VERIFIED(py)]` | round 2 |
| GEO-15d | tile `T = {sum_{j>=1} d_j beta^{-j}}` has dimension 2; boundary dimension `log rho / log \|beta\|` with neighbour-graph spectral radius `rho = 3, 5, 7, 9` for `k = 1..4`: 1.12915, 1.09321, 1.07779, 1.06898; `k = 1` is the Gosper island `2 ln 3 / ln 7`. `rho = 2k+1` for all `k` is a pattern from four cases | `[VERIFIED(py)]` for the four; `[OPEN]` general; measure exactly 1 not proved | round 2 |
| GEO-16 | Mersenne flowers: `N_k = 2^m - 1` only for `k = 0, 1, 6` (flowers 1, 7, 127) `[VERIFIED(py)]` `k < 10^5`; finiteness is a Ramanujan-Nagell-type equation `3x^2 + 5 = 2^n` (solutions `x = 1, 3, 13` for odd `x < 10^6`; finiteness by Siegel/Beukers is standard, an explicit all-`k` proof is `[UNSURE]` in this file). `N_k` is prime for `k = 1, 2, 3, 4, 6, 9, 10, 11, 13, 14, 17, 23, 24, 25, 27, 28` (7, 19, 37, 61, 127, 271, 331, 397, 547, ...); `N_5 = 7 * 13`, `N_7 = 13^2`, `N_8 = 7 * 31`. The earlier list "7, 19, 127, 271, 331" omitted 37, 61, 397; "flower board primes" needs a stricter definition than prime `N_k` before it can be used | `[VERIFIED(py)]`; status per `OPEN_ITEMS_STATUS` `[SWEEP]` | `FlowerGeneral`, `RecursiveDepth` |
| GEO-17 | 19-flower: `19 = N_2 = N(5 + 2w)`; Gaussian analogue `beta = 2 + i`, 5 digits, norm 5 | `[VERIFIED(py)]` norms | `Flower19` |

The claim `beta_k = cube root(k N_k)` seen in one sweep has no support in the sources; do not use it.

### 15.2 Conics and spheres over `Z/p^j`: counts, groups, Hensel

Notation: `p` odd prime; `eps = (-1/p) = +1` iff `p = 1 mod 4`; `eta = +1` iff `p = 1 mod 3` (and `-1` if `p = 2 mod 3`); `c` a unit mod `p`.

| ID | Formula | Status |
| --- | --- | --- |
| H-1 | `#{x^2 + y^2 = c mod p^j} = p^{j-1} (p - eps)`; `#{a^2 - ab + b^2 = c mod p^j} = p^{j-1} (p - eta)` (`p != 3`; the hex form also holds at `p = 2` with `eta = -1`: 3, 6, 12, 24). Brute force: circle 8, 56 (mod 7, 49), 12, 132 (mod 11, 121); hex 6, 42 (mod 7, 49), 18, 342 (mod 19, 361) | `[PROVED card_fiber AR/RequestProject/SphereHensel.lean:107, card_pow_split AR/RequestProject/FlowerFractal.lean:275 (p = 1 mod 3), card_pow_inert :282 (p = 2 mod 3, p != 2)]`; `[VERIFIED(py)]` counts |
| H-2 | the fibre of the reduction of the solution set of `Q = c` from `p^{j+1}` to `p^j` over every smooth point (`c` unit, `p` odd) has `p^{d-1}` points in `d` variables: `p` for the plane (`d = 2`), `p^3` for `d = 4` (checked: fibre 125 mod 25 for `p = 5`, 27 for `p = 3`). This is `card_fiber` (`k >= 1`, `p != 2`, `c` unit). Mod `p^j` and unit `c`: `N^{(j)}(c) = p^{(j-1)(d-1)} N^{(1)}(c)` (H-11). The fibre of the bare reduction `Z/b^{k+1} -> Z/b^k` has `b` points; a single-variable simple root (`x^2 = a`, `f'(a)` unit) has fibre 1. At singular points (`c = 0 mod p`) the fibre differs. Surjectivity of the reduction: `reduce_surjective AR/RequestProject/FlowerFractal.lean:85` (`k >= 1`, `p != 3`) | `[PROVED card_fiber SphereHensel.lean:107, reduce_surjective]`; `[VERIFIED(py)]` |
| H-3 | norm-1 group theorem (`O = Z[i]` or `Z[w]`, `p` odd unramified, `G_j = {N = 1} mod p^j`): split `G_j = (Z/p^j)*`; inert `G_j = mu_{p+1} x {N = 1 in 1 + pO}`; so `\|G_j\| = p^{j-1} (p - eta)` and `G_j = Z/(p - eta) x Z/p^{j-1}` is cyclic (orders coprime). 27 odd unramified cases (p = 5, 7, 13, 19, 3 for `Z[i]`, p = 5, 7, 13, 19 for `Z[w]`, `j = 1, 2, 3`; the list gives 15 + 12 = 27, not 24; 17 odd cases were re-brute-forced by a reviewer) all brute-forced as cyclic with generators found | `[STANDARD]` ingredients, `[DERIVED]` assembly, `[VERIFIED(py)]` 27 cases |
| H-3b | order table `\|G_j\|` for `j = 1, 2, 3`: `Z[i]` p=5: 4, 20, 100; 13: 12, 156, 2028; 7: 8, 56, 392; 19: 20, 380, 7220; 3: 4, 12, 36. `Z[w]` p=7: 6, 42, 294; 13: 12, 156, 2028; 5: 6, 30, 150; 19: 18, 342, 6498 | `[VERIFIED(py)]` |
| H-3c | ramified: `Z[w]` mod `3^j` has order `2 * 3^j` (6, 18, 54) and is `Z/2 x Z/3 x Z/3^{j-1}` for `j >= 2` (not cyclic; through `j = 4`); `Z[i]` mod `2^j` has order `2^{j+1}`, structure `Z/2 x Z/4 x Z/2^{j-2}` for `j >= 3` (verified `j <= 8`; the earlier `Z/2 x Z/2^{floor(j/2)} x Z/2^{ceil(j/2)}` fits `j <= 5` and fails at `j = 6`, where the group is `[2, 4, 16]`; a general proof is `[OPEN]`); `Z[w]` mod `2^j` (inert) has order `3 * 2^{j-1}`, 2-part `Z/2 x Z/2^{j-2}` for `j >= 2` (verified `j <= 8`; general `[OPEN]`). The formula `p^{j-1}(p - eta)` therefore fails at the ramified prime | `[VERIFIED(py)]` |
| H-4 | exponent coordinate: if `g` generates `G_j` every point is `g^e`, `e` unique in `Z/\|G_j\|`; `e <-> (e mod (p - eta), e mod p^{j-1})`; reduction to `p^{j'}` is `e -> (e mod (p - eta), e mod p^{j'-1})`; so Hensel fibre digits are the base-`p` digits of the p-adic coordinate `e mod p^{j-1}`. Generator reduction and `red(g^e) = red(g)^e` verified on 4 cases | `[DERIVED]`; `[VERIFIED(py)]` on (`Z[i]`, 5, 3), (`Z[i]`, 13, 3), (`Z[w]`, 7, 3), (`Z[w]`, 19, 3) |
| H-5 | level sets `N = c` (`c` unit, `p` odd, and `c` a norm) are cosets `x_0 G_j` of the same size. At the ramified prime `p = 3` for `Z[w]`: smooth unit-`c` points exist (fibres `p`) but the count is `2 * 3^j` for `c = 1 mod 3` and 0 for `c = 2 mod 3`, so "smooth" does not by itself give `p^{j-1}(p - eta)` | `[DERIVED]`; `[VERIFIED(py)]` |
| H-6 | stacking law (sum of `d` squares, `d` variables): `N_{d+2}(c) = (p - eps) p^d + eps p N_d(c)`; closed forms `N_{2k}(c) = p^{2k-1} - eps^k p^{k-1}`, `N_{2k+1}(c) = p^{2k} + eps^k p^k (N_1(c) - 1)`; hex version `F_{k+1}(c) = (p - eta) p^{2k} + eta p F_k(c)` (`p != 3`; it also holds at `p = 2`), `F_k(c) = p^{2k-1} - eta^k p^{k-1}`; for four variables the count mod `p` is `p^3 - p` (`p^{4j-1} - p^{2j-1}` in the earlier notation, where `j` meant the number of variable pairs and not the depth; mod `p^j` multiply by `p^{(d-1)(j-1)}`) (`sphere_four_mul AR/RequestProject/RodSpheres.lean:366`, `flower_four_mul :374`). The recurrence holds over `F_p` for every `c`, including 0; only the closed forms need `c` a unit (see H-10). Checked numerically for `d = 1..6`, `p in {3, 5, 7, 11, 13, 19}` and `c` unit | `[PROVED sphere_four_mul, flower_four_mul]` (the `d = 4` cases); the general stacking `[SWEEP]` (`SphereHensel`, `FlowerFractal`, `UNIFIED_GEOMETRY.md`); `[VERIFIED(py)]` |
| H-7 | `c = 0` over `F_p`: `d = 2` count is `2p - 1` if `p` splits and `1` if `p` is inert in `Z[i]` (so also at `p = 3` for squares); for the hex form at `p = 3` the count is 3 (`b = 2a`), and `3^j` mod `3^j`; `d = 4` count is `p^3 + p^2 - p`. The unit-`c` closed forms of H-6 do not hold at `c = 0` | `[VERIFIED(py)]` |
| H-8 | the 71 ladder: `seventyone_ladder AR/RequestProject/RodSpheres.lean:425` `[PROVED name located; statement not re-read]`; `Soddy`-type lift of the same structure; meaning `[OPEN]` | name `[FOUND]` |

Index (discrete-log) RNS: `[STANDARD]` in the RNS literature. Per rod with prime `p` and generator `g`, `[DERIVED]`:

| op | residue form | index form |
| --- | --- | --- |
| mul | multiply and reduce | add `ceil(log2(p-1))`-bit indices mod `p - 1` |
| inverse | extended gcd or `x^{p-2}` | negate: `-i mod (p - 1)` |
| `x^k` | `O(log k)` multiplications | one product `k i mod (p - 1)` |
| add | add and conditional subtract | `i_x + Z(i_y - i_x)` with Zech log `Z(n) = log_g(1 + g^n)`: subtract, table lookup (`p` entries), add |
| zero | ordinary value | needs a separate flag |

It helps multiplication- and power-heavy loads and hurts addition-heavy ones. Not used in `Thesis/math` today.

### 15.3 Dials, unit groups, orders

| ID | Formula | Status |
| --- | --- | --- |
| D-1 | unit groups `(Z/m)*` `[VERIFIED(py)]`: `m = 60`: `phi = 16`, `lambda = 4`, `[2,2,4]`, 8 square roots of 1; `360`: 96, 12, `[2,2,2,12]`, 16; `7200`: 1920, 120, `[2,2,4,120]`, 16; `144000`: 38400, 2400, `[2,2,4,2400]`, 16; `65520`: 13824, 12, `[2,2,2,12,12,12]`, 64; `2520`: 576, 12, `[2,2,2,6,12]`, 32; `1008000`: 230400, 2400, `[2,2,2,12,2400]`, 32. None is cyclic, so no generators. `#sqrt(1) = 2^{#even invariant factors}` |
| D-2 | `(Z/360)* = (Z/8)* x (Z/9)* x (Z/5)* = C2 x C2 x C6 x C4 = C2 x C2 x C2 x C12` (order 96). `C2 x C2 x C2 x C6` is a wrong guess: order 48 and no elements of order 4 or 12. Element orders mod 360: 1:1, 2:15, 3:2, 4:16, 6:30, 12:32. Mod 7200: 1:1, 2:15, 3:2, 4:48, 5:4, 6:30, 8:64, 10:60, 12:96, 15:8, 20:192, 24:128, 30:120, 40:256, 60:384, 120:512 (sum 1920). 96 Dirichlet characters mod 360, 16 real | `[VERIFIED(py)]` |
| D-3 | `u^12 = 1 mod m` for all units iff `lambda(m) \| 12` iff `m \| 65520 = 2^4 3^2 5 7 13` (120 divisors). Proof: `lambda(p^k)` gives primes `{2,3,5,7,13}` with exponents `4, 2, 1, 1, 1`. Checked for all `m <= 10^5`. `65520 = 2^16 - 16`; Leech kissing number `196560 = 3 * 65520`. The exponent 12 belongs to the 360-dial only: `lambda(144000) = 2400` | `[DERIVED]`, `[VERIFIED(py)]`; `[PROVED twelve_65520 AR/LatticeCalc/Verified/TwelveDial.lean:58; twelve_dial_iff, inv_eq_pow_eleven (u^-1 = u^11 on every divisor of 65520), orderOf_eleven_65520, prime_of_twelve :84 (only primes 2, 3, 5, 7, 13)]` |
| D-4 | order of 19: `19^2 - 1 = 360 = 2^3 3^2 5`; by lifting the exponent (`v2(19^k - 1) = 2 + v2(k)` for even `k`; see section 4) `ord_{360 d}(19) = 2d` for every `d = 2^a 3^b 5^c` (checked for 16 values of `d`); `360 * 10^k`: `2 * 10^k`; `360 * 20^k`: 2, 40, 800, 16000, 320000; `360 * 60^k`: 2, 120, 7200, 432000 (`2 * 60^k = lambda / 3` for `k >= 1`); `144000 = 360 * 400` gives 800; mod `1008000`: `lcm(800, ord_7(19) = 6) = 2400`. Only 2, 3, 5 divide `19^2 - 1`, so only they enter the lift | `[DERIVED]` LTE, `[VERIFIED(py)]` |
| D-5 | tower `m = 360 * 60^k`, `k = 0..3`: `phi = 96, 5760, 345600, 20736000`; `lambda = 12, 360, 21600, 1296000`; invariants `[2,2,2,12]`, `[2,2,4,360]`, `[2,2,4,21600]`, `[2,2,4,1296000]` (top factor `6 * 60^k`); open fraction `phi / m = 4/15` for all `k` | `[VERIFIED(py)]` |
| D-6 | multiplication by 19 on the 360-dial: `19 = 3 mod 8`, `1 mod 9`, `4 mod 5`; an involution with 18 fixed points (the multiples of 20); a CRT mixture of reflections, not a single mirror. The group of order 360 is the multiplicative group of the field `F_361 = GF(19^2)`, `F_361* = C360` with 96 generators (`FiniteField`); `(Z/361)*` (361 = 19^2 as a ring) is cyclic of order `phi(361) = 342`, not 360. `19 + 6 sqrt10 = (3 + sqrt10)^2`: 19 is the real part of the square of the fundamental unit of `Z[sqrt10]` (norm -1), so powers of 19 mod `T` are a Chebyshev/Pell orbit | `[VERIFIED(py)]` fixed points; `[PROVED sq_nineteen_mod_eq_one_iff AR/LatticeCalc/Scale361.lean:176, nineteen_involution :195 (orderOf (19 : ZMod 360) = 2)]` |
| D-7 | golden step `p -> p * 137508 mod 360000`: `gcd(137508, 360000) = 12`, period 30000, injective on `p < 30000`, all values multiples of 12; `11 * 137508 = 30011 * 137508 = 72588 mod 360000`; `137508 / 12 = 11459 = 7 * 1637`; `30000 (3 - sqrt5)/2 = 11458.98`, so 11459 is the exact rounding; `p * a mod M` has period `M / gcd(a, M)` | `[VERIFIED(py)]`; `[PROVED BG011]` |
| D-8 | `TM_GOLDEN_MILLI = 2225` (cited as `tm_angle_wrap.c:5`; a workspace-wide grep finds the symbol only in `Thesis/MASTER_PLAN.md:2310, :2476, :2511` and the `bak.Thesis` copy, not in any source file, so the code line is `[UNVERIFIED]`) cannot be derived from the golden step: `gcd(2225, 30000) = 25` gives period 1200 (11 and 1211 collide at 24475), on a 360000-dial period 14400; 2225 is not `0.381966 * 30000 = 11459`, not 2399.96 (milliradians of the golden angle) | `[VERIFIED(py)]`; intended unit `[OPEN]` (`CONFLICT-002`) |
| D-9 | Mersenne dial rods: gcds 1, lcm 360 and 144000, sizes 21.95 and 262 bits (v1 section 7); `lc_mersenne_mod`, `lc_rotl` | `[VERIFIED]` |
| D-10 | `SeventhRim`: `1008000 = 7 * 144000`, tick 600 ms, a base `B = 3 mod 7` is a primitive root mod 7 | `[PROVED]` `[SWEEP]` |

### 15.4 Soddy, Descartes, Pisot, quadratic rods

| ID | Formula | Status |
| --- | --- | --- |
| S-1 | Descartes: `(k_1 + k_2 + k_3 + k_4)^2 = 2 (k_1^2 + ... + k_4^2)`; mirror `k_i' = 2 sum_{j != i} k_j - k_i`; check `(-1, 2, 2, 3)`: 36 = 36. Spheres (5 mutually tangent): `(sum k)^2 = 3 sum k^2`; check `(-1, c, c, c, c)`, `c = 1 + sqrt6 / 2`: both sides `33 + 12 sqrt6 = 62.3939` | `[VERIFIED(py)]`; `[PROVED apollonian_mod24 AR/RequestProject/FirstSphere.lean:183]`; `DescartesGeneral` `[SWEEP]` |
| S-2 | `u_{n+3} = 3 u_{n+2} + 3 u_{n+1} - 6 u_n`, `u_0, u_1, u_2 = 1, 4, 12`: 1, 4, 12, 42, 138, 468, 1566, 5274, 17712, 59562, 200178, 672948, 2262006, 7603794. Characteristic polynomial `x^3 - 3x^2 - 3x + 6` (irreducible, discriminant `837 = 3^3 * 31`), roots 3.3614687662, 1.1674491911, -1.5289179573. With `x = y + 1`: `y^3 - 6y + 1`, `lambda_j = 1 + 2 sqrt2 cos((arccos(-1/(4 sqrt2)) + 2 pi j)/3)`. No rounding shortcut: the negative root has modulus above 1. `u_{10^18} mod (10^9 + 7) = 921810451` by companion matrix power. A rod column costs `2 d^3 floor(log2 N) = 54 floor(log2 N)` operations (`d = 3`). **What `u_n` counts `[PROVED]`:** in the recursive kissing packing of five mutually tangent spheres, generation `d` contains exactly `5 * b_d` new spheres with `b = 1, 1, 4, 12, 42, 138, ...`, i.e. `5 u_{d-1}` for `d >= 1`; the counts `5, 5, 20, 60, 210, 690, 2340, 7830, 26370, 88560, 297810, 1000890, 3364740` observed by the C library through depth 12 follow the recurrence at every depth (`newSpheres_ncard`, `soddyB_first_values` `AR/RequestProject/SoddyCounts.lean`). The proof: spheres are cosets `g W_{S minus j}` of the Coxeter group `W(M3(Fin 5))`; minimal coset representatives have growth series `(1 - 2t - 2t^2 + 3t^3) / (1 - 3t - 3t^2 + 6t^3)`. The Apollonian circle curvature sums have a different recurrence (`S_{g+2} = 8 S_{g+1} - 3 S_g`, discriminant 52), so `u_n` is not that. Mod `m` the sequence is eventually periodic with a pre-period because `det = -6` is a non-unit mod 2 and 3: (pre-period, period) mod 8 (3,6), 9 (5,1), 5 (0,6), 360 (5,6), 7200 (5,120), 144000 (7,2400); prime periods `p = 5: 6`, `7: 19`, `11: 665`, `13: 168`, `31: 465` `[VERIFIED(py)]` | `[VERIFIED(py)]`; `[PROVED soddyB_recurrence SoddyCounts.lean:47-48, soddyB :43, soddyB_first_values :53, newSpheres_ncard :138]` |
| S-3 | circle pair kernel `Delta = (d - (r_1 + r_2)^2)(d - (r_1 - r_2)^2)` (GEO-9), `D_n` roots `2n(n-1)` (GEO-12, source pending), hyper ball radius `beta(n) = (pi^{n/2} / Gamma(n/2 + 1))^{1/n}` (`HyperBridge`) | `[SWEEP]`; GEO-12 `[OPEN]` |
| S-4 | Pisot units `2 + sqrt6`, `3 + 2 sqrt3`, `2 + sqrt3` (`PisotRods` `read_pow`); `QuadRods`: norm multiplicative; `Cell120` (`Z[phi]`, 600 vertices of the 120-cell) and `ByteKissing` (240 vectors) | `[SWEEP]` |

### 15.5 Waves and signals

| ID | Formula | Status |
| --- | --- | --- |
| W-1 | Ramanujan sum `c_n(t) = sum_{a mod n, gcd(a,n)=1} cos(2 pi a t / n) = sum_{d \| gcd(n,t)} mu(n/d) d`; multiplicative in `n` over coprime `n` (2,002,123 checks, `m, n <= 60`); `c_n(0) = phi(n)`, `c_n(1) = mu(n)`; zoom `c_{p^{k+1}}(p t) = p c_{p^k}(t)` for `k >= 1` (at `k = 0`: `c_p(p t) = p - 1` but `p c_1(t) = p`); the closed form `c_n(t) = mu(n/g) phi(n) / phi(n/g)`, `g = gcd(n, t)`, so `c_n(t) != 0` iff `n | t rad(n)` iff `n/g` is squarefree, and the silent times are the complement (an earlier wording had this reversed); Parseval `sum_{t mod n} c_n(t)^2 = n phi(n)` | `[VERIFIED(py)]` `n <= 60` |
| W-2 | Good-Thomas: `N = m n'` coprime, input `n = n_1 n' a + n_2 m b` (`a = n'^{-1} mod m`, `b = m^{-1} mod n'`), output `X[k] = F2D[a k mod m, b k mod n']`; no twiddle factors; cost `(mn)^2 -> m n (m + n)` (naive row-column). Max error 1e-13 on (8,45), (9,40), (5,72), (128,1125). Derivation: `k n / N = k n_1 a / m + k n_2 b / n' mod 1` | `[STANDARD]`, `[VERIFIED(py)]` |
| W-3 | CRT-separable signal `f(x mod m_1) + g(x mod m_2)` has at most `m_1 + m_2 - 1` nonzero DFT coefficients (equality for generic data; a product signal has support `|f^| |g^|`, dense only when both factors are); `k` rods: `sum m_i - (k - 1)`. Measured: (8,45): 52 of 360; (9,40): 48; (5,72): 76; (8,9): 16 of 72; (128,1125): 1252 of 144000; (8,9,5): 20 of 360; (128,9,125): 260 of 144000. A product signal `f g` or a generic one is fully dense (360 of 360). Test: `M[i,j] - M[i,0] - M[0,j] + M[0,0] = 0` | `[VERIFIED(py)]` |
| W-4 | Lissajous period `lcm(a, b)`; Fine-Wilf bound `p + q - gcd(p, q)`; `window_hits_left`; negative-space sum identity | `[STANDARD]`; names `[SWEEP]` |
| W-5 | `hdc` basis `psi_{k,i} = sin(2 pi k r_i / p_i)`; handshake overhead `E = 100 (L - 8) / L`; sublattice gain `(1 - k'/k)` | `[CLAIMED-UNMEASURED]` |
| W-6 | superseded by section 23 rows CH-*, NTT-*, FFT-*, RS-*, KG-*: Dirichlet characters, NTT, Ramanujan sums, Kloosterman sums were computed in round 3. Farey sequences and discrete-log tables: no repository module | `[OPEN]` for code |

## 16. Deterministic coding recipes

Every recipe states its input class, exact bit formula, the naive cost, and a falsifier. All bit counts are `[VERIFIED(py)]` unless marked. Each is a change of model (section 21), not a way to shrink uniform data.

| ID | Input promise | Code | Bits | Naive | Falsifier |
| --- | --- | --- | --- | --- | --- |
| R1 hex rank | axial point in hex ball radius `R` | `rank`/`unrank` below | `ceil(log2(1 + 3R(R+1)))` | `2 ceil(log2(2R+1))`; asymptotic saving `log2(4/3) = 0.41504` bit per point, plus up to 2 bits from rounding | rank(unrank) = id for all `R <= 60` (done) |
| R1b shell code | points concentrated near the origin | entropy-coded shell `n` (Golomb or arithmetic), then ring index `i` (`log2 6n` bits) | discrete Gaussian `R = 300`: within 0.02 bit of the point entropy (4.30, 6.30, 8.95, 12.95, 17.42 bits for `sigma` = 1, 2, 5, 20, 100) | fixed 19-bit ball code, 20-bit two-coordinate code; saving about 15.7 bits at `sigma = 1`, 7 bits at `sigma = 20` | Elias-gamma on `n` is a poor prefix: at `sigma = 100` it costs 23.11 bits, worse than 19 |
| R2 flower address | lattice point of norm `m` | `n` base-`N_k` digits | `n log2 N_k`: 2.807 bits per digit (`k = 1`), 4.248 (`k = 2`); `n ~ log_{N_k} m + O(1)`; examples: `(-17, 22)` norm 1147: 14.0 bits (`k = 1`, 5 digits), 12.7 bits (`k = 2`, 3 digits) vs 12 for two coordinates; `(100, -37)`: 16.8 / 17.0 vs 16 | `log2 m + 2` | Not shorter than coordinates. Value: truncation at `n` digits is reduction mod `beta^n` (coarse view), which matches the tower |
| R3 norm-circle index | point promised on norm circle `n` | index among `r(n)` points | `log2 r(n)`: mean 3.378 bits over represented `n <= 200` (hex), max `log2 24 = 4.585`; squares: mean 2.885, max `log2 16 = 4` | storing the point | Summed over all `n <= B` it equals the ball count: no gain unless many points share a norm. Unranking needs the factorisation of `n` (unit: 6 choices; each `p = 1 mod 3`: `e_p + 1` splits, mixed radix) |
| R4 circle exponent | point of `N = 1` mod `p^j` | exponent `e` with point `= g^e` | `ceil(log2(p^{j-1}(p - eta)))`: (19,3): 13 vs 26; (13,3): 11 vs 24; (7,3): 9 vs 18; (5,3): 8 vs 14; (101,4): 27 vs 54 | two residues `2 ceil(j log2 p)` | Encoding needs a discrete log; Teichmuller/p-adic decomposition (section 23.1, M1) reduces it to a `(p - 1)`-entry table plus a p-adic logarithm computed digit by digit, so no table of size `|G|` or BSGS is needed. The factor 2 is the dimension count: a curve in a plane. Coding `x` plus a sign bit gives the same size; the exponent form is better for multiplication (add exponents), not for size |
| R5 unit vector | `x` promised coprime to `m` | exponent vector over invariant factors `d_i` | `sum ceil(log2 d_i)`: 360: 7 (exact `ceil log2 96 = 7`, residue 9); 7200: 11 (13); 144000: 16 (18); 1008000: 19 (exact 18, residue 20); 65520: 15 (exact 14, residue 16) | `ceil(log2 m)` | saving `<= log2(m / phi(m))`, units only; a non-unit needs a tag (264 of the 360 residues mod 360 are non-units) |
| R5b rod-wise unit index | `x` coprime to 360 across rods 8, 9, 5 | index in `(Z/m_i)*`, states 4, 6, 4 | `log2 96 = 6.585` vs `log2 360 = 8.492`: gain 1.907 = 1 + 0.585 + 0.322 | residue bits | any non-coprime input; equals the wheel gain of `{2,3,5}` |
| R6 wheel rank | integer coprime to `W` | `rank(n) = floor(n/W) phi(W) + #{r in R_W : r < n mod W}`, table of size `phi(W)` | saving `log2(W / phi(W))`: `W` = 6: 1.585; 30 and 360: 1.9069; 210: 2.1293; 2310: 2.2668; 30030: 2.3823 (grows like `log2(e^gamma ln y)`, Mertens) | `log2 W` | uniform data: 4/15 of integers are in the class, so with escape coding the expected length is at least `n` |
| R6b prime gaps | the primes up to `N` | Rice (best `k`) on wheel-index gaps | `N = 10^7`, 664,573 primes above 13 (`pi(10^7) = 664,579`; the six primes 2..13 lie outside the wheel index): fixed width 15,949,752 (24 bits per prime); plain Rice on `gap - 1` 3,519,884 (`k = 3`); raw-gap entropy `H_0` 2,771,826 (4.17 bit/prime); wheel 30030 + Rice on `gap - 1` 1,823,927 (`k = 1`), `H_0` 1,785,365 (2.69 bit/prime); `log2 C(N, n) = 3,525,606` for an arbitrary subset. `N = 10^6`, 78,492 primes above 13 (`pi = 78,498`): plain Rice 393,526, wheel 30030 Rice 191,803 (`k = 0`). Convention: Rice codes `gap - 1` (unary quotient, terminator bit, `k` remainder bits); coding the raw gap gives 3,632,418 and 2,087,868. The plain-Rice baseline is a straw man: gaps above 2 are even, so Rice on `g/2 - 1` costs 2,855,312 (`k = 2`) at `10^7` and 315,035 at `10^6`; the honest wheel gain is 1,031,385 bits (36%) at `10^7` and 123,232 bits (39%) at `10^6`, not 48% and 51%. The entropy figure 2.77 Mbit is unaffected | fixed width | Conditioning plain gaps on `p mod W` gives the same entropy (2.5985 bit/prime at `W = 30030`, 5760 contexts, overfit). The wheel carries only the density promise. The prime list below `N` is regenerable from `N` alone (`O(log N)` bits), so any gap coder is the wrong tool for "all primes" |
| R7 CRT-separable | additive periodic signal over rods `m_1..m_k` | store `sum m_i - (k - 1)` values | (128, 1125): 1252 vs 144000 values; (128, 9, 125): 260; (8, 9, 5): 20 of 360 | `prod m_i` values | product or generic signal: full support |
| R8 smooth exponent | `x` promised 5-smooth | exponent triple `(e_2, e_3, e_5)` | count of 5-smooth `<= 2^64`: 13283, `log2 = 13.697`; `<= 2^32`: 1849, 10.853; in the top bit range at `n = 64`: 591 (9.2 bits); with an escape bit at weight 1/2 a smooth `x` costs 14.70 bits, others 65 | 64 | a random 64-bit integer is 5-smooth with probability `6.4e-17` |
| R9 Garner prefix | any `x` | mixed-radix digits `v_i` | first `k` digits carry `log2 P_k` bits; `x < P_k` needs only `k` digits: `log2 P_k < log2 x + log2 m_{k-1} + 1` | `log2 x` | `sum_{i<k} v_i P_i = x mod P_k` (a residue-class prefix, verified on 2000 random 16-prime values); no magnitude prefix |
| R10 descriptor-first | integer sequence from a family | `1 B` tag, `4 B` length, parameters, raw fallback | `n = 10^5` 64-bit values, seed 12345 (raw 800,000 B): AP 21 B (zlib-9 800,251, lzma 800,100, bz2 803,810); cubic mod `2^64` 37 B; `LINREC` order 4: 69 B (lzma 726,552); periodic sum (7, 11, 13): 253 B (lzma 8,356); uniform random: 800,001 B (zlib 800,251, lzma 800,100, bz2 803,907); AP + 4-bit noise: 21 B + nibble-packed residual 50,021 B vs lzma 301,236, entropy floor 50,000 | generic compressors | Worst case `n + c` (header). Generic byte compressors cannot see the structure because 64-bit modular wrap hides it from byte models |

Hex `rank`/`unrank` `[VERIFIED(py)]`: bijection onto the ball for every `R <= 60`.

```python
from math import isqrt
U=[(1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1)]
def unrank(r):
    if r==0: return (0,0)
    n=(isqrt(12*r-3)+3)//6; s,t=divmod(r-(3*n*n-3*n+1),n); (p,q),(x,y)=U[s],U[(s+1)%6]
    return (n*p+t*(x-p), n*q+t*(y-q))
def rank(a,b):
    n=max(abs(a),abs(b),abs(a-b))
    if n==0: return 0
    if a==n and 0<=b<n: i=b
    elif b>0 and a>-n and (b==n or b-a==n): i=2*n-a
    elif a==-n and -n<b<=0: i=3*n-b
    else: i=5*n+a
    return 3*n*n-3*n+1+i
```

Shell `n` begins at rank `3n^2 - 3n + 1` (the ball of radius `n - 1`); shell of rank `rho >= 1`: `n = (isqrt(12 rho - 3) + 3) // 6`. The float form `ceil((-3 + sqrt(9 + 12 (r - 1))) / 6)` is correct for 1-indexed `r`; use `isqrt` for large `r`.

Lattice codes `[VERIFIED(py)]` (theta-series offset plus a DP rank, `[STANDARD]` enumerative coding): `E8` norm `<= 2`: 241 points, 7.91 bits vs 24 for doubled coordinates; norm `<= 4`: 2401, 11.23 bits vs 32; norm `<= 8`: 26641, 14.70 vs 32; `D4` norm `<= 4`: 49 points, 5.61 bits vs 12; `<= 12`: 409, 8.68 vs 12. Asymptotic saving against the coordinate box: `D4` 2.70 bits, `E8` (doubled coordinates) 13.98, plain `Z^8` 5.98.

Redundant rods `[VERIFIED(py)]` (largest 31-bit primes, every rod 31 bits; aligned bytes `4n` / packed `ceil(31 n / 8)`; ratio to payload; `r` redundant rods give distance `r + 1` provided the payload range is at most the product of the `c` smallest moduli (counterexample: moduli 5, 7, 11, 13, 17 with range `11 * 13 * 17 = 2431` gives `d = 2`, not 3; the table's payloads satisfy the condition, the shortfall being under 0.02 bit): detect `r`, correct `floor(r/2)` errors or `r` erasures):

| c | payload B | r = 0 | r = 1 | r = 2 | r = 4 | r = 7 |
| --- | --- | --- | --- | --- | --- | --- |
| 8 | 30 | 32/31 (1.067/1.033) | 36/35 (1.200/1.167) | 40/39 (1.333/1.300) | 48/47 (1.600/1.567) | 60/59 (2.000/1.967) |
| 16 | 61 | 64/62 (1.049/1.016) | 68/66 (1.115/1.082) | 72/70 (1.180/1.148) | 80/78 (1.311/1.279) | 92/90 (1.508/1.475) |
| 32 | 123 | 128/124 (1.041/1.008) | 132/128 (1.073/1.041) | 136/132 (1.106/1.073) | 144/140 (1.171/1.138) | 156/152 (1.268/1.236) |
| 64 | 247 | 256/248 (1.036/1.004) | 260/252 (1.053/1.020) | 264/256 (1.069/1.036) | 272/264 (1.101/1.069) | 284/276 (1.150/1.117) |
| 128 | 495 | 512/496 (1.034/1.002) | 516/500 (1.042/1.010) | 520/504 (1.051/1.018) | 528/512 (1.067/1.034) | 540/524 (1.091/1.059) |
| 1024 | 3967 | 4096/3968 (1.0325/1.0003) | 4100/3972 (1.0335/1.0013) | 4104/3976 (1.0345/1.0023) | 4112/3984 (1.0366/1.0043) | 4124/3996 (1.0396/1.0073) |

Brute-force minimum distance `d = n - c + 1`: moduli (5,7,11,13), `c = 3`: 2; (5,...,17), `c = 3`: 3; (5,...,19), `c = 3`: 4; (5,...,19), `c = 2`: 5. Singleton argument: puncturing `d - 1` rods must keep the map injective. Redundant rods add no entropy; they are an error-control code.

Garner prefix capacity `[VERIFIED(py)]`, `log2(p_k#)` for the first `k` primes: 1: 1.00; 2: 2.58; 3: 4.91; 4: 7.71; 5: 11.17; 6: 14.87; 7: 18.96; 8: 23.21; 9: 27.73; 10: 32.59; 11: 37.55; 12: 42.75; 13: 48.11; 14: 53.54; 15: 59.09; 16: 64.82; 24: 114.19; 32: 168.49. Exact products: 8 primes 9,699,690; 12 primes 7,420,738,134,810; 16 primes 32,589,158,477,190,044,730.

## 17. Fractal partition atlas (the divisor lattice and its rings)

Setting: dial `D = 144000 = 2^7 3^2 5^3`; ring of order `k` has `k` points; rings `k` and `m` share `gcd(k, m)` spokes; a ring is in register with the dial iff `k \| m`. Lean names are `[PROVED]` per sweep `[SWEEP]` (`FractalPartition.lean`, `Scale361.lean`, `ShellRelations`, `TowerCollapse`, `TotientDepth`, `RecursiveDepth`, `Base60`, `SmoothSplit`, `TwoSpokePrimes`, `FiniteField`).

| ID | Statement | Name / evidence |
| --- | --- | --- |
| P-1 | `rings_in_register_iff` (`k \| m`); `shared_spokes_card = gcd(k, m)` | `FractalPartition` |
| P-2 | nested codex tower `[3, 6, 12, 60, 360]` (`codex_tower_nested`); `[12, 30]` breaks it: `12 \| 30` is false (`scrap_sequence_break`) | `FractalPartition` |
| P-3 | maximal refinement paths of 360: 60 `= 6! / (3! 2! 1!)`, each of length 6 (`refinement_words_360`); a path code costs `log2 60 = 5.91` bits `[DERIVED]` | `FractalPartition` |
| P-4 | depth `Omega`: `Omega(60) = 4`, `Omega(360) = 6`, `Omega(7200) = 9`, `Omega(144000) = 12`, `Omega(360 * 60^k) = 6 + 4k` (`ring_depths`); `depth_eq_refinement_length`; `depth_seventy_one` (depth 2 although `Omega(70) = 3`); `depth_257`; `depth_unbounded` | `FractalPartition` |
| P-5 | `hits(d) = tau(20 / e_0)`, `e_0 = d / gcd(d, 7200)` (`hits_eq_card_divisors`), equivalently for `d = 2^a 3^b 5^c \| 144000`: `(8 - max(a, 5)) (4 - max(c, 2))` (checked equal on the grid; values 6, 4, 3, 2, 1 = level profile `{1, 2, 3, 4, 6}`, which is not a chain, `level_profile_not_chain`) | `FractalPartition`, `ShellRelations` (shell regions 54 / 9 / 18 / 12 / 3 hitting 6 / 4 / 3 / 2 / 1) |
| P-6 | coprime zoom: `coprime_zoom_iff_mod30` (`gcd(x, 360 * 60^k) = 1` iff `gcd(x mod 30, 30) = 1`); `totient_zoom`: `phi(360 * 60^k) = 96 * 60^k`, open fraction 4/15; `seven_breaks_zoom`: `phi(2520) = 576`, 8/35 | `[VERIFIED(py)]` fractions; names `[SWEEP]` |
| P-7 | temporal layers `7200, 14400, 28800, 36000, 72000, 144000` with counts `19, 24, 27, 25, 31, 35` (`layer_counts`), `gcd(layers) = 7200` | `[SWEEP]` Lean; gcd `[VERIFIED(py)]` |
| P-8 | `center_open AR/RequestProject/FractalPartition.lean:364`; `annulus_shut :374`: `24 \| p^2 - 1` for primes `p >= 5` (the closed annulus); the primes with `p^2 = 1 mod 360` are exactly `p = 1, 19, 26, 44 mod 45` (CRT): 11 below 360 (19, 71, 89, 109, 179, 181, 199, 251, 269, 271, 359) and 27 below 1000 (adds 379, 431, 449, 521, 541, 631, 701, 719, 739, 809, 811, 829, 881, 919, 971, 991); the earlier "11 below 1000" was wrong; `TwoSpokePrimes` `[SWEEP]` | `[PROVED center_open, annulus_shut]`; `[VERIFIED(py)]` counts |
| P-9 | `Scale361`: `sq_nineteen_mod_eq_one_iff` (`AR/LatticeCalc/Scale361.lean:176`), `nineteen_least` (`AR/Temporal.lean:121`; 19 is the least integer `> 1` with `19^2 = 1 mod 360`), `sqrt_one_mod360` (16 roots), `nineteen_involution` (`Scale361.lean:195`) | `[PROVED]` three names; `sqrt_one_mod360` name not yet located; 16 roots `[VERIFIED(py)]` |
| P-10 | `TowerCollapse` `dial_tower`: 360 -> 12 -> 2; core `M = 11 * 19 * 71 * 97 * 109 -> 30240 -> 72 -> 6`; `TotientDepth`: `A(360) = 7`, `A(361) = 6` (symbol `A` is not defined in any source read; two reviewers found the `phi`-depth of 361 is 7 and the Carmichael-tower depths are 3 for 360 and 5 for 361, so treat `A(361) = 6` as `[UNSURE]`), `tdepth(360) = tdepth(361) = 7`; the core tower `156892747 -> 30240 -> 72 -> 6` is `[VERIFIED(py)]`; `RecursiveDepth`: `totient_tower_360 :292`, `dial_refine_injective :262`; `AR/TowerCollapse.lean:77 dial_tower` | `[PROVED]` names; tower `[VERIFIED(py)]` |
| P-11 | `SmoothSplit`: `m` is 5-smooth iff `m \| 144000^j`; lcm closing exponent; `Base60`: exact add and multiply, `1/7` has a period | `[SWEEP]` |
| P-12 | chain primes `18 * 10^k + 1` with chain squared `= 1 mod 360`; anchor classes mod 90 are `1, 19, 71, 89` (class 89 empty); 10 Cunningham doubling pairs `<= 24001`; Chebyshev `2x^2 - 1` hits `{2, 3, 4, 7, 11, 17, 49}` give 7, 17, 31, 97, 241, 577, 4801 | `[SWEEP]` |
| P-13 | witness list of `GT007` (finite recursive architecture kernel), 37 primes: 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97, 101, 151, 181, 193, 241, 251, 401, 577, 601, 631, 641, 701, 757, 761, 1009, 1201, 1801, 3601, 4801, 5041, 7201, 8001, 10009, 14401, 40321, 72001 (`GT007L19`..`L26`). Several entries are composite (`5041 = 71^2`, `7201 = 19 * 379`, `8001 = 3^2 * 7 * 127`, `40321 = 61 * 661`, `3601 = 13 * 277`, `72001 = 89 * 809`): six composites, 31 primes, so the list is witnesses of the architecture, not only primes `[VERIFIED(py)]` | `[PROVED GT007RecursivePrimeFractal]` `[SWEEP]` (list not re-opened; "37 primes" is a wrong label: 31 primes and 6 composites). P-12 anchor classes mod 90, Cunningham pairs and the P-4 `depth_seventy_one` remark were not testable (objects undefined) `[UNSURE]`. Further Lean names confirmed by grep in `AR/RequestProject/FractalPartition.lean`: `rings_in_register_iff :59`, `shared_spokes_card :76`, `codex_tower_nested :116`, `scrap_sequence_break :122`, `refinement_words_360 :181`, `ring_depths :201`, `depth_eq_refinement_length :220`, `hits_eq_card_divisors :272`, `level_profile_not_chain :290`, `coprime_zoom_iff_mod30 :309`, `totient_zoom :323`, `seven_breaks_zoom :338`, `depth_seventy_one`, `depth_257`, `depth_unbounded`; `window_hits_left AR/RequestProject/SignalDials.lean:67` |
| P-14 | `BG-019` fractal depth formula, `BG-024` theta formula, `BG-026` negative space (264 of 360 residues are non-units), `BG-010/016/030` temporal, `BG075` and `BG011` golden angle; `BG088` b-adic tower; 158 theorems in BG001..BG031 with no `sorry`; `GT-001..006` open | `[PROVED]` per sweeps |

Round-2 correction: `compression_framework.lean` is not fully proved: it still has 9 `sorry` (lines 49, 74, 107, 118, 119, 149, 187, 200, 236; the last one sits inside the `h_lossless` field that calls `losslessRNSEncoding`) `[VERIFIED grep]`.

Fractal addressing counts (information-theoretic reading `[DERIVED]`): `n` digits of a map set of `N` similarities with ratio `r` give `n log2 N` bits and resolve scale `\|r\|^n`; per decade of scale the cost is `D log2 10` bits, `D = log N / log(1/\|r\|)` (`D = 1`: 3.3219, `D = 2`: 6.6439, `D = 3`: 9.9658). This equals the metric entropy of a uniform `D`-dimensional source, so the address code is optimal only if the source is Haar-uniform on the attractor; otherwise the cost is the model-change penalty `D(q || p)` of section 21.4. It is base conversion, not compression. Examples `[VERIFIED(py)]`: sexagesimal IFS `x -> (x + d)/60` dimension 1; `n = 5` digits cost 29.5345 bits and resolve `1.2860e-9` (8.8908 decades, 3.3219 bits per decade); Gaussian flower `beta = 2 + i`, 5 digits: 5^m distinct level-`m` points for `m <= 6`, box-count slopes 1.44, 1.63, 1.79, 1.82, 1.85 (approach 2 slowly from below); Eisenstein `beta = 2 - w` (norm 7): 1.55, 1.70, 1.81, 1.85. The 144000 tower: 144000 points, 12 digits, 17.1357 bits; a finite tower has no dimension (it is a finite set); the inverse limit `Z_2 x Z_3 x Z_5` is not the cube `[0,1]^3`, and its dimension depends on the metric: under the ultrametric `60^{-v_60}` it is 1, under `max_p |.|_p` it is 3 (Haar measure of a radius-`r` ball is about `r^3`) `[VERIFIED(py)]` cylinder counts, `[DERIVED]` for 3 (section 23.7).

## 18. Constants, variables, and glossary

| Symbol | Value / meaning | Source |
| --- | --- | --- |
| `m_i`, `R`, `M = prod m_i` | pairwise-coprime moduli (rods), rod count, capacity | `tm_rods.h` |
| `TM_ROD_MAX` | 4096 rods; modulus `< 2^31`; saturation `TM_ROD_BOUND_SAT = 2^62`; `TM_MAX_MODULUS_COUNT = 128`, `TM_MAX_FORMULA_DEPTH = 13` in `tm_limits.h` (two different limits: check which header governs a given path) | `tm_rods.h`, `tm_limits.h` |
| capacity | 4096 largest primes `< 2^31`: 126975.878 bits; 3226 primes: 100005.924 bits; per-rod floor 122880 bits; packing fraction 0.9687 | `[MEASURED]` |
| Garner | `R(R-1)/2` mulmods (8,386,560 at `R = 4096`); SK base extension `3k + 2`; break-even by count `k ~ 7.5`, by timing about 6 | `[DERIVED]` |
| 360, 7200, 144000, 1008000 | dials `2^3 3^2 5`, `2^5 3^2 5^2`, `2^7 3^2 5^3`, `7 * 144000`; `phi` = 96, 1920, 38400, 230400 | section 15.3 |
| 60 | base of the scaled tower (`Z[1/30]`); `360 * 60^k`; `Omega(360 * 60^k) = 6 + 4k` | section 17 |
| 19, 361 | `19^2 = 361 = 1 mod 360`; `N_2 = 19 = N(5 + 2w)`; `F_361*` (field `GF(19^2)`) cyclic of order 360, while `(Z/361)*` is cyclic of order 342 | sections 15.1, 15.3 |
| 65520, 12, 2400 | `lcm`-closing modulus of `u^12 = 1`; exponent of `(Z/360)*`; exponent of `(Z/144000)*` | D-3 |
| 4/15, 8/35, 96, 264 | open fractions `phi(360 60^k)/(360 60^k)`, `phi(2520)/2520`; units and non-units mod 360 | P-6 |
| `N_k` | flower numbers `3k^2 + 3k + 1` | GEO-2 |
| `eps`, `eta` | `+1` iff `p = 1 mod 4`, `p = 1 mod 3` | H-1 |
| `pi = 5 + 2w` | prime of norm 19 | GEO-17 |
| golden | step 137508 milli-degrees on a 360000-dial; period 30000; `TM_GOLDEN_MILLI 2225` not derivable | D-7, D-8 |
| TCMP | header 24 B: `'TCMP'`, version, variant, transform, algorithm, `origLen` u64, FNV-1a-64 with non-standard seed; flags `PACKED = 1`, `ADAPTIVE_MODSET = 2`, `IMPLICIT_MODSET = 4`, `IMPLICIT_BLOCKLEN = 8`; `packed_residue_bits = 48` for a 40-bit payload, `carrier_floor_bits = 43` | section 6 |
| Pisot units | `2 + sqrt6`, `3 + 2 sqrt3`, `2 + sqrt3` | S-4 |
| `V = 1`, `Y = 5/4`, `G = 3/2`; `g_ii = log^2 p_i / p_i^2` | calculator and manifold documents | `[CLAIMED-UNMEASURED]` |

## 19. `Thesis/math/` design map (arbitrary-precision library built on the rods)

Sources: `Thesis/math/include/rods/*.h`, `MASTER_PLAN.md` sections 5, 19, 2260-2310; Aristotle `LIBRARY_REDESIGN.md`, `clib/`.

| Module (header) | Role | Cost class / formula |
| --- | --- | --- |
| `tm_rods.h` | frame of coprime rods, encode/decode, boundary state `{UNSIGNED_FIT, SIGNED_FIT, NEEDS_MORE_RODS, INVALID}`, op kinds `{CONST, COPY, ADD, SUB, MUL, POW, MULC, ADDC}` | `RLOCAL_O1`: add, sub, mul `O(R)`; `RLOCAL_OLOGN`: pow `<= R (2 floor(log2 e) + 1)`; `FRAME_OR`; `BOUNDARY_OR2`: Garner `R(R-1)/2`; `ORACLE_POSITIONAL` |
| bound propagation | ADD/SUB `l' = max(l_a, l_b) + 1`; MUL `l' = l_a + l_b`; MULC `l' = l + ceil(log2 \|c\|)`; POW `l' = e l`; sum of `N` terms `l + ceil(log2 N)`; capacity law `l + 1 <= capacity_bits` | `tm_rods.h` |
| `tm_rod_series.h` | `ARITH`: `n a + d C(n, 2)`; `GEOM`: `a (r^n - 1)/(r - 1)`, or the matrix `[[r, 1], [0, 1]]^n` when `gcd(r - 1, q) != 1`; `FAULHABER` `p = 1..4` in the plan (`D_p in {2, 6, 4, 30}`), header allows `p <= 14`; `POLY`: `sum b_j C(n, j+1)`; `LINREC`: `s_N = C^N s_0`, `d <= 8` in the plan, 16 in the header; `PROD_GEOM`: `r^{n(n+1)/2}`; `MATPOW`; `tm_rod_series_shell_cumulative`, `tm_rod_series_square_sum` | `LINREC`: `2 d^3 floor(log2 N)` rod ops per rod |
| other headers | `tm_rod_batch_parallel.h`, `tm_rod_relation.h`, `tm_rod_matpow.h`, `tm_quad.h` (quadratic rings), `tm_polarity.h` (Gaussian), `tm_rat.h`, `tm_real.h`, `tm_kissing.h`, `tm_rod_sieve.h`, `tm_nat.h`, `tm_gnomon.h`, `tm_error_catalog.h` | - |
| Garner | `x = v_0 + m_0 (v_1 + m_1 (...))`; positional output only; `owner decision D3: accept Garner as output-only` | `BOUNDARY_OR2` |
| gates | `G-CX` (op-count scaling: add/sub/mul exactly `R`; ARITH, FAULHABER, GEO-1, GEO-3 equal at `n = 10^3` and `10^18`; LINREC/GEOM ratio `<= 7`), `G-DIFF`, `G-SYM`, `G-DB` | `MASTER_PLAN.md:2422` |
| owner decisions | `D1` modulus policy (primes for capacity, structured `{2^a, 3^b, 5^c}` for the dial, merge when coprime); `D2` port the `clib` behind `tm_` names; `D3` Garner output-only; `D4` RANGE error on overflow; `D6` phase check widened; `D7` stale pointer; `D8` reserve daemon ports | `MASTER_PLAN.md:2510-2522` |
| conflicts | `CONFLICT-001` shell `6n` vs `10n^2 + 2`; `CONFLICT-004` PQ ellipse `a = q/2` vs `(q+1)/2`; `CONFLICT-002` golden constant | `MASTER_PLAN.md:2510-2513` |
| gaps | no `p^k` rods, no moduli `>= 2^31` (one machine word per rod), no depth vectors, no serialisation, no prefix chains, no generic formula evaluator, no tower operations (B04c) | `LIBRARY_REDESIGN.md` |

Aristotle `clib` (to be ported behind `tm_`): `lc_abacus_*` (encode; decode by Garner with a re-encode check; run; `linrec` `d <= 8`), `lc_rns_*`, `lc_mersenne_mod`, `lc_rotl` (doubling mod `2^w - 1`), `LC_DIAL12 = 65520` split `(x mod 16, x mod 4095)`, `lc_int_order_split`, `lc_int_qtok`, `lc_int_check_lucas_pow`, `lc_rodsieve_cert/find/verify` (at most 32 rods), `lc_eis`, `lc_hexbase`, `lc_dial_order`, `lc_dial_sqrt_one`. Benchmarks `[MEASURED]`: `sqrt 3` to 100,000 decimals 335 ms on rods vs 8327 ms Garner; order split of 2112 / 4096 / 8192-bit numbers 0.88 / 5.81 / 24.07 s; 19-flower 116 ms; 124-circle shells 31.45 s; vertex about 2 ns vs 13 ns trigonometric.

Compression-relevant design consequences: (a) deepening by merging a coprime prime-power rod is the library form of the tower; the `p^k` gap is the main missing piece; (b) `LINREC`/`GEOM`/`FAULHABER` are the descriptor families of recipe R10 and give `O(log N)` jumps to term `N`; (c) the proposed circle exponent and unit-vector coordinates (R4, R5) need discrete-log and invariant-factor tables that no module has yet.

## 20. Measured evidence collected in one place

All `[MEASURED]`; logs are under `/tmp` (`geofs_*`) and ephemeral; rerun the named scripts before quoting.

- TCMP: text 64 KiB..8 MiB ratio about 0.394; JSON 0.210; random 1.000 (+24 B); 32 MiB zeros 65:1 (419.5 ms compress, 360 ms decompress); compress 3.5-4.3 MB/s, decompress 60-77 MB/s. Max RLE expansion 65:1; max LZ77 43.7:1 (`Thesis/research/geofs/batch2_devops.md`, which also treats the CRIME/BREACH compression-oracle threat: compress-then-encrypt leaks length).
- RNS cell: `c = 8`, `B = 30`: encode 172.8 ns/op (173.6 MB/s), decode 130 ns/op (230.8 MB/s); `c = 1`, `B = 3`: 18.8 / 32.6 ns; `c = 32`, `B = 123`: 1592.7 / 1900.9 ns; `c = 64`, `B = 247`: 8093.9 / 10328.6 ns; Barrett Garner digits 720 MB/s at `c = 4`. WASM numbers disagree (0.28-2.62 us).
- Shenoy-Kumaresan operation counts: `k = 8`: 24 vs 36; `k = 32`: 96 vs 528; `k = 128`: 384 vs 8256; `k = 4096`: 683 times fewer. Convention note: this geofs count uses `3k` against `k(k+1)/2`; section 2 uses `3k + 2` against `k(k-1)/2` (26 vs 28 at `k = 8`). The break-even differs by about 1 between the two; the section-2 convention is the one used in section 18.
- Composite moduli beat primes at equal rod count: (29, 30) = 870 > 667; (27, 28, 29) = 21924 > 12673; (23, 25, 27, 28, 29) = 12,606,300 > 2,800,733. Collision probability 0.0767 at `n = 4096`. Set-partition (Bell) splits of `omega(n)` verified 1874 / 1874. Redundant rods with `r >= c - 1` give zero silent tears (`SYNTHESIS.md`); quorum read.
- Refuted in `/tmp/geofs_devops_claims_1.txt`: "144000 has 48 divisors" (it has 96); `qToKBijection_complete` is unsatisfiable; "byte read needs `O(k^2)` Garner".
- Research variants V6-V10 live in `Thesis/math/tests/unit/test_compression_runtime.c` and `tests/research/test_research_compression.c`; the actual code does CRT residue packing with adaptive modset selection and a nibble permutation for SIC; no real lattice or harmonic transform exists in the code for the `hdc`, `lbc`, `fhc` aliases `[CLAIMED]` geometry only.
- Probe scripts: `/tmp/daemon_probe.py`, `/tmp/geofs_b3info3_speed.mjs`, `/tmp/compression_prod_test.mjs`, `/tmp/calc_probe.py`; `/tmp/thesis_formulas_compact.txt` (Lean declaration list), `/tmp/projection-chart-interpretations.md`; `/tmp/tcmp_interop.log` is stale; `/tmp/thesis_update_summary.md` is truncated.

## 21. What the geometry buys, and what it cannot

Corrected view after round 2. The residue geometry is not only decoration: it supplies exact set sizes (code lengths), exact group laws (arithmetic coordinates), symmetry quotients, scale-addressing, and sparse spectra. It cannot reduce the information in data that is uniform on the full range. Both statements are theorems or verified calculations below.

| Geometry fact | Exact consequence | Cost formula | Holds only if |
| --- | --- | --- | --- |
| Hex ball size `1 + 3R(R+1)` | enumerative code, `O(1)` rank | `log2(1 + 3R(R+1))` | points are promised in the ball; saves `log2(4/3)` vs the coordinate box |
| Shell `6n`, `D6` orbits `1 + floor(n/2)` | shell index + ring index; orbit quotient | `H(n) + log2 6n`; the orbit quotient removes at most `log2 12` bits per point | radial concentration (Gaussian-like) |
| Flower digits `beta_k` | scale-truncatable address | `n log2 N_k` | multiscale access is wanted; not shorter |
| Circle/hex group cyclic of order `p^{j-1}(p - eta)` | exponent coordinate; mul = add | `log2(p^{j-1}(p - eta))` | the point is promised on the circle; same size as `(x, sign)`; arithmetic benefit only |
| `(Z/m)*` invariants | unit vector | `sum ceil(log2 d_i)` | input promised coprime to `m` |
| Reduced residues mod `W` | wheel rank | `log2(W/phi(W))` saved | input promised coprime to `W` |
| CRT separability | sparse Fourier support | `sum m_i - (k-1)` values | the signal is additive over rods |
| Short generator rule | descriptor | `O(d)` words | the sequence really is `ARITH`/`GEOM`/`LINREC`... |
| Divisor lattice, `hits = tau(20/e_0)` | partition index of a spoke/ring | `log2 96 = 6.585` per divisor, `log2 60` per refinement path | the object is promised a divisor of 144000 |

Statements with proofs or computations (all `[STANDARD]` unless noted):

1. Counting: an injective `f: {0,1}^n -> {0,1}^*` has fewer than `2^{n-k+1}` codewords of length `<= n - k`; under the uniform distribution the mean length is at least `n - 2 + (n + 2)/2^n` (brute-force check at `n = 8`: 6.0390625 both ways). Prefix-free codes (Kraft): at most `2^{n-k}` strings with length `<= n - k`. The bound for one-to-one codes ignores delimiters; a stream of such codewords needs side information of order `log2 n`.
2. Incompressibility: for plain complexity `C`, `#{x : C(x) < n - k} < 2^{n-k}` (fraction `< 2^{-k}`). Invariance: `\|K_U - K_V\| <= c_{UV}`. `K` is upper semicomputable and not computable.
3. Bijection: `H(f(X)) = H(X)` for any bijection `f`, and `K(f(x)) = K(x) +- K(f) +- O(1)` for computable `f` with computable inverse `[DERIVED]`. The RNS column is such a bijection (section 1).
4. Model change: a model `p` yields `-log2 p(x)` bits (arithmetic coding within +2). `x` gains over `n` raw bits iff `p(x) > 2^{-n}`; since `sum p = 1`, fewer than `2^n` elements can exceed that, so mass moves, it does not appear. Expected cost under the true source `q` is `H(q) + D(q \|\| p)`.
5. Probabilities that an integer uniform on `[2^{n-1}, 2^n)` lies in a structured class `[VERIFIED(py)]` (exact for `n <= 24`, asymptotic estimates `~` beyond): coprime to 360: 0.2656 (`n = 8`), 0.2667 (`n = 16, 24`), `-> 4/15`; 5-smooth: 0.109, 1.3e-3, 1.1e-5, 7.3e-8 (`n = 32`), 6.4e-17 (`n = 64`); 7-smooth: 0.188, 3.5e-3, 3.9e-5, 3.3e-7, 5.3e-16; `a^2 + b^2`: 0.336, 0.236, 0.1905, 0.162, 0.115; `a^2 - ab + b^2`: 0.281, 0.197, 0.159, 0.136, 0.096; prime: 0.180, 0.0925, 0.0612, 0.045, 0.0225; all prime factors `= 1 mod 3`: 0.117, 0.087, 0.072, 0.064, 0.045; `p - 1 \| 144000`: 0.039 at `n = 8`, then 0 (exactly 38 primes, the largest 24001). Every class is either about 4/15 (1.9 bits under a promise) or vanishing: a rod prior does not help generic data.
6. Sparse-set counts below `N` `[VERIFIED(py)]` `N = 10^4, 10^5, 10^6, 10^7`: `a^2 + b^2`: 2749, 24028, 216341, 1985459 (count `sqrt(ln N)/N` falls 0.834, 0.815, 0.804, 0.797 toward Landau-Ramanujan `C = 0.7642`); `a^2 - ab + b^2`: 2299, 20091, 180874, 1659711; 5-smooth: 175, 313, 507, 768; 7-smooth: 338, 694, 1273, 2155; all primes `= 1 mod 3`: 985, 8814, 80587, 746922 (flat constant about 0.300). The smooth-count leading term `(ln N)^3 / (6 ln2 ln3 ln5)` is 26% off at `10^7` (569.4 vs 768); the shifted form `(ln N + (1/2) sum ln p)^k / (k! prod ln p)` gives 769.4 (5-smooth) and 2178.6 (7-smooth, exact 2155). Bits per member at `log2 N = 23.25`: 20.92 (`a^2 + b^2`), 20.66 (hex norms), 9.58 (5-smooth), 11.07 (7-smooth), 5.25 (`p - 1 \| 144000`), 19.51 (primes `= 1 mod 3`).
7. Descriptor-first: lossless iff each family decoder is deterministic and total, the codec verifies `decode(params) = data` before choosing, and tags are prefix-free; worst case `n + c`; descriptor length is an upper bound on `K(x)` only.

New experiments (all `[DESIGN]`, same decision rule as section 10):

| # | Test | Baseline | Pass |
| --- | --- | --- | --- |
| E6 | hex walk with Gaussian steps: shell code + ring index vs two-coordinate delta + xz | xz, order-0 arithmetic | within 0.1 bit of entropy; no gain on a uniform-in-bounding-box control |
| E7 | multiplication-heavy loop (`x -> g^e` products) in index form vs residue form over 31-bit prime rods | `tm_` mul | time and op count; Zech table cost reported |
| E8 | prime list to `10^7` with wheel 30030 + Rice vs xz on 4-byte gaps | xz -9e, zstd absent | at most 1.9 Mbit and exact round trip |
| E9 | CRT-additive periodic data with periods (7, 11, 13), 4096 samples, noise-free and 1-bit noise | xz | noise-free at most `sum m_i` words; noisy falls back |
| E10 | `Z[w]/p^j` point coding by exponent vs `(x, sign)` for `p = 19, j = 3` | residue pair | equal size expected (13 vs about 13 bits); report arithmetic speed only |

## 22. Round-2 review status and corrections ledger

Done in round 2: R1 (topic fan-out: geometry, fractal partitions, math library, root compression documents, `/tmp`, Lean catalogue, proofs and ontology, support and web), R2 (related terms: quadratic/polytope, waves/Farey, `clib`, temporal/witness/totient, signal/harmonic), R3 (compression re-sweep), R4 (second `/tmp` pass), and four mathematician passes (group theory and `p`-adic structure; combinatorics and lattice geometry; analytic number theory and harmonic analysis; information, coding and fractal theory). Their computed results are in sections 15, 16, 17, 21.

Done in round 3: R5 (Lean and file-line citation verification, two independent verifiers plus my own grep), R6 (five multi-branch mathematician reviews: number theory; algebraic geometry and p-adic; combinatorics and coding; harmonic analysis and signals; fractals, dynamics, information) and two repository gap finders. Their results are merged into sections 15-21 (corrections) and section 23 (new formulas); the round-3 ledger is section 24.

New corrections found in round 2:

| Claim | Where | Truth |
| --- | --- | --- |
| hex distance `max(\|a\|, \|b\|, \|a + b\|)` | convention ambiguity | correct form for `a^2 - ab + b^2` is `\|a - b\|` `[VERIFIED(py)]` |
| first-`k`-primes capacity 23.9, 32.8, 39.2, 57.0, 85.0 bits for `k` = 8, 12, 16, 24, 32 | `COPRIME_COMPRESSION_FIVE_VARIANTS.md` | 23.21, 42.75, 64.82, 114.19, 168.49 bits |
| `P_7 = 9,699,690` is 23.9 bits | FHC files | 23.21 bits |
| 30 B payload in 36 B is 1.0667 | earlier note | 1.2 (`r = 1`); 1.0667 is `r = 0` aligned |
| "`x mod m_1` is a function of `x mod m_1 m_2` only when divisible" | informal | always a function; what fails for coprime moduli is a value-interval prefix |
| `144000 = 360 * 60^k` | informal | `144000 = 360 * 400`; `360 * 60^k` is 360, 21600, 1,296,000, ... |
| `(Z/360)* = C2 x C2 x C2 x C6` | guess | order 48; true group `C2 x C2 x C2 x C12` |
| exponent 12 for the 144000-dial | informal | `lambda(144000) = 2400`; exponent 12 is the 360-dial |
| sphere formula `p^{2k-1} - eps^k p^{k-1}` for all `c` | docs | only for `c` a unit mod `p` |
| Hensel fibre size `p` | docs | only at smooth points (`c` unit, `p` odd) |
| `p = 3` hex circle count `p^{j-1}(p - eta)` | docs | `2 * 3^j`, group `Z/2 x Z/3 x Z/3^{j-1}` (not cyclic) |
| `compression_framework.lean` proved | one sweep agent | 9 `sorry` `[VERIFIED grep]` |
| `beta_k = cube root(k N_k)` | one sweep agent | unsupported; `beta_k = (2k+1) + k w` |
| Soddy `u_n` has a rounding closed form | informal | three real roots, one with modulus above 1: no rounding shortcut |
| smooth count `(ln N)^3 / (6 ln2 ln3 ln5)` | docs | 26% low at `N = 10^7`; use the shifted form |
| `TM_GOLDEN_MILLI = 2225` realises the golden step | `tm_angle_wrap.c` | not derivable (period 1200 on a 30000-dial) |

Citation check state: file-line anchors `MASTER_PLAN.md:2300`, `:2304`, `:2307`, `:2310`, `:2311`, `:2510`, `:2513`, `:2422` and the 9 `sorry` lines of `compression_framework.lean` were re-opened by grep on 2026-10-11. Lean theorem names tagged `[SWEEP]` are reported by sweep agents; the R5 verification (see below) checks them by grep.

Open at the end of round 2:
1. Lean names tagged `[SWEEP]` not yet grepped one by one (R5 below).
2. General (non-sampled) proofs: flower address termination, boundary dimension pattern `rho = 2k + 1`, tile measure 1, `Z[i]` mod `2^j` structure, `Z[w]` mod `2^j` 2-part, `D4`/`E8` within-shell rank.
3. Meaning of `TM_GOLDEN_MILLI = 2225`; the geometric meaning of the Soddy sequence `u_n`.
4. No measured test of any `hdc`/`lbc`/`fhc` geometry in code; no real-data test that coprime-wave structure occurs (section 10, item 8).
5. Experiments E1-E10 are unrun.
