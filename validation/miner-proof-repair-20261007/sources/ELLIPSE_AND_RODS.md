# The pq ellipse as a search bound, and rods added by coprimality

This note covers two proposals:

1. The ellipse built from `p` and `q` should fix scale and volume straight away. The minimum and
   maximum of its oscillation are then the bounds of the calculation, and they show which
   fractal partition the number belongs to.
2. Once an abacus of prime rods is loaded, with a given volume, primes inside that volume can be
   found in constant time. Rods can be added as needed, chosen by coprimality.

Everything here is public mathematics, written to be read and checked by anyone. The statements
are about the numbers themselves (the ellipse, the rods, the counts), not about any particular
display or file format.

The proofs are in `RequestProject/EllipseSearch.lean` and `RequestProject/DynamicRods.lean`.
Both build with no `sorry` and use only Lean's standard axioms. The two finite checks
(`rods19`, `window19`) are run by the kernel, without `native_decide`.

---

## 1. The ellipse: what its bounds determine

The ellipse is the corrected chart from earlier work. Its semi-major axis is `a = q/2`, its focal
half-distance is `c = p/2`, `b² = (q² − p²)/4`, and its eccentricity is `e = p/q`.

### 1.1 The oscillation and its two bounds

Measured from a focus, the distance to the ellipse is `r(θ) = (b²/a)/(1 + e cos θ)`. It swings
between

* `rMin = a − c = (q − p)/2` at `θ = 0`, and
* `rMax = a + c = (q + p)/2` at `θ = π`.

(`focalRadius_zero`, `focalRadius_pi`, `focalRadius_bounds`)

These two numbers carry all the information in the pair `p, q`:

| relation | Lean |
|---|---|
| `rMax + rMin = q` | `bounds_sum` |
| `rMax − rMin = p` | `bounds_diff` |
| `rMin · rMax = b²` | `bounds_mul` |
| `rMax² − rMin² = p·q = n` | `bounds_sq_sub` |

So the minimum and maximum of the oscillation really are the bounds of the calculation. Their
difference is the smaller factor, their sum is the larger factor, and the difference of their
squares is `n`.

### 1.2 Scale and volume

* **Area fixes the ellipse.** With `A = π a b`, we have `q⁴ = n² + (4A/π)²` (`area_sq`). Two pq
  ellipses with the same `n` and the same area are the same ellipse (`area_determines`).
* **Eccentricity fixes the scale.** `p² = n·e` and `q² = n/e` (`ecc_scale`). So if `e` is known
  to lie in a band `e₁ ≤ e ≤ e₂`, then `p` lies in `[√(n e₁), √(n e₂)]` (`ecc_band`). The search
  space shrinks to exactly that interval.
* **Fermat's search is bounded by the ellipse.** From `n` alone we know `rMax ≥ √n`. The gap
  `rMax − √n` is at most `rMin²/(2√n)` (`fermat_gap`). A nearly round ellipse (small `e`, so `p`
  close to `q`) is therefore found almost immediately by stepping `rMax` up from `√n`.

### 1.3 Which fractal partition

In earlier work the fractal partition of an `n`-dial was identified with its divisor lattice:
the rings are the divisors of `n` (`FRACTAL_PARTITIONS.md`).

* Every way of writing `n = X² − Y²` comes from a ring of the `n`-dial: `X − Y` divides `n`, and
  `(X − Y)(X + Y) = n` (`fermat_pair_divisor`).
* For odd primes `p < q` there are exactly two such ways (`fermat_pairs_pq`):
  - the trivial one, `((n+1)/2, (n−1)/2)`, which comes from the 1-ring;
  - the ellipse's own pair `(rMax, rMin)`, which comes from the `p`-ring and the `q`-ring.
* The two bounds are coprime integers (`intBounds`, `intBounds_coprime`).

So the two bounds of the oscillation pick out exactly the one non-trivial partition of the
pq-dial. Example: for `3439 = 19·181` the bounds are `81` and `100`, and `100² − 81² = 3439`
(`nineteen_bounds`).

### 1.4 The limit, stated plainly

The ellipse is built from `p` and `q`. Knowing its area, its eccentricity or its two bounds is
therefore the same information as knowing `p` and `q`: each quantity is a reparametrisation of
the others, and the theorems above give the exact conversions. The geometry turns *partial*
knowledge into a smaller search: an eccentricity band gives an interval for `p` (`ecc_band`),
and roundness gives a short Fermat search (`fermat_gap`). Nothing here recovers the ellipse from
`n` alone. Doing that would factor `n`, and no fast general method for that is known.

---

## 2. Prime rods, the coprime window, and adding rods

The abacus is the library's `LatticeCalc.Abacus`, a list of rods. A number *passes* when its
reading is nonzero on every rod. `primeRods r` has one rod for each prime below `r`.

### 2.1 Coprimality picks the next rod

* For **any** modulus `M`, the least `m > 1` coprime to `M` is prime (`least_coprime_prime`). A
  rod chosen by coprimality is therefore always a prime.
* For a prime `r`, the abacus names its own next rod: `r` is the least number `> 1` that passes
  `primeRods r` (`next_rod`).

### 2.2 The volume, and the next prime set

* **The window** (`window`). For `1 < x < r²`, `x` passes `primeRods r` exactly when `x` is a
  prime `≥ r`. Inside the volume `r²`, the coprime positions *are* the next prime set.
* **The window is sharp** (`window_sharp`). `r²` passes but is not prime, so the volume cannot be
  pushed past `r²` without a new rod.
* **Example** (`rods19`, `window19`, checked by the kernel). The seven rods `2, 3, 5, 7, 11, 13, 17`
  pick out exactly the 65 primes in `[19, 361)`.

### 2.3 Adding rods dynamically

* **Next rod** (`add_rod`). If `s` is the next prime after `r`, then `primeRods s` is
  `primeRods r` with the single rod `r` appended. The window grows from `r²` to `s²`.
* **General extension** (`extend_pairwise`, `extend_capacity`, `extendEquiv`). Appending any rod
  coprime to the current capacity keeps the rods pairwise coprime and multiplies the capacity. It
  also splits the arithmetic as a ring isomorphism
  `ℤ/(capacity·p) ≅ ℤ/capacity × ℤ/p`, so the existing rods are left untouched.

This is the scaling mechanism you described: the rod to add is found by coprimality, adding it
never disturbs the existing rods, and each new rod enlarges the certified volume.

### 2.4 In what sense the cost is constant

* **Proved.** Checking a number inspects each rod exactly once. The number of checks equals the
  number of rods, whatever the number being checked (`passCount_snd`, `passCount_fst`). For a
  loaded `primeRods r`, whether any `x` in the volume `r²` is prime is therefore settled by a
  fixed number of rod checks, one per prime below `r`. That number depends on the abacus, not on
  `x`. In that precise sense the decision is O(1) with respect to the query inside the loaded
  volume.
* **Proved limit 1** (`no_finite_abacus`). No finite abacus decides primality for every `x > 1`.
* **Proved limit 2** (`rods_needed`). Suppose an abacus with no rod of size 1 answers correctly on
  a window `[L, V)`. Then it has at least as many rods as there are primes `p` with `L ≤ p² < V`.
  This is a statement about the abacus itself, not about storage or output. The number of rods,
  and so the number of checks, must grow with the volume.
* **Finding the next prime** after a given `x` inside the volume means stepping to the next
  passing position, so it costs one rod check per position times the length of the prime gap.
  Inside a fixed volume the gaps are bounded, so this is also a constant *for that abacus*. Prime
  gaps are unbounded as the volume grows. That is a standard fact, but it is not formalized here.

**Summary.** The claim holds exactly in this form: *for a loaded abacus, deciding or locating
primes inside its volume takes a number of rod operations fixed by the abacus alone.* It fails in
the stronger form *one constant for every volume*: the rod count must grow at least like the
number of primes below `√V`. Dynamic rod addition by coprimality (§2.3) is the correct way to
grow it.

---

## 3. Joining the two halves

`factor_on_rods`: if `n = p·q` with primes `p ≤ q` and `n < r²`, then `p` is one of the rods of
`primeRods r`, and `n` reads zero on that rod. The ellipse gives `p = rMax − rMin`, and the
abacus of volume `n` already holds that rod. The ellipse's bounds say *which* rod reads zero,
and an eccentricity band (`ecc_band`) says which interval of rods to look at.
