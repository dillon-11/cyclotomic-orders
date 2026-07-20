# Cyclotomic values at integer bases: Mersenne, Fermat, repunit, Wieferich

Sorry-free Lean 4 proofs unifying the classical prime families as **cyclotomic
values at integer bases**. Mersenne numbers are `Φ_p(2)` at prime index, Fermat
numbers are `Φ_{2^(k+1)}(2)` at 2-power index, repunits are the base-10 row —
and the factor arithmetic of all of them is one law.

Three headline theorems, stated Mathlib-only in
[`Challenge.lean`](Challenge.lean):

1. **The master order theorem** (`cyclotomic_primeFactor_orderOf`): a prime
   `q` dividing `Φ_n(a)` with `q ∤ n` has `a` of multiplicative order
   **exactly `n`** modulo `q` — hence `q ≡ 1 (mod n)`. This is the
   general-index law behind every classical divisibility pattern in these
   families.
2. **The Mersenne congruence** (`mersenne_primeFactor_two_mul`): every prime
   factor of `2^p − 1` (`p` an odd prime) is `≡ 1 (mod 2p)` — the Mersenne
   analogue of Mathlib's Fermat-number congruence, explaining
   `2¹¹ − 1 = 23 · 89` (23 = 2·11 + 1, 89 = 8·11 + 1). At the time of
   writing Mathlib carries the Fermat-number congruence but not this one.
3. **The order-lift dichotomy** (`orderOf_lift_dichotomy`):
   `ord_{p²}(a) ∈ {ord_p(a), p · ord_p(a)}`. The non-lift branch **is** the
   Wieferich condition — squared prime factors of cyclotomic values are
   exactly order-lift failures.

## Repository layout

| File | Contents |
| --- | --- |
| `Challenge.lean` | the trusted claim statements (Mathlib imports only, nine `sorry` placeholders) |
| `CyclotomicOrders.lean` | root module importing the library |
| [`MasterOrder.lean`](CyclotomicOrders/MasterOrder.lean) | the master order theorem: `q ∣ Φ_n(a)`, `q ∤ n` ⟹ `ord_q(a) = n` ⟹ `n ∣ q − 1`, via Mathlib's `isRoot_cyclotomic_iff` (primitive-root characterization of cyclotomic roots) |
| [`BaseTwo.lean`](CyclotomicOrders/BaseTwo.lean) | the base-2 row: `2^p − 1 = Φ_p(2)`, Fermat numbers `= Φ_{2^(k+1)}(2)`, the full factorization `2^n − 1 = ∏_{d ∣ n} Φ_d(2)`, and the Pierce-sequence product form |
| [`BaseCongruence.lean`](CyclotomicOrders/BaseCongruence.lean) | the general-base congruences: prime factors of `(a^p − 1)/(a − 1)` at prime index have order `p` and are `≡ 1 (mod p)`; instantiated for the Mersenne (base 2) and repunit (base 10) rows |
| [`MersenneCongruence.lean`](CyclotomicOrders/MersenneCongruence.lean) | the sharpened Mersenne form: factors are `≡ 1 (mod 2p)` (the extra factor of 2 because `q` is odd), matching Euler's classical statement |
| [`Wieferich.lean`](CyclotomicOrders/Wieferich.lean) | `IsWieferich` defined; the equivalence with the Fermat-quotient form; the **order-lift dichotomy** `ord_{p²}(a) ∈ {ord_p(a), p·ord_p(a)}`; non-instances 2, 3 decided |
| [`PierceSequence.lean`](CyclotomicOrders/PierceSequence.lean) | the Pierce sequence: `log ∏_ρ \|ρ^n − 1\|` pinned in a window around `n · log M(p)` — the growth of the whole cyclotomic-value column is governed by the Mahler measure |
| [`CyclotomicRepulsion.lean`](CyclotomicOrders/CyclotomicRepulsion.lean) | the analytic floor under the Pierce sequence: `∏ \|ρ^n − 1\| ≥ 1` for monic integer polynomials under the no-root-of-unity hypothesis |
| [`MersenneSquare.lean`](CyclotomicOrders/MersenneSquare.lean) | **the square-factor exclusion** (v0.1.1): a squared prime factor of `2^p − 1` (p prime) is a base-2 Wieferich prime; general index: `q² ∣ 2ⁿ − 1` forces `q` Wieferich or `q·ord_q(2) ∣ n` |
| [`WallSunSun.lean`](CyclotomicOrders/WallSunSun.lean) | **the Fibonacci-unit analogue** (v0.1.1): `IsWallSunSun` defined and decidable via the rank index `p − (5/p)`; the rank-of-apparition sanity and the below-100 null, both kernel-decided |
| [`ParityLadder.lean`](CyclotomicOrders/ParityLadder.lean) | **the parity-tower law** (v0.1.2): harmonic ladders `H^(r)_m` over `ZMod p` — mirror symmetry, parity selection rule, recurrence-defined Bernoulli numbers with Faulhaber proven formally (von Staudt–Clausen never enters), the ladder–Bernoulli coupling `(p−r)·H^(r)_m = B_{p−r}(m+1) − B_{p−r}`, the full χ-projection law with conjugate-character Euler factor, and the golden (2/5) and silver (1/4) Glaisher bands in Bernoulli closed form |
| [`Mahler.lean`](CyclotomicOrders/Mahler.lean) | the Mahler-measure frame the Pierce sequence sits over: Lehmer's polynomial as the E₁₀ Coxeter characteristic polynomial (kernel-decided: annihilation, trace −1, det 1, Lorentzian signature), the monic floor `1 ≤ M(p)`, and Lehmer's problem as a *defined* `Prop` (never axiomatized) |

The library is sorry-free with axiom footprint exactly
`[propext, Classical.choice, Quot.sound]`. The only `sorry`s in the repository
are the intentional placeholders in `Challenge.lean`.

**Not claimed:** no Wieferich-prime *search* results, tallies, or completeness
statements live in this repository — it is the lemma layer under those
searches. Lehmer's problem appears only as a defined hypothesis `Prop`, never
assumed.

## Why these lemmas are worth extracting

- The master order theorem is the single statement from which the classical
  congruences (Euler on Mersenne factors, the Fermat-number congruence,
  repunit factor congruences) fall out as one-line instantiations — the
  repository derives each row from it.
- The order-lift dichotomy is the entire local theory of squared prime
  factors: for `q ∤ n`, `q² ∣ Φ_n(a)` exactly when the order of `a` fails to
  grow from `q` to `q²`. Every "Wieferich-like" condition in the literature
  (base-`a` Wieferich, Fibonacci–Wieferich, …) is the non-lift branch at a
  different unit.
- The Pierce sequence is the bridge from this algebraic layer to Lehmer's
  problem: the Mahler measure is exactly the exponential growth rate of the
  cyclotomic values.

## Companion repositories

The order and parity machinery here is used by
[`wieferich-families`](https://github.com/dillon-11/wieferich-families) (the paper repository: its §2.2 reads the Wall–Sun–Sun condition as the
vanishing of a harmonic band, citing this repository's Glaisher layer);
[`salem-tower`](https://github.com/dillon-11/salem-tower) carries the graded
prime towers over the same cyclotomic values; [`lehmer-e10`](https://github.com/dillon-11/lehmer-E10) proves
irreducibility of Lehmer's polynomial and the E₁₀ Coxeter identity.
Every repository builds against Mathlib only — no cross-repo
dependencies, by design: shared lemmas are duplicated or headed to
Mathlib.

## Verifying the proofs with comparator

You do not need to read the proof library to check the claims. Inspect
`Challenge.lean` (the trust surface, Mathlib imports only), then verify
mechanically with [comparator](https://github.com/leanprover/comparator),
which checks that each named theorem proves *exactly* the statement in
`Challenge.lean`, uses only the permitted axioms, and is accepted by the Lean
kernel:

```bash
# toolchain
elan toolchain install leanprover/lean4:v4.32.0-rc1

# tools (see https://github.com/leanprover/comparator for pinned setup)
git clone https://github.com/leanprover/comparator && (cd comparator && lake build comparator)
git clone https://github.com/leanprover/lean4export && (cd lean4export && lake build)
git clone https://github.com/Zouuup/landrun && (cd landrun && go build -o landrun cmd/landrun/main.go)   # Linux sandbox

# this repository
lake exe cache get   # fetch Mathlib build cache
lake build           # builds Challenge (sorry warnings, intentional) and CyclotomicOrders
lake env path/to/comparator/.lake/build/bin/comparator config.json
```

On systems without kernel-level sandbox support, use comparator's development
shim:

```bash
COMPARATOR_LANDRUN=path/to/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=path/to/lean4export/.lake/build/bin/lean4export \
lake env path/to/comparator/.lake/build/bin/comparator config.json
```

Expected output: `Your solution is okay!`

## Provenance

Three contributors: the human author (direction, judgment, review);
Claude (Anthropic) — reasoning, implementation, Lean formalization; and a
research harness enforcing preregistration, control-first experiments, and
independent re-computation. Trust none of them: every claim is
kernel-checked or re-computable in one command. Machine-readable
metadata: `formalization.yaml`.

## License

Apache-2.0.
