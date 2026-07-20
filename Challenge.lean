/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
/-
  Challenge: cyclotomic values at integer bases — three headline theorems,
  stated Mathlib-only.

  1. `cyclotomic_primeFactor_orderOf` (the master order theorem): a prime `q`
     dividing `Φ_n(a)` with `q ∤ n` has `a` of multiplicative order exactly
     `n` modulo `q` — the general-index law behind the factor arithmetic of
     the classical prime families.

  2. `mersenne_primeFactor_two_mul` (the Mersenne congruence): every prime
     factor of `2^p − 1` (p an odd prime) is `≡ 1 (mod 2p)` — the Mersenne
     analogue of Mathlib's Fermat-number congruence, explaining
     `2¹¹ − 1 = 23 · 89` (23 = 2·11+1, 89 = 8·11+1).

  3. `orderOf_lift_dichotomy`: for a prime `p` and `a` coprime to `p`, the
     multiplicative order of `a` modulo `p²` equals its order modulo `p` or
     `p` times it — the non-lift branch is the Wieferich condition.
-/
import Mathlib

open Polynomial

/-- The master order theorem: `q ∣ Φ_n(a)`, `q ∤ n` ⟹ `ord_q(a) = n`. -/
theorem cyclotomic_primeFactor_orderOf {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    orderOf ((a : ZMod q)) = n := sorry

/-- The Mersenne congruence: a prime factor of `2^p − 1` (p an odd prime) is
    `≡ 1 (mod 2p)`. -/
theorem mersenne_primeFactor_two_mul {p q : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1) : 2 * p ∣ q - 1 := sorry

/-- The order-lift dichotomy: `ord_{p²}(a) ∈ {ord_p(a), p · ord_p(a)}`. -/
theorem orderOf_lift_dichotomy {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    orderOf ((a : ZMod (p ^ 2))) = orderOf ((a : ZMod p)) ∨
      orderOf ((a : ZMod (p ^ 2))) = p * orderOf ((a : ZMod p)) := sorry

/-- The Wall–Sun–Sun rank index `p − (5/p)`: `p − 1` when `5` is a quadratic
    residue mod `p` (`p ≡ ±1 (mod 5)`), `p + 1` when not (`p ≡ ±2 (mod 5)`),
    and `p` itself at `p = 5` (the ramified prime). -/
def wssIndex (p : ℕ) : ℕ :=
  if p % 5 = 1 ∨ p % 5 = 4 then p - 1
  else if p % 5 = 2 ∨ p % 5 = 3 then p + 1
  else p

/-- **The Wall–Sun–Sun condition**: `p² ∣ F_{p − (5/p)}` — the Fibonacci
    unit's Wieferich condition. -/
def IsWallSunSun (p : ℕ) : Prop := p ^ 2 ∣ Nat.fib (wssIndex p)

/-- Square factors of Mersenne numbers are Wieferich primes: if `p` is prime
    and `q² ∣ 2^p − 1`, then `2^(q−1) ≡ 1 (mod q²)`. -/
theorem sq_dvd_mersenne_wieferich {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ^ 2 ∣ 2 ^ p - 1) : (q : ℤ) ^ 2 ∣ 2 ^ (q - 1) - 1 := sorry

/-- The general-index forced obstruction: `q² ∣ 2ⁿ − 1` (`q` odd prime) forces
    `q` Wieferich or `q · ord_q(2) ∣ n`. -/
theorem sq_dvd_two_pow_forced {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ^ 2 ∣ 2 ^ n - 1) :
    ((q : ℤ) ^ 2 ∣ 2 ^ (q - 1) - 1) ∨ q * orderOf (2 : ZMod q) ∣ n := sorry

/-- No Wall–Sun–Sun prime below 100. -/
theorem no_wallSunSun_below_100 : ∀ p < 100, p.Prime → ¬ IsWallSunSun p := sorry

/-! ### v0.1.2: the parity-tower law and the golden/silver Glaisher bands

Self-contained vocabulary: harmonic ladders, recurrence-defined Bernoulli
numbers over `ZMod p` (von Staudt–Clausen never enters — every division in
the recurrence is by an invertible element), Bernoulli-polynomial evaluation,
and the quadratic characters mod 5 and mod 8. -/

open Finset

/-- The r-th harmonic ladder prefix over `ZMod p`. -/
def ladder (p : ℕ) (r m : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 m, ((k : ZMod p)⁻¹) ^ r

/-- Bernoulli numbers over `ZMod p`: `B_0 = 1`,
    `B_{m+1} = −(m+2)⁻¹ · Σ_{j≤m} C(m+2,j)·B_j`. -/
def bmod (p : ℕ) : ℕ → ZMod p
  | 0 => 1
  | m + 1 =>
      -((m : ZMod p) + 2)⁻¹ *
        ∑ j ∈ (Finset.range (m + 1)).attach,
          (((m + 2).choose j.1 : ℕ) : ZMod p) * bmod p j.1
  decreasing_by exact Finset.mem_range.mp j.2

/-- Evaluation of the degree-`n` Bernoulli polynomial over `ZMod p`. -/
def bpolyEval (p n : ℕ) (x : ZMod p) : ZMod p :=
  ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ZMod p) * bmod p i * x ^ (n - i)

/-- The quadratic character mod 5 (`χ₅(±1) = 1`, `χ₅(±2) = −1`), valued in
    `ZMod p`. -/
def chiFive (p : ℕ) : ℕ → ZMod p := fun j =>
  if j % 5 = 1 ∨ j % 5 = 4 then 1
  else if j % 5 = 2 ∨ j % 5 = 3 then -1 else 0

/-- The quadratic character mod 8 (`χ₈(±1) = 1`, `χ₈(±3) = −1`), valued in
    `ZMod p`. -/
def chiEight (p : ℕ) : ℕ → ZMod p := fun j =>
  if j % 8 = 1 ∨ j % 8 = 7 then 1
  else if j % 8 = 3 ∨ j % 8 = 5 then -1 else 0

variable {p : ℕ} [Fact p.Prime]

/-- **The parity-tower law** (inverse-free form): for any weight `χ` mod `f`
    with `Σχ = 0`, the multiplicative twist, and parity `ε`,
    `χ(p̄)·(p−r)·Σ_j χ(j)·H^(r)_{⌊jp/f⌋} = ε·Σ_a χ(a)·B_{p−r}(a/f)` over
    `ZMod p` — the mod-p Glaisher/Lehmer congruence family in one law, with
    the conjugate-character Euler factor. -/
theorem parity_tower_law {f r : ℕ} (χ : ℕ → ZMod p) (ε : ZMod p)
    (hr : 1 ≤ r) (hrp : r ≤ p - 2) (hco : Nat.Coprime p f) (hf : 2 ≤ f)
    (hsum : ∑ j ∈ Finset.Icc 1 (f - 1), χ j = 0)
    (htw : ∀ j, χ (j * p % f) = χ (p % f) * χ j)
    (hpar : ∀ a, 0 < a → a < f → χ (f - a) = ε * χ a) :
    χ (p % f) * (((p - r : ℕ) : ZMod p)) *
        ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)
      = ε * ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            ((a : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := sorry

/-- **The golden band in Bernoulli closed form**: the Glaisher band
    `H_{⌊2p/5⌋} − H_{⌊p/5⌋}` (the Fibonacci/golden Fermat-quotient band)
    equals an explicit generalized-Bernoulli value. -/
theorem golden_band_bernoulli (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    chiFive p (p % 5) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (2 * p / 5) - ladder p 1 (1 * p / 5)))
      = ∑ a ∈ Finset.Icc 1 4,
          chiFive p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((5 : ℕ) : ZMod p)⁻¹) := sorry

/-- **The silver band in Bernoulli closed form**: the Pell/silver band
    `H_{⌊3p/8⌋} − H_{⌊p/8⌋}` likewise. -/
theorem silver_band_bernoulli (hp2 : p ≠ 2) :
    chiEight p (p % 8) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (3 * p / 8) - ladder p 1 (1 * p / 8)))
      = ∑ a ∈ Finset.Icc 1 7,
          chiEight p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((8 : ℕ) : ZMod p)⁻¹) := sorry
