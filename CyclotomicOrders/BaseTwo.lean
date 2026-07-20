/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.Fermat
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import CyclotomicOrders.PierceSequence

/-!
# Mersenne and Fermat numbers as cyclotomic values at 2
The cyclotomic-base-2 unification (census): both classical prime families
are values of cyclotomic polynomials evaluated at 2, distinguished only by the
index type.
  • `mersenne_eq_cyclotomic_eval` — for p prime, 2ᵖ − 1 = Φ_p(2)  (the Mersenne
    number is the value at 2 of the p-th cyclotomic polynomial; its only proper
    divisor index is 1, and Φ₁(2) = 1, so the primitive part is everything);
  • `fermat_eq_cyclotomic_eval`   — Fₖ = 2^(2ᵏ) + 1 = Φ_{2^(k+1)}(2)  (Φ of a
    power of two is Xᵐ + 1);
  • `two_pow_sub_one_eq_prod_cyclotomic_eval` — 2ⁿ − 1 = ∏_{d ∣ n} Φ_d(2)  (the
    cyclotomic factorization of the Mersenne numbers, `X^n − 1 = ∏ Φ_d` at 2);
  • `pierce_eq_prod_cyclotomic_eval` — the bridge to the Pierce sequence: the Pierce
    sequence of X − 2 factors into the cyclotomic values Φ_d(2).
Together: Mersenne primes are the prime Φ_p(2) at prime index p; Fermat primes are
the prime Φ_{2^(k+1)}(2) at power-of-two index — the two extreme index types of the
same base-2 cyclotomic family.  This is why Mersenne primality forces a prime
exponent (Mathlib's `Nat.prime_of_pow_sub_one_prime`): for composite n a proper
Φ_d(2) > 1 splits off the product.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace CyclotomicOrders.BaseTwo

open Polynomial CyclotomicOrders.Mahler CyclotomicOrders.Pierce

noncomputable section

/-- Mersenne as a cyclotomic value: for `p` prime, `2^p − 1 = Φ_p(2)`.  One
    evaluation of `cyclotomic p ℤ * (X − 1) = X^p − 1` at `X = 2`. -/
theorem mersenne_eq_cyclotomic_eval (p : ℕ) (hp : p.Prime) :
    (2 ^ p - 1 : ℤ) = (cyclotomic p ℤ).eval 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun q : Polynomial ℤ => q.eval 2) (cyclotomic_prime_mul_X_sub_one ℤ p)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at h
  linarith [h]

/-- Fermat as a cyclotomic value: `Fₖ = 2^(2ᵏ) + 1 = Φ_{2^(k+1)}(2)`.  `Φ` of a
    prime power collapses (base 2) to the two-term geometric sum `1 + X^(2ᵏ)`. -/
theorem fermat_eq_cyclotomic_eval (k : ℕ) :
    (Nat.fermatNumber k : ℤ) = (cyclotomic (2 ^ (k + 1)) ℤ).eval 2 := by
  rw [cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := k) Nat.prime_two]
  rw [eval_finsetSum]
  simp only [eval_pow, eval_X]
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  rw [Nat.fermatNumber]
  push_cast
  ring

/-- The cyclotomic factorization of the Mersenne numbers: `2ⁿ − 1 = ∏_{d ∣ n} Φ_d(2)`.
    The evaluation at 2 of `X^n − 1 = ∏_{d ∣ n} Φ_d`. -/
theorem two_pow_sub_one_eq_prod_cyclotomic_eval (n : ℕ) (hn : 0 < n) :
    (2 ^ n - 1 : ℤ) = ∏ d ∈ n.divisors, (cyclotomic d ℤ).eval 2 := by
  have h := congrArg (fun q : Polynomial ℤ => q.eval 2)
    (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
  exact h.symm

/-- The bridge to the Pierce sequence: the Pierce sequence of `X − 2` — proven equal to
    `2ⁿ − 1` in `PierceSequence` — factors into the cyclotomic values `Φ_d(2)`. -/
theorem pierce_eq_prod_cyclotomic_eval (n : ℕ) (hn : 0 < n) :
    pierce (X - C 2) n = ((∏ d ∈ n.divisors, (cyclotomic d ℤ).eval 2 : ℤ) : ℝ) := by
  rw [mersenne_pierce, ← two_pow_sub_one_eq_prod_cyclotomic_eval n hn]
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  push_cast
  ring

end






end CyclotomicOrders.BaseTwo
