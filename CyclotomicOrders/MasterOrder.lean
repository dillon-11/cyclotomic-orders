/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# the general primitive-prime order theorem
The arbitrary-index generalization of the Mersenne order lemma: a prime `q`
dividing the cyclotomic value `Φ_n(a)`, with `q ∤ n`, has `a` of multiplicative
order exactly `n` modulo `q` — hence `n ∣ q − 1`.  This is the full
"primitive prime divisors are ≡ 1 (mod n)" law behind the whole cyclotomic-base
program, discharging the general-index case (not just prime and
power-of-two indices).
  • `cyclotomic_primeFactor_orderOf` — `q ∤ n`, `q ∣ Φ_n(a)` ⟹ `orderOf (a : ZMod q) = n`
    (a root of `Φ_n` in a field of characteristic coprime to `n` is a primitive
    `n`-th root, `isRoot_cyclotomic_iff`);
  • `cyclotomic_primeFactor_dvd_sub_one` — hence `n ∣ q − 1`.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace CyclotomicOrders

open Polynomial

/-- The value `Φ_n(a)` cast into `ZMod q` is the evaluation of `cyclotomic n (ZMod q)`
    at `a`. -/
lemma cyclotomic_eval_cast (n a q : ℕ) :
    (cyclotomic n (ZMod q)).eval (a : ZMod q) =
      (Int.castRingHom (ZMod q)) ((cyclotomic n ℤ).eval (a : ℤ)) := by
  have hx : (a : ZMod q) = (Int.castRingHom (ZMod q)) (a : ℤ) := by simp
  rw [hx, ← map_cyclotomic n (Int.castRingHom (ZMod q)), eval_map, eval₂_hom]

/-- **The general primitive-prime order theorem**: if `q ∤ n` and the prime `q`
    divides `Φ_n(a)`, then the order of `a` modulo `q` is exactly `n`. -/
theorem cyclotomic_primeFactor_orderOf {n a q : ℕ} (_hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    orderOf (a : ZMod q) = n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (n : ZMod q) := ⟨by
    rw [Ne, ← Nat.cast_zero, ZMod.natCast_eq_iff]
    rintro ⟨k, hk⟩
    exact hqn ⟨k, by simpa using hk⟩⟩
  have hroot : (cyclotomic n (ZMod q)).IsRoot (a : ZMod q) := by
    rw [IsRoot, cyclotomic_eval_cast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
  exact (isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm

/-- Consequently `n ∣ q − 1` (Lagrange in `(ℤ/q)ˣ`). -/
theorem cyclotomic_primeFactor_dvd_sub_one {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hqa : ¬ q ∣ a) (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    n ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hord := cyclotomic_primeFactor_orderOf hn hq hqn hdvd
  have hne0 : (a : ZMod q) ≠ 0 := by
    rw [Ne, show (a : ZMod q) = ((a : ℕ) : ZMod q) by norm_cast, ZMod.natCast_eq_zero_iff]
    exact hqa
  have := ZMod.orderOf_dvd_card_sub_one hne0
  rwa [hord] at this

end CyclotomicOrders
