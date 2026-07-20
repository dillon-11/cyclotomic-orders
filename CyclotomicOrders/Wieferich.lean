/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# Wieferich primes and the order-lift crux
A Wieferich prime is a prime `p` with `p² ∣ 2^(p-1) − 1` (only `1093` and `3511`
are known below 2⁶⁴).  They live inside the primitive-prime order machinery
as the primes where the multiplicative order of 2 fails to grow from `p` to `p²`.
  • `sq_dvd_pow_mul_of_dvd` — the order-lift crux: `p ∣ aᵈ − 1 ⟹ p² ∣ a^(pd) − 1`
    (from `dvd_sub_pow_of_dvd_sub`, the base of "lifting the exponent"); so the
    order modulo `p²` always divides `p ·` the order modulo `p`;
  • `Wieferich` — the predicate `p² ∣ 2^(p-1) − 1`;
  • `wieferich_iff` — `p` Wieferich ⟺ `(2 : ZMod p²)^(p-1) = 1`;
  • `not_wieferich_two`, `not_wieferich_three` — 2 and 3 are not Wieferich.
Axiom-clean, `sorry`-free.
-/

namespace CyclotomicOrders.Wieferich

/-- **The order-lift crux**: if `p ∣ aᵈ − 1` then `p² ∣ a^(pd) − 1`.  A prime power
    lift of a congruence — the reason `ord_{p²}(a) ∣ p · ord_p(a)`. -/
theorem sq_dvd_pow_mul_of_dvd {p : ℕ} {a : ℤ} {d : ℕ} (h : (p : ℤ) ∣ a ^ d - 1) :
    (p : ℤ) ^ 2 ∣ a ^ (p * d) - 1 := by
  have hk := dvd_sub_pow_of_dvd_sub (p := p) (a := a ^ d) (b := 1) (by simpa using h) 1
  simp only [one_pow, pow_one, ← pow_mul] at hk
  rwa [mul_comm d p] at hk

/-- A prime `p` is Wieferich when `p²` divides `2^(p-1) − 1`. -/
def IsWieferich (p : ℕ) : Prop := (p : ℤ) ^ 2 ∣ 2 ^ (p - 1) - 1

/-- Wieferich in the residue ring: `(2 : ZMod p²)^(p-1) = 1`. -/
theorem wieferich_iff {p : ℕ} :
    IsWieferich p ↔ (2 : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
  unfold IsWieferich
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]

/-- 2 is not a Wieferich prime (`2² = 4 ∤ 2⁰ = 1`). -/
theorem not_wieferich_two : ¬ IsWieferich 2 := by norm_num [IsWieferich]

/-- 3 is not a Wieferich prime (`3² = 9 ∤ 2² = 4`, i.e. `9 ∤ 3`). -/
theorem not_wieferich_three : ¬ IsWieferich 3 := by norm_num [IsWieferich]

/-- The order-lift bound as a divisibility on `2^(p-1) − 1`: if the order `d` of 2
    modulo `p` divides `p − 1` (always true for `p` an odd prime, by Fermat), then
    `p² ∣ 2^(p·(p-1)/d ...)` — the clean consequence used to test Wieferich.  Here
    the direct form: any `d` with `p ∣ 2ᵈ − 1` gives `p² ∣ 2^(pd) − 1`. -/
theorem sq_dvd_two_pow_mul {p d : ℕ} (h : (p : ℤ) ∣ 2 ^ d - 1) :
    (p : ℤ) ^ 2 ∣ 2 ^ (p * d) - 1 :=
  sq_dvd_pow_mul_of_dvd h

/-- Integer congruence from the order modulo `p`: `p ∣ aᵈ − 1` where `d` is the
    order of `a` modulo `p`. -/
lemma dvd_pow_orderOf_sub_one {p a : ℕ} [Fact p.Prime] :
    (p : ℤ) ∣ (a : ℤ) ^ orderOf ((a : ZMod p)) - 1 := by
  have h1 : ((a : ZMod p)) ^ orderOf ((a : ZMod p)) = 1 := pow_orderOf_eq_one _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h1, sub_self]

/-- **The order-lift dichotomy**: for an odd prime `p` and `a` coprime to `p`, the
    order of `a` modulo `p²` is either the order modulo `p` or `p` times it.  The
    Wieferich primes are exactly the base-2 primes realizing the first (non-lift)
    branch. -/
theorem orderOf_lift_dichotomy {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    orderOf ((a : ZMod (p ^ 2))) = orderOf ((a : ZMod p)) ∨
      orderOf ((a : ZMod (p ^ 2))) = p * orderOf ((a : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set d := orderOf ((a : ZMod p)) with hd
  set D := orderOf ((a : ZMod (p ^ 2))) with hD
  have hpp2 : p ∣ p ^ 2 := ⟨p, sq p⟩
  -- d ∣ D via the reduction ring hom ZMod p² → ZMod p
  have hdD : d ∣ D := by
    apply orderOf_dvd_of_pow_eq_one
    have hpow : ((a : ZMod (p ^ 2))) ^ D = 1 := pow_orderOf_eq_one _
    have hc := congrArg (ZMod.castHom hpp2 (ZMod p)) hpow
    rwa [map_pow, map_natCast, map_one] at hc
  -- D ∣ p·d via the order-lift crux
  have hDpd : D ∣ p * d := by
    have hsq : (p : ℤ) ^ 2 ∣ (a : ℤ) ^ (p * d) - 1 :=
      sq_dvd_pow_mul_of_dvd dvd_pow_orderOf_sub_one
    have hz : ((a : ZMod (p ^ 2))) ^ (p * d) = 1 := by
      have : (((a : ℤ) ^ (p * d) - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rwa [show ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 by push_cast; ring]
      push_cast at this
      rw [sub_eq_zero] at this
      exact_mod_cast this
    exact orderOf_dvd_of_pow_eq_one hz
  -- d ≠ 0 : the order divides p − 1 > 0
  have hane : ((a : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact ha
  have hd0 : d ≠ 0 := by
    have hdd : d ∣ p - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hane)
    intro h0
    rw [h0, Nat.zero_dvd] at hdd
    have := hp.two_le
    omega
  -- D = d·m with m ∣ p, p prime ⇒ m ∈ {1, p}
  obtain ⟨m, hm⟩ := hdD
  have hmp : m ∣ p := by
    have : d * m ∣ d * p := by rw [← hm, mul_comm d p]; exact hDpd
    exact (mul_dvd_mul_iff_left hd0).mp this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp m hmp) with h1 | hp'
  · left; rw [hm, h1, mul_one]
  · right; rw [hm, hp', mul_comm]

end CyclotomicOrders.Wieferich
