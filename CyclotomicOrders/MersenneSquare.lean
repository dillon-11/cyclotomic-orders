/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import CyclotomicOrders.MersenneCongruence
import CyclotomicOrders.Wieferich

/-!
# square factors of Mersenne numbers are Wieferich.
  • `orderOf_sq_dvd_two_pow` — `q² ∣ 2ⁿ − 1` forces `ord_{q²}(2) ∣ n`;
  • `sq_dvd_mersenne_wieferich` — THE EXCLUSION: a squared prime factor of
    `2^p − 1` (p prime) is a base-2 Wieferich prime.  Mechanism: the order of
    2 mod q is exactly p (`two_orderOf_eq_of_dvd_mersenne`); the order mod q²
    divides p and by the order-lift dichotomy is p or q·p; q·p ∤ p kills the
    lift branch, so the order fails to lift — Wieferich — and `p ∣ q − 1`
    transports the congruence to `2^(q−1) ≡ 1 (mod q²)`.
  • `sq_dvd_two_pow_forced` — the general-index form: `q² ∣ 2ⁿ − 1` forces
    `q` Wieferich or `q · ord_q(2) ∣ n` (the forced-index obstruction).
Consequence: a Mersenne number with a repeated prime factor would exhibit a
Wieferich prime.  None is known below 2^p − 1 for any tested p; the only
base-2 Wieferich primes below 10¹⁷ are 1093 and 3511, and neither divides any
Mersenne number with prime exponent twice (their orders 364 = 2²·7·13 and
1755 = 3³·5·13 are composite).
-/

namespace CyclotomicOrders.MersenneSquare

open CyclotomicOrders CyclotomicOrders.Wieferich

/-- `q² ∣ 2ⁿ − 1` (as naturals) gives `(2 : ZMod q²)ⁿ = 1`. -/
lemma zmod_sq_pow_eq_one {q n : ℕ} (hdvd : q ^ 2 ∣ 2 ^ n - 1) :
    (2 : ZMod (q ^ 2)) ^ n = 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have h0 : ((2 ^ n - 1 : ℕ) : ZMod (q ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h2 : ((2 ^ n : ℕ) : ZMod (q ^ 2)) = ((1 : ℕ) : ZMod (q ^ 2)) := by
    have := congrArg (· + ((1 : ℕ) : ZMod (q ^ 2))) h0
    simpa [← Nat.cast_add, Nat.sub_add_cancel h1] using this
  simpa using h2

/-- The order of 2 modulo `q²` divides any `n` with `q² ∣ 2ⁿ − 1`. -/
theorem orderOf_sq_dvd_two_pow {q n : ℕ} (hdvd : q ^ 2 ∣ 2 ^ n - 1) :
    orderOf (2 : ZMod (q ^ 2)) ∣ n :=
  orderOf_dvd_of_pow_eq_one (zmod_sq_pow_eq_one hdvd)

/-- Wieferich from the residue-ring order: if `ord_{q²}(2) ∣ q − 1` then `q` is
    Wieferich. -/
lemma wieferich_of_orderOf_dvd {q : ℕ} (h : orderOf (2 : ZMod (q ^ 2)) ∣ q - 1) :
    IsWieferich q := by
  rw [wieferich_iff]
  exact orderOf_dvd_iff_pow_eq_one.mp h

/-- `q ∤ 2` for an odd prime `q`. -/
lemma not_dvd_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ 2 := fun h =>
  hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)

/-- **Square factors of Mersenne numbers are Wieferich primes**: if `p` is prime
    and `q² ∣ 2^p − 1`, then `q` is a base-2 Wieferich prime. -/
theorem sq_dvd_mersenne_wieferich {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ^ 2 ∣ 2 ^ p - 1) : IsWieferich q := by
  have hdvd1 : q ∣ 2 ^ p - 1 := dvd_trans (dvd_pow_self q two_ne_zero) hdvd
  have hq2 : q ≠ 2 := primeFactor_ne_two hp.pos hdvd1
  haveI : Fact q.Prime := ⟨hq⟩
  have hordq : orderOf (2 : ZMod q) = p := two_orderOf_eq_of_dvd_mersenne hp hq hq2 hdvd1
  have hDdvd : orderOf (2 : ZMod (q ^ 2)) ∣ p := orderOf_sq_dvd_two_pow hdvd
  have hdich := orderOf_lift_dichotomy (p := q) (a := 2) hq (not_dvd_two hq hq2)
  rw [show ((2 : ℕ) : ZMod (q ^ 2)) = (2 : ZMod (q ^ 2)) by norm_num,
    show ((2 : ℕ) : ZMod q) = (2 : ZMod q) by norm_num, hordq] at hdich
  have hD : orderOf (2 : ZMod (q ^ 2)) = p := by
    rcases hdich with h | h
    · exact h
    · exfalso
      rw [h] at hDdvd
      have hle : q * p ≤ p := Nat.le_of_dvd hp.pos hDdvd
      nlinarith [hq.two_le, hp.pos]
  have hp_dvd : p ∣ q - 1 := mersenne_primeFactor_dvd_sub_one hp hq hdvd1
  exact wieferich_of_orderOf_dvd (hD ▸ hp_dvd)

/-- **The general-index forced obstruction**: `q² ∣ 2ⁿ − 1` (`q` odd prime)
    forces `q` Wieferich or `q · ord_q(2) ∣ n`. -/
theorem sq_dvd_two_pow_forced {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ^ 2 ∣ 2 ^ n - 1) :
    IsWieferich q ∨ q * orderOf (2 : ZMod q) ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hDdvd : orderOf (2 : ZMod (q ^ 2)) ∣ n := orderOf_sq_dvd_two_pow hdvd
  have hdich := orderOf_lift_dichotomy (p := q) (a := 2) hq (not_dvd_two hq hq2)
  rw [show ((2 : ℕ) : ZMod (q ^ 2)) = (2 : ZMod (q ^ 2)) by norm_num,
    show ((2 : ℕ) : ZMod q) = (2 : ZMod q) by norm_num] at hdich
  rcases hdich with h | h
  · left
    have hd1 : orderOf (2 : ZMod q) ∣ q - 1 :=
      ZMod.orderOf_dvd_card_sub_one (two_ne_zero_ne_one hq hq2).1
    exact wieferich_of_orderOf_dvd (h ▸ hd1)
  · right
    rw [← h]
    exact hDdvd

end CyclotomicOrders.MersenneSquare
