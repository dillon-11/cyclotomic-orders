/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# the primitive-prime congruence at an arbitrary base
The master theorem behind the Mersenne congruence: a prime factor of `aᵖ − 1`
(p prime) either divides `a − 1` or is `≡ 1 (mod p)`.  Base 2 recovers the
exceptionless Mersenne congruence (a − 1 = 1); base 10 gives the same law for
repunit primes Rₚ = (10ᵖ − 1)/9.
  • `orderOf_base_eq_prime` — a, q with q ∤ a and q ∤ a − 1, q ∣ aᵖ − 1 (p prime):
    the order of a modulo q is exactly p;
  • `primeFactor_base_pow_prime_dvd_sub_one` — hence p ∣ q − 1;
  • `mersenne_base_two` — base 2 corollary: every prime factor of 2ᵖ − 1 is
    ≡ 1 (mod p) (a − 1 = 1 is never divisible by a prime);
  • `repunit_primeFactor` — base 10: a prime factor q ≠ 3 of the repunit
    Rₚ · 9 = 10ᵖ − 1 is ≡ 1 (mod p).
Axiom-clean, `sorry`-free.
-/

namespace CyclotomicOrders.Base

/-- The residue of `a` modulo a prime dividing `aⁿ − 1` satisfies `aⁿ = 1`. -/
lemma base_pow_eq_one {a n q : ℕ} [Fact q.Prime] (ha : 1 ≤ a) (hdvd : q ∣ a ^ n - 1) :
    (a : ZMod q) ^ n = 1 := by
  have h1 : (1 : ℕ) ≤ a ^ n := Nat.one_le_pow _ _ ha
  have hz : ((a ^ n - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ q).mpr hdvd
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hz
  exact hz

/-- The order of `a` modulo a prime factor `q` of `aᵖ − 1` (`p` prime), when `q`
    divides neither `a` nor `a − 1`, is exactly `p`. -/
theorem orderOf_base_eq_prime {a p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 ≤ a) (_hqa : ¬ q ∣ a) (hqa1 : ¬ q ∣ a - 1) (hdvd : q ∣ a ^ p - 1) :
    orderOf (a : ZMod q) = p := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (base_pow_eq_one ha hdvd) ?_
  intro h
  -- a ≡ 1 (mod q) would give q ∣ a − 1
  have hcast : ((a : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff] at hcast
  exact hqa1 ((Nat.modEq_iff_dvd' ha).mp hcast.symm)

/-- **The base-`a` primitive-prime congruence**: a prime factor `q` of `aᵖ − 1`
    (`p` prime) with `q ∤ a` and `q ∤ a − 1` satisfies `p ∣ q − 1`. -/
theorem primeFactor_base_pow_prime_dvd_sub_one {a p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 ≤ a) (hqa : ¬ q ∣ a) (hqa1 : ¬ q ∣ a - 1) (hdvd : q ∣ a ^ p - 1) :
    p ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : orderOf (a : ZMod q) = p := orderOf_base_eq_prime hp hq ha hqa hqa1 hdvd
  have hne0 : (a : ZMod q) ≠ 0 := by
    rw [Ne, show (a : ZMod q) = ((a : ℕ) : ZMod q) by norm_cast, ZMod.natCast_eq_zero_iff]
    exact hqa
  have hdvd' : orderOf (a : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hne0
  rwa [hord] at hdvd'

/-- Base 2: every prime factor of `2ᵖ − 1` is `≡ 1 (mod p)` — the exceptionless
    Mersenne congruence (`a − 1 = 1` has no prime divisor). -/
theorem mersenne_base_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : p ∣ q - 1 := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    have he : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.pos.ne'
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    omega
  refine primeFactor_base_pow_prime_dvd_sub_one hp hq (by norm_num) ?_ ?_ hdvd
  · exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  · exact fun h => hq.ne_one (Nat.dvd_one.mp (by simpa using h))

/-- Base 10: a prime factor `q ≠ 3` of `10ᵖ − 1` (equivalently of the repunit
    `Rₚ = (10ᵖ − 1)/9`) is `≡ 1 (mod p)`. -/
theorem repunit_primeFactor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq5 : q ≠ 5) (hdvd : q ∣ 10 ^ p - 1) :
    p ∣ q - 1 := by
  refine primeFactor_base_pow_prime_dvd_sub_one hp hq (by norm_num) ?_ ?_ hdvd
  · -- q ∤ 10 : q is a prime ≠ 2, 5
    intro h
    rw [show (10 : ℕ) = 2 * 5 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h2 | h5
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
    · exact hq5 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)
  · -- q ∤ 9 : q ≠ 3
    intro h
    have h9 : q ∣ 3 ^ 2 := by norm_num at h ⊢; exact h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h9))

end CyclotomicOrders.Base
