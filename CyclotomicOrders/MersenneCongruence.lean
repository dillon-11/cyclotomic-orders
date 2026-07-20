import Mathlib
import CyclotomicOrders.BaseTwo

/-!
# the primitive-prime congruence: why Mersenne factors are large
The order structure behind the cyclotomic-base-2 unification (census):
a prime dividing a Mersenne number is congruent to 1 modulo the (prime) exponent.
  • `two_orderOf_eq_of_dvd_mersenne` — for p prime and q an odd prime with
    q ∣ 2ᵖ − 1, the multiplicative order of 2 modulo q is exactly p (it divides p
    by q ∣ 2ᵖ−1, and it is not 1 since q ∤ 2−1);
  • `mersenne_primeFactor_dvd_sub_one` — hence p ∣ q − 1  (Lagrange: the order
    divides |(ℤ/q)ˣ| = q − 1);
  • `mersenne_primeFactor_modEq_one` — the same as q ≡ 1 (mod p);
  • `mersenne_primeFactor_two_mul` — the sharp form q ≡ 1 (mod 2p): q is odd and
    p is odd, so both 2 and p divide q − 1.
This is the Mersenne analogue of Mathlib's `Nat.fermat_primeFactors_one_lt`
(prime factors of Fₙ are ≡ 1 mod 2^(n+2)); together they are one law — a
primitive prime divisor of Φ_d(2) is ≡ 1 (mod d) — instantiated at the two index
families (prime index for Mersenne, power-of-two index for Fermat).  It explains
the factorizations 2¹¹ − 1 = 23·89 (23 = 2·11+1, 89 = 8·11+1) and
2²³ − 1 = 47·178481.
Axiom-clean, `sorry`-free.
-/

namespace CyclotomicOrders

open Polynomial

/-- A Mersenne number `2ᵖ − 1` is odd. -/
lemma odd_two_pow_sub_one {p : ℕ} (hp : 0 < p) : Odd (2 ^ p - 1) := by
  have he : Even (2 ^ p) := by
    rw [Nat.even_pow]
    exact ⟨even_two, hp.ne'⟩
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  rcases he with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

/-- The residue of `2` modulo a prime dividing a Mersenne number satisfies `2ᵖ = 1`. -/
lemma two_pow_eq_one {p q : ℕ} [Fact q.Prime] (hdvd : q ∣ 2 ^ p - 1) :
    (2 : ZMod q) ^ p = 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ q).mpr hdvd
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at hz
  exact hz

/-- A prime `q ≠ 2` dividing `2ᵖ − 1` has `2 ≠ 0` and `2 ≠ 1` modulo it. -/
lemma two_ne_zero_ne_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (2 : ZMod q) ≠ 0 ∧ (2 : ZMod q) ≠ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hnd : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  refine ⟨?_, ?_⟩
  · rw [show (2 : ZMod q) = ((2 : ℕ) : ZMod q) by norm_cast, Ne, ZMod.natCast_eq_zero_iff]
    exact hnd
  · intro h
    have h21 : ((2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; exact h
    rw [ZMod.natCast_eq_natCast_iff] at h21
    have hd : q ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp h21.symm
    have := hq.one_lt
    exact absurd (Nat.le_of_dvd one_pos hd) (by omega)

/-- The order of `2` modulo an odd prime factor of `2ᵖ − 1` (`p` prime) is exactly `p`. -/
theorem two_orderOf_eq_of_dvd_mersenne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hdvd : q ∣ 2 ^ p - 1) : orderOf (2 : ZMod q) = p := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (two_pow_eq_one hdvd) (two_ne_zero_ne_one hq hq2).2

/-- The odd-prime side condition: any prime factor of `2ᵖ − 1` (`p > 0`) is `≠ 2`. -/
lemma primeFactor_ne_two {p q : ℕ} (hp : 0 < p) (hdvd : q ∣ 2 ^ p - 1) : q ≠ 2 := by
  intro h
  subst h
  exact (Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one hp)) (even_iff_two_dvd.mpr hdvd)

/-- **The Mersenne primitive-prime congruence**: every prime factor `q` of `2ᵖ − 1`
    (`p` prime) satisfies `p ∣ q − 1`. -/
theorem mersenne_primeFactor_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : p ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := primeFactor_ne_two hp.pos hdvd
  have hord : orderOf (2 : ZMod q) = p := two_orderOf_eq_of_dvd_mersenne hp hq hq2 hdvd
  have hdvd' : orderOf (2 : ZMod q) ∣ q - 1 :=
    ZMod.orderOf_dvd_card_sub_one (two_ne_zero_ne_one hq hq2).1
  rwa [hord] at hdvd'

/-- The congruence form: `q ≡ 1 (mod p)` for every prime factor `q` of `2ᵖ − 1`. -/
theorem mersenne_primeFactor_modEq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : q ≡ 1 [MOD p] :=
  ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr (mersenne_primeFactor_dvd_sub_one hp hq hdvd)).symm

/-- **The sharp Mersenne congruence** `q ≡ 1 (mod 2p)`: for an odd prime `p`, every
    prime factor `q` of `2ᵖ − 1` satisfies `2p ∣ q − 1` (both `q` and `p` odd, so
    `q − 1` is even and divisible by the odd `p`). -/
theorem mersenne_primeFactor_two_mul {p q : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1) : 2 * p ∣ q - 1 := by
  have hq2 : q ≠ 2 := primeFactor_ne_two hp.pos hdvd
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hp_dvd : p ∣ q - 1 := mersenne_primeFactor_dvd_sub_one hp hq hdvd
  have h2_dvd : 2 ∣ q - 1 := by have := Nat.odd_iff.mp hqodd; omega
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (by rw [Nat.coprime_primes Nat.prime_two hp]; have := Nat.odd_iff.mp hodd; omega)
    h2_dvd hp_dvd

/-- **Unification with the Fermat side.**  Mathlib's `Nat.fermat_primeFactors_one_lt`
    gives, for `1 < n`, that every prime factor of `Fₙ = 2^(2ⁿ) + 1` is
    `≡ 1 (mod 2^(n+2))`.  Restated here beside the Mersenne congruence in the same
    `d ∣ q − 1` form: a primitive prime divisor of `Φ_d(2)` is `≡ 1 (mod d)` —
    Mersenne at the prime index `d = p`, Fermat at the power-of-two index. -/
theorem fermat_primeFactor_dvd_sub_one {n q : ℕ} (hn : 1 < n) (hq : q.Prime)
    (hdvd : q ∣ Nat.fermatNumber n) : 2 ^ (n + 2) ∣ q - 1 := by
  obtain ⟨k, hk⟩ := Nat.fermat_primeFactors_one_lt n q hn hq hdvd
  exact ⟨k, by rw [hk, Nat.add_sub_cancel]; ring⟩

end CyclotomicOrders
