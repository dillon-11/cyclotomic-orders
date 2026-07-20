/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import CyclotomicOrders.ParityLadder
import CyclotomicOrders.MersenneSquare
import CyclotomicOrders.WallSunSun
import CyclotomicOrders.Mahler
import CyclotomicOrders.CyclotomicRepulsion
import CyclotomicOrders.PierceSequence
import CyclotomicOrders.BaseTwo
import CyclotomicOrders.MersenneCongruence
import CyclotomicOrders.BaseCongruence
import CyclotomicOrders.MasterOrder
import CyclotomicOrders.Wieferich

/-! Axiom audit: every theorem, discharged. -/
#print axioms CyclotomicOrders.Mahler.cartan_symmetric
#print axioms CyclotomicOrders.Mahler.lehmer_palindrome
#print axioms CyclotomicOrders.Mahler.coxeter_eq_lit
#print axioms CyclotomicOrders.Mahler.lehmer_annihilates_lit
#print axioms CyclotomicOrders.Mahler.lehmer_annihilates
#print axioms CyclotomicOrders.Mahler.coxeter_trace
#print axioms CyclotomicOrders.Mahler.coxeter_det
#print axioms CyclotomicOrders.Mahler.minors_natural
#print axioms CyclotomicOrders.Mahler.minors_certification
#print axioms CyclotomicOrders.Mahler.fl_charpoly_lehmer
#print axioms CyclotomicOrders.Mahler.fl_charpoly_coxeter
#print axioms CyclotomicOrders.Mahler.power_sums_value
#print axioms CyclotomicOrders.Mahler.newton_pin
#print axioms CyclotomicOrders.Mahler.newton_unique
#print axioms CyclotomicOrders.Mahler.log_gap_pos_iff_dilatation_gt_one
#print axioms CyclotomicOrders.Mahler.one_le_mahler
#print axioms CyclotomicOrders.Mahler.gap_floor_of_lehmer
#print axioms CyclotomicOrders.dev_nonneg
#print axioms CyclotomicOrders.dev_neg
#print axioms CyclotomicOrders.norm_exp_mul_I_sub_one_le
#print axioms CyclotomicOrders.norm_exp_two_pi_sub_one_le
#print axioms CyclotomicOrders.prod_pow_sub_one_int
#print axioms CyclotomicOrders.one_le_prod_norm
#print axioms CyclotomicOrders.repulsion_floor
#print axioms CyclotomicOrders.mimicry_impossible
#print axioms CyclotomicOrders.Pierce.prod_map_le
#print axioms CyclotomicOrders.Pierce.pierce_lower
#print axioms CyclotomicOrders.Pierce.pierce_upper
#print axioms CyclotomicOrders.Pierce.pierce_pos
#print axioms CyclotomicOrders.Pierce.pierce_log_window
#print axioms CyclotomicOrders.Pierce.roots_X_sub_two
#print axioms CyclotomicOrders.Pierce.mersenne_pierce
#print axioms CyclotomicOrders.Pierce.mersenne_mahler
#print axioms CyclotomicOrders.BaseTwo.mersenne_eq_cyclotomic_eval
#print axioms CyclotomicOrders.BaseTwo.fermat_eq_cyclotomic_eval
#print axioms CyclotomicOrders.BaseTwo.two_pow_sub_one_eq_prod_cyclotomic_eval
#print axioms CyclotomicOrders.BaseTwo.pierce_eq_prod_cyclotomic_eval
#print axioms CyclotomicOrders.odd_two_pow_sub_one
#print axioms CyclotomicOrders.two_pow_eq_one
#print axioms CyclotomicOrders.two_ne_zero_ne_one
#print axioms CyclotomicOrders.two_orderOf_eq_of_dvd_mersenne
#print axioms CyclotomicOrders.primeFactor_ne_two
#print axioms CyclotomicOrders.mersenne_primeFactor_dvd_sub_one
#print axioms CyclotomicOrders.mersenne_primeFactor_modEq_one
#print axioms CyclotomicOrders.mersenne_primeFactor_two_mul
#print axioms CyclotomicOrders.fermat_primeFactor_dvd_sub_one
#print axioms CyclotomicOrders.Base.base_pow_eq_one
#print axioms CyclotomicOrders.Base.orderOf_base_eq_prime
#print axioms CyclotomicOrders.Base.primeFactor_base_pow_prime_dvd_sub_one
#print axioms CyclotomicOrders.Base.mersenne_base_two
#print axioms CyclotomicOrders.Base.repunit_primeFactor
#print axioms CyclotomicOrders.cyclotomic_eval_cast
#print axioms CyclotomicOrders.cyclotomic_primeFactor_orderOf
#print axioms CyclotomicOrders.cyclotomic_primeFactor_dvd_sub_one
#print axioms CyclotomicOrders.Wieferich.sq_dvd_pow_mul_of_dvd
#print axioms CyclotomicOrders.Wieferich.wieferich_iff
#print axioms CyclotomicOrders.Wieferich.not_wieferich_two
#print axioms CyclotomicOrders.Wieferich.not_wieferich_three
#print axioms CyclotomicOrders.Wieferich.sq_dvd_two_pow_mul
#print axioms CyclotomicOrders.Wieferich.dvd_pow_orderOf_sub_one
#print axioms CyclotomicOrders.Wieferich.orderOf_lift_dichotomy
#print axioms CyclotomicOrders.MersenneSquare.orderOf_sq_dvd_two_pow
#print axioms CyclotomicOrders.MersenneSquare.sq_dvd_mersenne_wieferich
#print axioms CyclotomicOrders.MersenneSquare.sq_dvd_two_pow_forced
#print axioms fib_wssIndex_dvd
#print axioms no_wallSunSun_below_100
#print axioms not_wallSunSun_two
#print axioms not_wallSunSun_five

/-! The Challenge statements, re-declared at root level (comparator model). -/

open Polynomial in
/-- The master order theorem: `q ∣ Φ_n(a)`, `q ∤ n` ⟹ `ord_q(a) = n`. -/
theorem cyclotomic_primeFactor_orderOf {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    orderOf ((a : ZMod q)) = n :=
  CyclotomicOrders.cyclotomic_primeFactor_orderOf hn hq hqn hdvd

/-- The Mersenne congruence: a prime factor of `2^p − 1` (p an odd prime) is
    `≡ 1 (mod 2p)`. -/
theorem mersenne_primeFactor_two_mul {p q : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1) : 2 * p ∣ q - 1 :=
  CyclotomicOrders.mersenne_primeFactor_two_mul hp hodd hq hdvd

/-- The order-lift dichotomy: `ord_{p²}(a) ∈ {ord_p(a), p · ord_p(a)}`. -/
theorem orderOf_lift_dichotomy {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    orderOf ((a : ZMod (p ^ 2))) = orderOf ((a : ZMod p)) ∨
      orderOf ((a : ZMod (p ^ 2))) = p * orderOf ((a : ZMod p)) :=
  CyclotomicOrders.Wieferich.orderOf_lift_dichotomy hp ha

#print axioms cyclotomic_primeFactor_orderOf
#print axioms mersenne_primeFactor_two_mul
#print axioms orderOf_lift_dichotomy

/-- Square factors of Mersenne numbers are Wieferich primes: if `p` is prime
    and `q² ∣ 2^p − 1`, then `2^(q−1) ≡ 1 (mod q²)`. -/
theorem sq_dvd_mersenne_wieferich {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ^ 2 ∣ 2 ^ p - 1) : (q : ℤ) ^ 2 ∣ 2 ^ (q - 1) - 1 :=
  CyclotomicOrders.MersenneSquare.sq_dvd_mersenne_wieferich hp hq hdvd

/-- The general-index forced obstruction: `q² ∣ 2ⁿ − 1` (`q` odd prime) forces
    `q` Wieferich or `q · ord_q(2) ∣ n`. -/
theorem sq_dvd_two_pow_forced {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ^ 2 ∣ 2 ^ n - 1) :
    ((q : ℤ) ^ 2 ∣ 2 ^ (q - 1) - 1) ∨ q * orderOf (2 : ZMod q) ∣ n :=
  CyclotomicOrders.MersenneSquare.sq_dvd_two_pow_forced hq hq2 hdvd

#print axioms sq_dvd_mersenne_wieferich
#print axioms sq_dvd_two_pow_forced

/-! Parity-tower / band-law audit (v0.1.2). -/
#print axioms ladder_reflect
#print axioms parity_vanish
#print axioms chi5_projection_eq_band
#print axioms chi8_projection_eq_band
#print axioms ladder_bernoulli
#print axioms sum_pow_bernoulli
#print axioms floor_cut_cast
#print axioms parity_tower_law
#print axioms parity_tower_genBern
#print axioms golden_band_bernoulli
#print axioms silver_band_bernoulli
