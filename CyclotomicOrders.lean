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


/-! Parity-tower / band-law audit (v0.1.2). -/
