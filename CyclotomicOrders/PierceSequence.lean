import CyclotomicOrders.Mahler
import CyclotomicOrders.CyclotomicRepulsion

/-!
# THE MAHLER MEASURE IS THE GROWTH RATE OF THE PIERCE SEQUENCE
The Mersenne/Fermat face of the escape volume (Lehmer's ORIGINAL 1933 frame: he asked
the gap question while hunting primes in the sequences Δ_n = ∏_ρ (ρⁿ − 1)).
  • The PIERCE SEQUENCE of p at time n:  Δ_n(p) := ∏_{ρ root of p} ‖ρⁿ − 1‖.
  • Mersenne numbers ARE the Pierce sequence of x − 2:  Δ_n(x−2) = 2ⁿ − 1  (proven below);
    Fermat numbers are its 2-adic tower quotients Φ_{2^{k+1}}(2) — the 2-power tower
    rungs.
WHAT IS PROVEN (axiom-clean, sorry-free):
  • `pierce_lower`   — 1 ≤ Δ_n(p) for monic p with no n-th root of unity among its
                       roots (the integrality jaw, consumed verbatim from the
                       cyclotomic repulsion module);
  • `pierce_upper`   — Δ_n(p) ≤ 2^d · M(p)ⁿ  (the archimedean jaw);
  • `pierce_log_window` — 0 ≤ log Δ_n(p) ≤ n·log M(p) + d·log 2:
    THE GROWTH RATE IS PINNED BY THE ESCAPE VOLUME — (1/n)·log Δ_n is squeezed
    into [0, log M + d·log2/n].  Lehmer's problem = does the Pierce sequence's exponential
    rate jump from 0 (cyclotomic, Kronecker cliff) to a floor γ > 0?
  • `mersenne_pierce`, `mersenne_mahler` — the Pierce sequence of x−2 is exactly 2ⁿ − 1 with
    M = 2: Mersenne growth is the minimal-escape instance of the window.
The lower rate (liminf (1/n)·log Δ_n = log M, Baker-grade for roots on the circle)
is not claimed here; the window above is what elementary integrality and norm
bounds give, with explicit constants.
-/

namespace CyclotomicOrders.Pierce

open Polynomial Multiset CyclotomicOrders.Mahler

noncomputable section

/-- The Pierce sequence `Δ_n(p) = ∏_ρ ‖ρⁿ − 1‖` over the complex roots of `p`. -/
def pierce (p : Polynomial ℤ) (n : ℕ) : ℝ :=
  (((p.map (Int.castRingHom ℂ)).roots).map fun z => ‖z ^ n - 1‖).prod

/-- Root count (with multiplicity) of `p` over ℂ. -/
def rootCount (p : Polynomial ℤ) : ℕ :=
  Multiset.card ((p.map (Int.castRingHom ℂ)).roots)

/-- Multiset product monotonicity for nonneg real-valued maps. -/
lemma prod_map_le {s : Multiset ℂ} {f g : ℂ → ℝ}
    (h0 : ∀ z ∈ s, 0 ≤ f z) (hfg : ∀ z ∈ s, f z ≤ g z) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hfa : 0 ≤ f a := h0 a (Multiset.mem_cons_self a t)
      have hga : f a ≤ g a := hfg a (Multiset.mem_cons_self a t)
      have htf : 0 ≤ (t.map f).prod := by
        refine Multiset.prod_nonneg ?_
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        exact h0 z (Multiset.mem_cons_of_mem hz)
      have hih : (t.map f).prod ≤ (t.map g).prod := by
        refine ih (fun z hz => h0 z (Multiset.mem_cons_of_mem hz))
          (fun z hz => hfg z (Multiset.mem_cons_of_mem hz))
      exact mul_le_mul hga hih htf (le_trans hfa hga)

/-- **THE INTEGRALITY JAW** (consumed verbatim from the repulsion module):
    the Pierce sequence never drops below 1 when no root is an n-th root of unity. -/
theorem pierce_lower (p : Polynomial ℤ) (hm : p.Monic) (n : ℕ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ n ≠ 1) :
    1 ≤ pierce p n :=
  CyclotomicOrders.one_le_prod_norm p hm n hnru

/-- **THE ARCHIMEDEAN JAW**: `Δ_n(p) ≤ 2^d · M(p)ⁿ`. -/
theorem pierce_upper (p : Polynomial ℤ) (n : ℕ) :
    pierce p n ≤ 2 ^ rootCount p * (mahler p) ^ n := by
  set s := (p.map (Int.castRingHom ℂ)).roots with hs
  have hterm : ∀ z ∈ s, ‖z ^ n - 1‖ ≤ 2 * (max 1 ‖z‖) ^ n := by
    intro z _
    have h1 : ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    have h2 : ‖z ^ n‖ = ‖z‖ ^ n := norm_pow z n
    have h3 : ‖z‖ ^ n ≤ (max 1 ‖z‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) n
    have h4 : (1 : ℝ) ≤ (max 1 ‖z‖) ^ n := one_le_pow₀ (le_max_left 1 ‖z‖)
    have h5 : ‖(1 : ℂ)‖ = 1 := norm_one
    nlinarith
  have hmono : pierce p n ≤ (s.map fun z => 2 * (max 1 ‖z‖) ^ n).prod := by
    rw [pierce, ← hs]
    exact prod_map_le (fun z _ => norm_nonneg _) hterm
  have hsplit : (s.map fun z => 2 * (max 1 ‖z‖) ^ n).prod =
      2 ^ Multiset.card s * ((s.map fun z => max 1 ‖z‖).prod) ^ n := by
    have h6 : (s.map fun z => 2 * (max 1 ‖z‖) ^ n).prod =
        (s.map fun _ => (2 : ℝ)).prod * (s.map fun z => (max 1 ‖z‖) ^ n).prod := by
      rw [← Multiset.prod_map_mul]
    have h7 : (s.map fun _ => (2 : ℝ)).prod = 2 ^ Multiset.card s := by
      rw [Multiset.map_const', Multiset.prod_replicate]
    have h8 : (s.map fun z => (max 1 ‖z‖) ^ n).prod =
        ((s.map fun z => max 1 ‖z‖).prod) ^ n := by
      rw [← Multiset.prod_map_pow]
    rw [h6, h7, h8]
  unfold CyclotomicOrders.Mahler.mahler rootCount
  rw [← hs]
  calc pierce p n ≤ (s.map fun z => 2 * (max 1 ‖z‖) ^ n).prod := hmono
    _ = 2 ^ Multiset.card s * ((s.map fun z => max 1 ‖z‖).prod) ^ n := hsplit

/-- Positivity of the Pierce sequence under the no-root-of-unity hypothesis. -/
theorem pierce_pos (p : Polynomial ℤ) (hm : p.Monic) (n : ℕ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ n ≠ 1) :
    0 < pierce p n :=
  lt_of_lt_of_le one_pos (pierce_lower p hm n hnru)

/-- **THE ENTROPY WINDOW**: `0 ≤ log Δ_n(p) ≤ n·log M(p) + d·log 2`.
    The exponential rate of the Pierce sequence is pinned by the escape volume:
    Lehmer's problem is whether the rate jumps from the Kronecker cliff (0) to a
    uniform floor.  Mersenne growth (`x−2`, rate log 2) is the minimal-escape
    nontrivial instance. -/
theorem pierce_log_window (p : Polynomial ℤ) (hm : p.Monic) (n : ℕ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ n ≠ 1) :
    0 ≤ Real.log (pierce p n) ∧
      Real.log (pierce p n) ≤ n * Real.log (mahler p) + rootCount p * Real.log 2 := by
  have hlow := pierce_lower p hm n hnru
  have hM : (1 : ℝ) ≤ mahler p := one_le_mahler p
  constructor
  · exact Real.log_nonneg hlow
  · have hup := pierce_upper p n
    have hrhs : (0 : ℝ) < 2 ^ rootCount p * (mahler p) ^ n := by positivity
    have hlog := Real.log_le_log (lt_of_lt_of_le one_pos hlow) hup
    have hsplit : Real.log (2 ^ rootCount p * (mahler p) ^ n) =
        rootCount p * Real.log 2 + n * Real.log (mahler p) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [hsplit] at hlog
    linarith

/-- The map of `X − 2` to ℂ has root multiset `{2}`. -/
lemma roots_X_sub_two :
    ((X - C 2 : Polynomial ℤ).map (Int.castRingHom ℂ)).roots = {(2 : ℂ)} := by
  have hmap : (X - C 2 : Polynomial ℤ).map (Int.castRingHom ℂ) =
      (X - C 2 : Polynomial ℂ) := by
    have hc : (Int.castRingHom ℂ) 2 = 2 := by simp
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc]
  rw [hmap, roots_X_sub_C]

/-- **MERSENNE = THE PIERCE SEQUENCE OF `x − 2`**: `Δ_n(x−2) = 2ⁿ − 1`. -/
theorem mersenne_pierce (n : ℕ) :
    pierce (X - C 2) n = 2 ^ n - 1 := by
  rw [pierce, roots_X_sub_two]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  have h2 : ((2 : ℂ)) ^ n - 1 = ((2 ^ n - 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [h2, Complex.norm_intCast]
  push_cast
  have h3 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [abs_of_nonneg (by linarith)]

/-- The escape volume of the Mersenne generator: `M(x−2) = 2`. -/
theorem mersenne_mahler : mahler (X - C 2 : Polynomial ℤ) = 2 := by
  unfold CyclotomicOrders.Mahler.mahler
  rw [roots_X_sub_two]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show ((2 : ℂ)) = (((2 : ℤ)) : ℂ) from by norm_num, Complex.norm_intCast]
    norm_num
  rw [h2]
  norm_num

end





end CyclotomicOrders.Pierce
