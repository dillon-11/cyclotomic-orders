/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# THE CYCLOTOMIC REPULSION FLOOR
Irreducible Salem configurations repel cyclotomic grids with a floor forced by
INTEGRALITY: for a monic integer polynomial p none of whose roots is a q-th root of
unity, the resultant `Res(p, X^q − 1) = ∏_ρ (ρ^q − 1)` is a NONZERO INTEGER, so the
product of the factor norms is ≥ 1.  For a Salem-shaped root multiset
`{λ, λ⁻¹} ∪ {e^{±iθ_j}}` each circle pair contributes at most `(2π‖qθ_j/2π‖)²`
(‖·‖ = distance to the nearest integer) and the λ-pair at most `λ^q`, giving
      1 ≤ λ^q · ∏_j (2π · dev(q·θ_j/2π))²          (dev u = |u − round u|)
— the measured census floor (2187 Salems × q ≤ 40, zero violations, min ratio
1.2162), now proven.  Mimicry corollary: if every phase sits within ε of the q-grid
then `1 ≤ λ^q (2πε)^{2r}` — exact mimicry (ε → 0) is impossible off the reducible
locus, and any mimicry certificate must let q grow (so
matched-below-depth-(q−1) is the exactness this floor caps).
Assembly:
  §1  dev + the arc bound  ‖e^{2πiu} − 1‖ ≤ 2π · dev u   (cos quadratic bound)
  §2  the integrality engine: Res over ℤ, mapped to ℂ (Mathlib resultant API)
  §3  THE FLOOR for Salem-shaped root multisets + the ε-mimicry corollary
No `sorry`, no `axiom`.
-/

open Polynomial Complex Real

namespace CyclotomicOrders

/-! ### 1. Distance to the nearest integer, and the arc bound. -/

/-- Distance from `u` to the nearest integer. -/
noncomputable def dev (u : ℝ) : ℝ := |u - round u|

/-- The circle deviation is nonnegative. -/
theorem dev_nonneg (u : ℝ) : 0 ≤ dev u := abs_nonneg _

/-- `dev(−u) = dev u`.  NOTE: `round(−u) = −round u` is FALSE at half-integer ties
    (round-half-up), but the distances still agree — the tie cases are both exactly
    1/2, forced by the integer sum `(−u − round(−u)) + (u − round u) ∈ ℤ` of two
    quantities each of absolute value ≤ 1/2. -/
theorem dev_neg (u : ℝ) : dev (-u) = dev u := by
  unfold dev
  set a := u - round u with hadef
  set b := (-u : ℝ) - round (-u) with hbdef
  have ha : |a| ≤ 1 / 2 := abs_sub_round u
  have hb : |b| ≤ 1 / 2 := abs_sub_round (-u)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, b + a = (m : ℝ) :=
    ⟨-(round (-u) + round u), by push_cast; rw [hadef, hbdef]; ring⟩
  have hmabs : |(m : ℝ)| ≤ 1 := by
    rw [← hm]
    calc |b + a| ≤ |b| + |a| := abs_add_le _ _
      _ ≤ 1 := by linarith
  have hmcases : m = 0 ∨ m = 1 ∨ m = -1 := by
    have h1 : |m| ≤ (1 : ℤ) := by exact_mod_cast hmabs
    rw [abs_le] at h1
    omega
  have haabs := abs_le.mp ha
  have hbabs := abs_le.mp hb
  rcases hmcases with h0 | h1 | h1'
  · have hba : b = -a := by
      have : b + a = 0 := by rw [hm, h0]; norm_num
      linarith
    rw [hba, abs_neg]
  · have hsum : b + a = 1 := by rw [hm, h1]; norm_num
    have hae : a = 1 / 2 := by linarith
    have hbe : b = 1 / 2 := by linarith
    rw [hae, hbe]
  · have hsum : b + a = -1 := by rw [hm, h1']; norm_num
    have hae : a = -(1 / 2) := by linarith
    have hbe : b = -(1 / 2) := by linarith
    rw [hae, hbe]

/-- `‖e^{iθ} − 1‖² = 2 − 2cos θ ≤ θ²`, so `‖e^{iθ} − 1‖ ≤ |θ|`. -/
theorem norm_exp_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ ≤ |θ| := by
  have hre : Complex.exp (θ * Complex.I) - 1
      = Complex.ofReal (Real.cos θ - 1) + Complex.ofReal (Real.sin θ) * Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  have hnorm : ‖Complex.exp (θ * Complex.I) - 1‖
      = Real.sqrt ((Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2) := by
    rw [hre, Complex.norm_add_mul_I]
  rw [hnorm]
  have hcos : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hval : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 ≤ θ ^ 2 := by
    have hpyth := Real.sin_sq_add_cos_sq θ
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    nlinarith
  calc Real.sqrt ((Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2)
      ≤ Real.sqrt (θ ^ 2) := Real.sqrt_le_sqrt hval
    _ = |θ| := Real.sqrt_sq_eq_abs θ

/-- **THE ARC BOUND**: `‖e^{2πiu} − 1‖ ≤ 2π · dev u`. -/
theorem norm_exp_two_pi_sub_one_le (u : ℝ) :
    ‖Complex.exp (2 * π * u * Complex.I) - 1‖ ≤ 2 * π * dev u := by
  have harg : (2 * (π : ℂ) * (u : ℂ)) * Complex.I
      = ((2 * π * (u - round u) : ℝ) : ℂ) * Complex.I
        + (round u : ℤ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  calc ‖Complex.exp (((2 * π * (u - round u) : ℝ) : ℂ) * Complex.I) - 1‖
      ≤ |2 * π * (u - round u)| := norm_exp_mul_I_sub_one_le _
    _ = 2 * π * dev u := by
        rw [abs_mul, dev, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

/-! ### 2. The integrality engine. -/

/-- The product `∏_ρ (ρ^q − 1)` over the complex roots of a monic integer polynomial
    is an INTEGER — the resultant `Res(p, X^q − 1)` computed over ℤ, mapped to ℂ. -/
theorem prod_pow_sub_one_int (p : ℤ[X]) (hm : p.Monic) (q : ℕ) :
    ∃ N : ℤ, (N : ℂ)
      = (((p.map (Int.castRingHom ℂ)).roots).map (fun z => z ^ q - 1)).prod := by
  set pC := p.map (Int.castRingHom ℂ) with hpC
  have hmC : pC.Monic := hm.map _
  have hsplits : pC.Splits := IsAlgClosed.splits pC
  have hgdeg : ((X : ℂ[X]) ^ q - 1).natDegree ≤ q := by
    calc ((X : ℂ[X]) ^ q - 1).natDegree
        ≤ max ((X : ℂ[X]) ^ q).natDegree (1 : ℂ[X]).natDegree := natDegree_sub_le _ _
      _ ≤ q := by simp
  refine ⟨p.resultant ((X : ℤ[X]) ^ q - 1) p.natDegree q, ?_⟩
  have hgmap : ((X : ℤ[X]) ^ q - 1).map (Int.castRingHom ℂ) = (X : ℂ[X]) ^ q - 1 := by
    simp
  have hmap : (Int.castRingHom ℂ) (p.resultant ((X : ℤ[X]) ^ q - 1) p.natDegree q)
      = pC.resultant ((X : ℂ[X]) ^ q - 1) p.natDegree q := by
    rw [← hgmap, hpC]
    exact (resultant_map_map _ _ _ _ (Int.castRingHom ℂ)).symm
  have hdegC : pC.natDegree = p.natDegree := hm.natDegree_map _
  have heval : pC.resultant ((X : ℂ[X]) ^ q - 1) pC.natDegree q
      = pC.leadingCoeff ^ q * (pC.roots.map (fun z => z ^ q - 1)).prod := by
    have := resultant_eq_prod_eval pC ((X : ℂ[X]) ^ q - 1) q hgdeg hsplits
    simpa using this
  rw [show ((p.resultant ((X : ℤ[X]) ^ q - 1) p.natDegree q : ℤ) : ℂ)
      = (Int.castRingHom ℂ) (p.resultant ((X : ℤ[X]) ^ q - 1) p.natDegree q) from rfl,
    hmap, ← hdegC, heval, hmC.leadingCoeff, one_pow, one_mul]

/-- **THE INTEGRALITY FLOOR**: if no root of `p` is a q-th root of unity, the product
    of the norms `‖ρ^q − 1‖` is at least 1. -/
theorem one_le_prod_norm (p : ℤ[X]) (hm : p.Monic) (q : ℕ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ q ≠ 1) :
    1 ≤ (((p.map (Int.castRingHom ℂ)).roots).map (fun z => ‖z ^ q - 1‖)).prod := by
  obtain ⟨N, hN⟩ := prod_pow_sub_one_int p hm q
  have hN0 : N ≠ 0 := by
    intro h
    rw [h] at hN
    have hzero : (((p.map (Int.castRingHom ℂ)).roots).map
        (fun z => z ^ q - 1)).prod = 0 := by
      simpa using hN.symm
    have h0mem := Multiset.prod_eq_zero_iff.mp hzero
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0mem
    exact hnru z hz (sub_eq_zero.mp hz0)
  have h1 : (1 : ℝ) ≤ ‖(N : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN0
  have hnormprod : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map (fun z => ‖z‖)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  calc (1 : ℝ) ≤ ‖(N : ℂ)‖ := h1
    _ = ‖(((p.map (Int.castRingHom ℂ)).roots).map (fun z => z ^ q - 1)).prod‖ := by
        rw [hN]
    _ = (((p.map (Int.castRingHom ℂ)).roots).map (fun z => ‖z ^ q - 1‖)).prod := by
        rw [hnormprod, Multiset.map_map]
        rfl

/-! ### 3. THE FLOOR for Salem-shaped configurations. -/

/-- The Salem-shaped root multiset: `λ`, `λ⁻¹`, and `r` conjugate circle pairs. -/
noncomputable def salemRoots (lam : ℝ) {r : ℕ} (θ : Fin r → ℝ) : Multiset ℂ :=
  (lam : ℂ) ::ₘ ((lam : ℂ)⁻¹ ::ₘ
    ((Finset.univ.val.map fun j => Complex.exp ((θ j : ℂ) * Complex.I))
      + (Finset.univ.val.map fun j => Complex.exp (-(θ j : ℂ) * Complex.I))))

/-- **THE CYCLOTOMIC REPULSION FLOOR** (proven): a monic integer polynomial
    with Salem-shaped roots (`λ > 1`, circle phases `θ_j`), none a q-th root of unity,
    satisfies  `1 ≤ λ^q · ∏_j (2π · dev(q·θ_j / 2π))²`.
    Integrality itself repels the configuration from every cyclotomic grid. -/
theorem repulsion_floor (p : ℤ[X]) (hm : p.Monic) (q : ℕ)
    (lam : ℝ) (hlam : 1 < lam) {r : ℕ} (θ : Fin r → ℝ)
    (hshape : (p.map (Int.castRingHom ℂ)).roots = salemRoots lam θ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ q ≠ 1) :
    1 ≤ lam ^ q * ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) ^ 2 := by
  have hfloor := one_le_prod_norm p hm q hnru
  rw [hshape] at hfloor
  unfold salemRoots at hfloor
  rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map] at hfloor
  simp only [Function.comp_def] at hfloor
  rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod] at hfloor
  have hlam0 : (0:ℝ) < lam := lt_trans one_pos hlam
  have hπC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- block bounds
  have hb1 : ‖((lam : ℂ)) ^ q - 1‖ ≤ lam ^ q := by
    have hcast : ((lam : ℂ)) ^ q - 1 = ((lam ^ q - 1 : ℝ) : ℂ) := by push_cast; ring
    have hq1 : (1:ℝ) ≤ lam ^ q := one_le_pow₀ (le_of_lt hlam)
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hb2 : ‖((lam : ℂ))⁻¹ ^ q - 1‖ ≤ 1 := by
    have hcast : ((lam : ℂ))⁻¹ ^ q - 1 = ((lam⁻¹ ^ q - 1 : ℝ) : ℂ) := by push_cast; ring
    have hlaminv : lam⁻¹ ^ q ≤ 1 :=
      pow_le_one₀ (le_of_lt (inv_pos.mpr hlam0)) (le_of_lt (inv_lt_one_of_one_lt₀ hlam))
    have hpos : (0:ℝ) < lam⁻¹ ^ q := by positivity
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hb3 : (∏ j : Fin r, ‖Complex.exp ((θ j : ℂ) * Complex.I) ^ q - 1‖)
      ≤ ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) := by
    apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j _
    have hexp : Complex.exp ((θ j : ℂ) * Complex.I) ^ q
        = Complex.exp (2 * (π : ℂ) * ((q * θ j / (2 * π) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [hexp]
    exact norm_exp_two_pi_sub_one_le _
  have hb4 : (∏ j : Fin r, ‖Complex.exp (-(θ j : ℂ) * Complex.I) ^ q - 1‖)
      ≤ ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) := by
    apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j _
    have hexp : Complex.exp (-(θ j : ℂ) * Complex.I) ^ q
        = Complex.exp (2 * (π : ℂ) * ((-(q * θ j / (2 * π)) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [hexp]
    calc ‖Complex.exp (2 * (π : ℂ) * ((-(q * θ j / (2 * π)) : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ 2 * π * dev (-(q * θ j / (2 * π))) := norm_exp_two_pi_sub_one_le _
      _ = 2 * π * dev (q * θ j / (2 * π)) := by rw [dev_neg]
  -- assemble
  set P := ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) with hP
  have hP0 : (0:ℝ) ≤ P := Finset.prod_nonneg fun j _ => by
    have := dev_nonneg (q * θ j / (2 * π)); positivity
  have hn3 : (0:ℝ) ≤ ∏ j : Fin r, ‖Complex.exp ((θ j : ℂ) * Complex.I) ^ q - 1‖ :=
    Finset.prod_nonneg fun j _ => norm_nonneg _
  have hn4 : (0:ℝ) ≤ ∏ j : Fin r, ‖Complex.exp (-(θ j : ℂ) * Complex.I) ^ q - 1‖ :=
    Finset.prod_nonneg fun j _ => norm_nonneg _
  have hchain : ‖((lam : ℂ)) ^ q - 1‖ * (‖((lam : ℂ))⁻¹ ^ q - 1‖ *
      ((∏ j : Fin r, ‖Complex.exp ((θ j : ℂ) * Complex.I) ^ q - 1‖) *
       (∏ j : Fin r, ‖Complex.exp (-(θ j : ℂ) * Complex.I) ^ q - 1‖)))
      ≤ lam ^ q * (1 * (P * P)) := by
    apply mul_le_mul hb1 _ (by positivity) (by positivity)
    apply mul_le_mul hb2 _ (by positivity) (by norm_num)
    exact mul_le_mul hb3 hb4 hn4 hP0
  have hsq : lam ^ q * (1 * (P * P))
      = lam ^ q * ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) ^ 2 := by
    rw [one_mul, hP, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun j _ => (sq _).symm
  linarith [le_trans hfloor hchain, hsq.le, hsq.ge]

/-- **THE MIMICRY COROLLARY**: if every phase sits within `ε` of the q-grid, then
    `1 ≤ λ^q (2πε)^{2r}` — exact mimicry (ε → 0) is impossible for a Salem-shaped
    integer configuration; any mimicry certificate must let q grow.  Combined with
    (a q-th-roots termination IS matched below depth q−1); the blindness
    window is bounded from both sides. -/
theorem mimicry_impossible (p : ℤ[X]) (hm : p.Monic) (q : ℕ)
    (lam : ℝ) (hlam : 1 < lam) {r : ℕ} (θ : Fin r → ℝ)
    (hshape : (p.map (Int.castRingHom ℂ)).roots = salemRoots lam θ)
    (hnru : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, z ^ q ≠ 1)
    (ε : ℝ) (_hε : 0 ≤ ε) (hdev : ∀ j : Fin r, dev (q * θ j / (2 * π)) ≤ ε) :
    1 ≤ lam ^ q * (2 * π * ε) ^ (2 * r) := by
  have h := repulsion_floor p hm q lam hlam θ hshape hnru
  have hmono : ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) ^ 2
      ≤ (2 * π * ε) ^ (2 * r) := by
    calc ∏ j : Fin r, (2 * π * dev (q * θ j / (2 * π))) ^ 2
        ≤ ∏ _j : Fin r, (2 * π * ε) ^ 2 := by
          apply Finset.prod_le_prod
          · intro j _
            have := dev_nonneg (q * θ j / (2 * π))
            positivity
          · intro j _
            have h1 := hdev j
            have h2 := dev_nonneg (q * θ j / (2 * π))
            have hle : 2 * π * dev (q * θ j / (2 * π)) ≤ 2 * π * ε := by
              have hpi : (0:ℝ) < 2 * π := by positivity
              nlinarith
            exact pow_le_pow_left₀ (by positivity) hle 2
      _ = (2 * π * ε) ^ (2 * r) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hlam0 : (0:ℝ) < lam ^ q := by positivity
  nlinarith [h, hmono]

end CyclotomicOrders
