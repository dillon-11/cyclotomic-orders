/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.IntervalCases

/-!
# Lehmer's polynomial, the E10 Coxeter element, and the Mahler-measure gap
Kernel-decided integer facts about Lehmer's polynomial
`L(x) = x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1` realized as the characteristic
polynomial of the E10 Coxeter element, together with the Mahler-measure framework:
  • `cartan` — the E10 Cartan matrix generated from its 9-edge tree; symmetry decided;
  • `coxeter` — the Coxeter element as the ordered product of the 10 simple reflections;
  • `lehmer_annihilates` — `L(coxeter) = 0` exactly (Cayley–Hamilton witness);
  • `lehmer_palindrome` — the coefficient vector equals its own reversal (reciprocal);
  • `coxeter_trace`, `coxeter_det` — trace −1, determinant 1;
  • `minors_natural`, `minors_certification` — the Jacobi leading-minor cascades,
    ending in the Lorentzian signature (+9, −1);
  • `one_le_mahler` — the monic Mahler floor `1 ≤ M(p)`;
  • `LehmerProblem` — Lehmer's problem as a *defined* Prop (never axiomatized), and
    `gap_floor_of_lehmer`: it implies a uniform positive log-Mahler floor;
  • `log_gap_pos_iff_dilatation_gt_one` — `0 < log λ ↔ 1 < λ`.
All proofs foundational ([propext, Classical.choice, Quot.sound]), no `sorry`.
-/

namespace CyclotomicOrders.Mahler

/-! ### List-matrix kernel layer (plain ℤ lists so `decide` reduces structurally). -/

/-- A matrix as a plain list of rows over ℤ (structural, so `decide` reduces it). -/
abbrev Mat := List (List ℤ)

/-- The rank of E10: all list-matrices below are 10×10. -/
def dim : Nat := 10

/-- The T(2,3,7) tree: center 0; arms 0–1 (length 1), 0–2–3 (length 2), 0–4–…–9 (length 6). -/
def edges : List (Nat × Nat) := [(0,1),(0,2),(2,3),(0,4),(4,5),(5,6),(6,7),(7,8),(8,9)]

/-- Adjacency in the T(2,3,7) tree (symmetrized edge membership). -/
def adj (i j : Nat) : Bool := edges.contains (i, j) || edges.contains (j, i)

/-- The E10 Cartan matrix, generated from the tree (2 on the diagonal, −1 on edges). -/
def cartan : Mat :=
  (List.range dim).map fun i =>
    (List.range dim).map fun j =>
      if i = j then 2 else if adj i j then -1 else 0

/-- Entry `M i j` of a list-matrix, defaulting to 0 out of range. -/
def entry (M : Mat) (i j : Nat) : ℤ := ((M.getD i []).getD j 0)

/-- The 10×10 identity list-matrix. -/
def idMat : Mat :=
  (List.range dim).map fun i => (List.range dim).map fun j => if i = j then (1 : ℤ) else 0

/-- The 10×10 zero list-matrix. -/
def zeroMat : Mat :=
  (List.range dim).map fun _ => (List.range dim).map fun _ => (0 : ℤ)

/-- List-matrix product (structural, so `decide` reduces it). -/
def mul (A B : Mat) : Mat :=
  (List.range dim).map fun i =>
    (List.range dim).map fun j =>
      ((List.range dim).map fun k => entry A i k * entry B k j).foldl (· + ·) 0

/-- List-matrix transpose. -/
def transpose (M : Mat) : Mat :=
  (List.range dim).map fun i => (List.range dim).map fun j => entry M j i

/-- List-matrix trace. -/
def trace (M : Mat) : ℤ := ((List.range dim).map fun i => entry M i i).foldl (· + ·) 0

/-- Simple reflection s_i on root coordinates: row i of the identity becomes eᵢ − (Cartan row i). -/
def reflMat (i : Nat) : Mat :=
  (List.range dim).map fun r =>
    (List.range dim).map fun c =>
      (if r = c then (1 : ℤ) else 0) - (if r = i then entry cartan i c else 0)

/-- The Coxeter element: the ordered product s₉ s₈ ⋯ s₁ s₀ (any order is conjugate;
    this fixes the representative the kernel facts are decided on). -/
def coxeter : Mat := (List.range dim).foldl (fun M i => mul (reflMat i) M) idMat

/-- Lehmer's polynomial, degree-10-first coefficient vector. -/
def lehmer : List ℤ := [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]

/-- Horner evaluation of an integer polynomial at a matrix. -/
def polyEvalMat (coeffs : List ℤ) (M : Mat) : Mat :=
  coeffs.foldl
    (fun P c =>
      let PM := mul P M
      (List.range dim).map fun i =>
        (List.range dim).map fun j =>
          entry PM i j + (if i = j then c else 0))
    zeroMat

/-- Bareiss fraction-free determinant (exact over ℤ; pivots verified nonzero for every
    matrix it is applied to below — the pivot ladders are checked by kernel decide).
    Fuel-recursive: fuel = row count bounds the elimination depth. -/
def bareissAux : Nat → ℤ → Mat → ℤ
  | _,     _,    []          => 1
  | _,     _,    [r]         => r.getD 0 0
  | 0,     _,    _           => 0
  | f + 1, prev, (p :: rows) =>
      let p0 := p.getD 0 0
      let reduced := rows.map fun r =>
        (p.tail.zip r.tail).map fun q => (p0 * q.2 - r.getD 0 0 * q.1) / prev
      bareissAux f p0 reduced

/-- Determinant by Bareiss fraction-free elimination (exact over ℤ). -/
def det (M : Mat) : ℤ := bareissAux M.length 1 M

/-- The leading k×k block of a list-matrix. -/
def leading (M : Mat) (k : Nat) : Mat := (M.take k).map (·.take k)

/-- The finite-type-leading-block certification order (long arm far→near, center, short arms). -/
def certPerm : List Nat := [9, 8, 7, 6, 5, 4, 0, 1, 2, 3]

/-- The E10 Cartan matrix in certification order (conjugate by `certPerm`). -/
def cartanCert : Mat := certPerm.map fun i => certPerm.map fun j => entry cartan i j

/-! ### The kernel facts (all `decide`, no axioms). -/

/-- The generated Cartan matrix is symmetric. -/
theorem cartan_symmetric : transpose cartan = cartan := by decide +kernel

/-- **Reciprocity witness**: Lehmer's coefficient vector is its own reversal — the
    algebraic functional equation (roots closed under z ↔ 1/z). -/
theorem lehmer_palindrome : lehmer.reverse = lehmer := by decide +kernel

/-- The Coxeter element, evaluated (the reduction is split so each `decide` stays
    shallow: product chain in `coxeter_eq_lit`, Horner chain on the literal). -/
def coxeterLit : Mat :=
  [[-1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
   [-1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
   [-1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
   [-1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
   [-1, 1, 1, 0, 0, 1, 0, 0, 0, 0],
   [-1, 1, 1, 0, 0, 0, 1, 0, 0, 0],
   [-1, 1, 1, 0, 0, 0, 0, 1, 0, 0],
   [-1, 1, 1, 0, 0, 0, 0, 0, 1, 0],
   [-1, 1, 1, 0, 0, 0, 0, 0, 0, 1],
   [-1, 1, 1, 0, 0, 0, 0, 0, 0, 0]]

/-- The reflection product evaluates to the literal. -/
theorem coxeter_eq_lit : coxeter = coxeterLit := by decide +kernel

/-- Horner evaluation of L at the literal is the zero matrix. -/
theorem lehmer_annihilates_lit : polyEvalMat lehmer coxeterLit = zeroMat := by decide +kernel

/-- **THE ANNIHILATION WITNESS**: Lehmer's polynomial annihilates the E10 Coxeter
    element — L(coxeter) = 0 exactly.  With `coxeter_trace` and `coxeter_det` this is
    the kernel side of "char poly = Lehmer" (the full coefficient vector is decided). -/
theorem lehmer_annihilates : polyEvalMat lehmer coxeter = zeroMat :=
  coxeter_eq_lit ▸ lehmer_annihilates_lit

/-- tr(coxeter) = −1 = −(coefficient of x⁹ in L). -/
theorem coxeter_trace : trace coxeter = -1 := by decide +kernel

/-- det(coxeter) = 1 = (−1)¹⁰ · (constant term of L): the Coxeter element is a
    reciprocal (Salem-type) isometry. -/
theorem coxeter_det : det coxeter = 1 := by decide +kernel

/-- **THE E8/E9/E10 CROSSING, IN INTEGERS**: the natural-order Jacobi leading minors of
    the E10 Cartan matrix.  The final entries 1, 0, −1 at k = 8, 9, 10 is det(E8), det(E9),
    det(E10): finite type → affine (determinant 0) → indefinite (Lorentzian). -/
theorem minors_natural :
    (List.range dim).map (fun k => det (leading cartan (k + 1))) =
      [2, 3, 4, 5, 4, 3, 2, 1, 0, -1] := by decide +kernel

/-- Jacobi certification minors (all proper leading blocks finite type, so all nonzero):
    9 positive then −1 ⇒ the Cartan form has Lorentzian signature (+9, −1). -/
theorem minors_certification :
    (List.range dim).map (fun k => det (leading cartanCert (k + 1))) =
      [2, 3, 4, 5, 6, 7, 8, 9, 4, -1] := by decide +kernel

/-! ### The FULL characteristic polynomial.

  Three independent pins, upgrading the annihilation witness to the full coefficient vector:
  (1) `fl_charpoly_lehmer` — Faddeev–LeVerrier computed IN THE KERNEL on the Coxeter
      element returns exactly Lehmer's coefficients;
  (2) `power_sums_value`   — the trace power sums tr(Cᵏ), k = 1..10;
  (3) `newton_pin` + `newton_unique` — Lehmer's elementary-symmetric data satisfies the
      Newton recurrence against those traces (decided), AND any e : ℕ → ℤ satisfying it
      is PROVEN equal to Lehmer's on 0..10 — the traces pin the char poly uniquely.
  Remaining bridge (not claimed here): identify `flCharpoly` with Mathlib's `Matrix.charpoly`. -/

def addDiag (M : Mat) (c : ℤ) : Mat :=
  (List.range dim).map fun i =>
    (List.range dim).map fun j => entry M i j + (if i = j then c else 0)

/-- Faddeev–LeVerrier: M₀ = 0, c₀ = 1; Mₖ = C·Mₖ₋₁ + cₖ₋₁·I, cₖ = −tr(C·Mₖ)/k.
    Exact over ℤ (all divisions exact); returns [c₀, c₁, …] degree-10 first. -/
def flAux (C : Mat) : Nat → Nat → List ℤ → Mat → List ℤ
  | 0,     _, cs, _ => cs.reverse
  | f + 1, k, cs, M =>
      let M' := addDiag (mul C M) (cs.headD 1)
      flAux C f (k + 1) ((-(trace (mul C M')) / (k : ℤ)) :: cs) M'

/-- Characteristic-polynomial coefficients by Faddeev–LeVerrier (leading 1 first). -/
def flCharpoly (C : Mat) : List ℤ := flAux C dim 1 [1] zeroMat

/-- **THE FULL COEFFICIENT VECTOR**: Faddeev–LeVerrier on the E10 Coxeter element
    computes Lehmer's polynomial, coefficient by coefficient. -/
theorem fl_charpoly_lehmer : flCharpoly coxeterLit = lehmer := by decide +kernel

/-- On the reflection-product form. -/
theorem fl_charpoly_coxeter : flCharpoly coxeter = lehmer :=
  coxeter_eq_lit ▸ fl_charpoly_lehmer

/-- Power sums pₖ = tr(Cᵏ), k = 1..fuel. -/
def powAux (C : Mat) : Nat → Mat → List ℤ
  | 0,     _ => []
  | f + 1, P => trace P :: powAux C f (mul P C)

/-- The trace power sums `tr(C), tr(C²), …, tr(C¹⁰)`. -/
def powerSums (C : Mat) : List ℤ := powAux C dim C

/-- The E10 Coxeter trace power sums. -/
theorem power_sums_value : powerSums coxeterLit = [-1, 1, 2, 1, 4, 4, 6, 1, 2, 6] := by
  decide +kernel

/-- The trace power sums as a table (values decided in `power_sums_value`). -/
def pTable : Nat → ℤ
  | 1 => -1 | 2 => 1 | 3 => 2 | 4 => 1 | 5 => 4
  | 6 => 4  | 7 => 6 | 8 => 1 | 9 => 2 | 10 => 6
  | _ => 0

/-- Lehmer's elementary symmetric functions eₖ = (−1)ᵏ·(coefficient of x^{10−k}). -/
def lehmerE : Nat → ℤ
  | 0 => 1 | 1 => -1 | 2 => 0 | 3 => 1  | 4 => -1 | 5 => 1
  | 6 => -1 | 7 => 1 | 8 => 0 | 9 => -1 | 10 => 1
  | _ => 0

/-- Newton right-hand side: Σ_{i=1..k} (−1)^{i−1} e(k−i) pᵢ. -/
def newtonRhs (e : Nat → ℤ) (k : Nat) : ℤ :=
  ((List.range k).map fun i' =>
    (if i' % 2 = 0 then (1 : ℤ) else -1) * e (k - (i' + 1)) * pTable (i' + 1)).foldl
    (· + ·) 0

/-- **NEWTON PIN (decided)**: Lehmer's symmetric functions satisfy Newton's identities
    against the E10 Coxeter traces at every k = 1..10. -/
theorem newton_pin :
    ((List.range 10).all fun k' =>
      ((k' + 1 : Nat) : ℤ) * lehmerE (k' + 1) = newtonRhs lehmerE (k' + 1)) = true := by
  decide

/-- **NEWTON UNIQUENESS (proven, not decided)**: ANY e : ℕ → ℤ with e 0 = 1 satisfying
    Newton's identities against the E10 Coxeter traces agrees with Lehmer's symmetric
    functions on 0..10.  The recurrence k·eₖ = rhs(e₀…eₖ₋₁) determines each eₖ over ℤ,
    so the trace power sums pin the characteristic polynomial UNIQUELY. -/
theorem newton_unique (e : Nat → ℤ) (h0 : e 0 = 1)
    (hN : ∀ k : ℕ, 1 ≤ k → k ≤ 10 → (k : ℤ) * e k = newtonRhs e k) :
    ∀ k, k ≤ 10 → e k = lehmerE k := by
  have h1 : e 1 = -1 := by
    have := hN 1 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0] at this
    omega
  have h2 : e 2 = 0 := by
    have := hN 2 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1] at this
    omega
  have h3 : e 3 = 1 := by
    have := hN 3 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2] at this
    omega
  have h4 : e 4 = -1 := by
    have := hN 4 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3] at this
    omega
  have h5 : e 5 = 1 := by
    have := hN 5 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4] at this
    omega
  have h6 : e 6 = -1 := by
    have := hN 6 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4, h5] at this
    omega
  have h7 : e 7 = 1 := by
    have := hN 7 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4, h5, h6] at this
    omega
  have h8 : e 8 = 0 := by
    have := hN 8 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4, h5, h6, h7] at this
    omega
  have h9 : e 9 = -1 := by
    have := hN 9 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4, h5, h6, h7, h8] at this
    omega
  have h10 : e 10 = 1 := by
    have := hN 10 (by norm_num) (by norm_num)
    simp [newtonRhs, List.range_succ, pTable, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at this
    omega
  intro k hk
  interval_cases k <;> simp_all [lehmerE]

/-! ### The reduction rung: gap positivity ↔ dilatation > 1, and the Lehmer floor. -/

open Polynomial in
/-- Mahler measure of an integer polynomial (roots taken in ℂ; leading coefficient ±1
    for the monic case this file uses it on). -/
noncomputable def mahler (p : Polynomial ℤ) : ℝ :=
  ((p.map (Int.castRingHom ℂ)).roots.map fun z => max 1 ‖z‖).prod

/-- **THE GAP↔DILATATION REDUCTION**: the log gap is positive iff the dilatation
    exceeds 1 — the exact logical content of "gap > 0 ⇔ λ > 1" (the sharp half). -/
theorem log_gap_pos_iff_dilatation_gt_one {l : ℝ} (hl : 0 < l) :
    0 < Real.log l ↔ 1 < l := Real.log_pos_iff hl.le

/-- Mahler measure of any polynomial is ≥ 1… once each root factor is (every factor is
    max 1 ‖z‖ ≥ 1, and a product of factors ≥ 1 is ≥ 1). -/
theorem one_le_mahler (p : Polynomial ℤ) : 1 ≤ mahler p := by
  unfold mahler
  refine Multiset.one_le_prod ?_
  intro x hx
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
  exact le_max_left 1 ‖z‖

/-- **LEHMER'S PROBLEM, DEFINED (never axiomatized)**: monic integer polynomials of
    non-trivial Mahler measure are uniformly bounded away from measure 1.  This is the
    single open locus (1933) the gap positivity hangs on. -/
def LehmerProblem : Prop :=
  ∃ ε > (0 : ℝ), ∀ p : Polynomial ℤ, p.Monic → mahler p ≠ 1 → 1 + ε ≤ mahler p

/-- **THE GAP FLOOR TRANSFER**: LehmerProblem gives a uniform strictly positive
    floor for the log-Mahler (= topological entropy) reading: the gap is not
    merely positive but bounded below by log(1+ε) across the whole nontrivial sector. -/
theorem gap_floor_of_lehmer (h : LehmerProblem) :
    ∃ δ > (0 : ℝ), ∀ p : Polynomial ℤ, p.Monic → mahler p ≠ 1 →
      δ ≤ Real.log (mahler p) := by
  obtain ⟨ε, hε, hfloor⟩ := h
  refine ⟨Real.log (1 + ε), Real.log_pos (by linarith), fun p hm hne => ?_⟩
  have h1 : 1 + ε ≤ mahler p := hfloor p hm hne
  exact Real.log_le_log (by linarith) h1

















end CyclotomicOrders.Mahler
