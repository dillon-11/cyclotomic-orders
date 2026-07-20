/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# the parity-tower law over ZMod p, structural + analytic halves.
The harmonic ladders H^(r)_m = Σ_{k=1}^m (1/k)^r over ZMod p obey a mirror
symmetry that SELECTS character parity:
  • `sum_pow_eq_zero`      — Σ_{x ∈ ZMod p} x^r = 0 when (p−1) ∤ r;
  • `ladder_total_eq_zero` — the full ladder vanishes: H^(r)_{p−1} = 0;
  • `ladder_reflect`       — THE MIRROR: H^(r)_{p−1−m} = (−1)^(r+1)·H^(r)_m;
  • `floor_complement`     — the cut identity (f−j)·p/f = p − 1 − j·p/f
    (f coprime to p, 0 < j < f);
  • `parity_vanish`        — THE SELECTION RULE: a weight with the wrong
    parity, χ(f−j) = (−1)^r χ(j), projects the ladder to zero.  Structural
    half of the parity-tower law; the analytic half (the coupling of the
    surviving projection to (−1)^r (f^r/r) χ̄(p) B_{p−r,χ}) is the
    Bernoulli half below.
  • `chi5_projection_eq_band` — THE COLLAPSE at f = 5, r = 1: the
    χ₅-projection equals −2·(H_{⌊2p/5⌋} − H_{⌊p/5⌋}): the character
    projection law and the golden Glaisher band form coincide.
-/

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The r-th harmonic ladder prefix over `ZMod p`. -/
def ladder (p : ℕ) (r m : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 m, ((k : ZMod p)⁻¹) ^ r

/-- **Power sums over the whole field vanish off the resonant exponents**:
    `Σ_{x ∈ ZMod p} x^r = 0` when `(p−1) ∤ r`. -/
lemma sum_pow_eq_zero {r : ℕ} (hr : ¬ (p - 1) ∣ r) :
    ∑ x : ZMod p, x ^ r = 0 := by
  haveI hp := Fact.out (p := p.Prime)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hu
    simpa [ZMod.card_units_eq_totient, Nat.totient_prime hp,
      Nat.card_eq_fintype_card] using h
  have hgr : ((u : ZMod p)) ^ r ≠ 1 := by
    intro hc
    apply hr
    have hgu : u ^ r = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hc
    have := orderOf_dvd_of_pow_eq_one hgu
    rwa [hord] at this
  have hg0 : ((u : ZMod p)) ≠ 0 := Units.ne_zero u
  have hperm : ∑ x : ZMod p, x ^ r
      = ((u : ZMod p)) ^ r * ∑ x : ZMod p, x ^ r := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ ((u : ZMod p)) hg0)
      (fun x => x ^ r)]
    apply Finset.sum_congr rfl
    intro x _
    simp [mul_pow]
  have hz : (1 - ((u : ZMod p)) ^ r) * ∑ x : ZMod p, x ^ r = 0 := by
    linear_combination hperm
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (by linear_combination -h) hgr
  · exact h

/-- The full-range ladder is the field power sum of the inverses. -/
lemma ladder_total_eq_sum {r : ℕ} (hr0 : r ≠ 0) :
    ladder p r (p - 1) = ∑ x : ZMod p, (x⁻¹) ^ r := by
  haveI hp := Fact.out (p := p.Prime)
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [ladder]
  have hins : (range p) = insert 0 (Icc 1 (p - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    have := hp.two_le
    omega
  have hsum : ∑ k ∈ range p, (((k : ZMod p))⁻¹) ^ r
      = ∑ k ∈ Icc 1 (p - 1), (((k : ZMod p))⁻¹) ^ r := by
    rw [hins, Finset.sum_insert (by simp)]
    simp [zero_pow hr0]
  rw [← hsum]
  exact Finset.sum_nbij' (fun k : ℕ => ((k : ZMod p))) (fun x => x.val)
    (fun k _ => mem_univ _)
    (fun x _ => by simpa only [mem_range] using ZMod.val_lt x)
    (fun k hk => ZMod.val_cast_of_lt (by simpa only [mem_range] using hk))
    (fun x _ => ZMod.natCast_rightInverse x)
    (fun k _ => rfl)

/-- **The full ladder vanishes**: `H^(r)_{p−1} = 0` when `(p−1) ∤ r`. -/
lemma ladder_total_eq_zero {r : ℕ} (hr : ¬ (p - 1) ∣ r) :
    ladder p r (p - 1) = 0 := by
  have hr0 : r ≠ 0 := fun h => hr (h ▸ dvd_zero _)
  rw [ladder_total_eq_sum hr0]
  have h := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x : ZMod p => x ^ r)
  simp only [Equiv.inv_apply] at h
  rw [h]
  exact sum_pow_eq_zero hr

/-- **The mirror**: `H^(r)_{p−1−m} = (−1)^(r+1) · H^(r)_m` for `m ≤ p − 1`. -/
lemma ladder_reflect {r m : ℕ} (hr : ¬ (p - 1) ∣ r) (hm : m ≤ p - 1) :
    ladder p r (p - 1 - m) = (-1 : ZMod p) ^ (r + 1) * ladder p r m := by
  haveI hp := Fact.out (p := p.Prime)
  have h2 : 2 ≤ p := hp.two_le
  have hIco : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  have hIoc : ∀ n : ℕ, ladder p r n = ∑ k ∈ Ioc 0 n, (((k : ZMod p))⁻¹) ^ r :=
    fun n => by rw [ladder, hIco]
  have hsplit : (∑ k ∈ Ioc 0 (p - 1 - m), (((k : ZMod p))⁻¹) ^ r)
      + ∑ k ∈ Ioc (p - 1 - m) (p - 1), (((k : ZMod p))⁻¹) ^ r
      = ∑ k ∈ Ioc 0 (p - 1), (((k : ZMod p))⁻¹) ^ r :=
    Finset.sum_Ioc_consecutive _ (by omega) (by omega)
  have htail : ∑ k ∈ Ioc (p - 1 - m) (p - 1), (((k : ZMod p))⁻¹) ^ r
      = (-1 : ZMod p) ^ r * ladder p r m := by
    rw [ladder, Finset.mul_sum]
    refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_Ioc] at hk
      simp only [mem_Icc]
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      simp only [mem_Ioc]
      omega
    · intro k hk
      simp only [mem_Ioc] at hk
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      omega
    · intro k hk
      simp only [mem_Ioc] at hk
      change (((k : ZMod p))⁻¹) ^ r
          = (-1 : ZMod p) ^ r * ((((p - k : ℕ) : ZMod p))⁻¹) ^ r
      have hcast : ((k : ZMod p)) = -(((p - k : ℕ) : ZMod p)) := by
        rw [Nat.cast_sub (show k ≤ p by omega)]
        simp
      rw [hcast, inv_neg, neg_pow]
  rw [← hIoc, ← hIoc] at hsplit
  rw [ladder_total_eq_zero hr, htail] at hsplit
  have : ladder p r (p - 1 - m) = -((-1 : ZMod p) ^ r * ladder p r m) := by
    linear_combination hsplit
  rw [this, pow_succ]
  ring

/-- **The cut identity**: for `f` coprime to `p` and `0 < j < f`,
    `(f−j)·p/f = p − 1 − j·p/f` (Nat division). -/
lemma floor_complement {f j : ℕ} (hco : Nat.Coprime p f) (hj : 0 < j)
    (hjf : j < f) : (f - j) * p / f = p - 1 - j * p / f := by
  haveI hp := Fact.out (p := p.Prime)
  have hf0 : 0 < f := by omega
  set q := j * p / f with hq
  set s := j * p % f with hs
  have hqm : f * q + s = j * p := Nat.div_add_mod (j * p) f
  have hslt : s < f := Nat.mod_lt _ hf0
  have hs0 : s ≠ 0 := by
    intro hc
    have hdvd : f ∣ j * p := Nat.dvd_of_mod_eq_zero (hs ▸ hc)
    have hcop : Nat.Coprime f p := Nat.coprime_comm.mp hco
    have hfj : f ∣ j := hcop.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd hj hfj
    omega
  have hjp_lt : j * p < f * p := by
    exact (Nat.mul_lt_mul_right hp.pos).mpr hjf
  have hqlt : q < p := by
    rw [hq]
    exact Nat.div_lt_of_lt_mul (by omega)
  have key : (f - j) * p = f * (p - 1 - q) + (f - s) := by
    have hq1 : q ≤ p - 1 := Nat.le_pred_of_lt hqlt
    have hp1 : 1 ≤ p := hp.pos
    have hqmZ : (f : ℤ) * q + s = j * p := by exact_mod_cast hqm
    zify [Nat.le_of_lt hjf, Nat.le_of_lt hslt, hq1, hp1]
    linear_combination hqmZ
  rw [key, Nat.mul_add_div hf0, Nat.div_eq_of_lt (by omega)]
  omega

/-- **The parity selection rule**: a weight `χ` with the wrong mirror parity,
    `χ(f−j) = (−1)^r χ(j)`, projects the ladder to zero. -/
theorem parity_vanish {f r : ℕ} (χ : ℕ → ZMod p) (hco : Nat.Coprime p f)
    (hr : ¬ (p - 1) ∣ r) (hf : 2 ≤ f) (hp2 : p ≠ 2)
    (hχ : ∀ j, 0 < j → j < f → χ (f - j) = (-1 : ZMod p) ^ r * χ j) :
    ∑ j ∈ Icc 1 (f - 1), χ j * ladder p r (j * p / f) = 0 := by
  haveI hp := Fact.out (p := p.Prime)
  set T := ∑ j ∈ Icc 1 (f - 1), χ j * ladder p r (j * p / f) with hT
  have hre : T = ∑ j ∈ Icc 1 (f - 1),
      χ (f - j) * ladder p r ((f - j) * p / f) := by
    rw [hT]
    refine Finset.sum_nbij' (fun j => f - j) (fun j => f - j)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_Icc] at hj ⊢
      omega
    · intro j hj
      simp only [mem_Icc] at hj ⊢
      omega
    · intro j hj
      simp only [mem_Icc] at hj
      omega
    · intro j hj
      simp only [mem_Icc] at hj
      omega
    · intro j hj
      simp only [mem_Icc] at hj
      have : f - (f - j) = j := by omega
      rw [this]
  have hsq : (-1 : ZMod p) ^ r * (-1 : ZMod p) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  have hstep : ∀ j ∈ Icc 1 (f - 1),
      χ (f - j) * ladder p r ((f - j) * p / f)
        = -(χ j * ladder p r (j * p / f)) := by
    intro j hj
    simp only [mem_Icc] at hj
    have hdiv : j * p / f ≤ p - 1 := by
      have h1 : j * p < f * p := (Nat.mul_lt_mul_right hp.pos).mpr (by omega)
      have h2 : j * p / f < p := Nat.div_lt_of_lt_mul (by omega)
      omega
    rw [hχ j hj.1 (by omega), floor_complement hco hj.1 (by omega),
      ladder_reflect hr hdiv, pow_succ]
    calc ((-1 : ZMod p) ^ r * χ j)
          * ((-1 : ZMod p) ^ r * (-1) * ladder p r (j * p / f))
        = ((-1 : ZMod p) ^ r * (-1 : ZMod p) ^ r)
          * (-1) * (χ j * ladder p r (j * p / f)) := by ring
      _ = -(χ j * ladder p r (j * p / f)) := by rw [hsq]; ring
  have h2T : T + T = 0 := by
    nth_rewrite 2 [hre]
    rw [hT, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hstep j hj]
    ring
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have hdvd : p ∣ 2 := by
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hc
      exact (ZMod.natCast_eq_zero_iff 2 p).mp this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have : (2 : ZMod p) * T = 0 := by linear_combination h2T
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2ne
  · exact h

/-- **The collapse at f = 5**: the χ₅-projection of the harmonic ladder equals
    the band form — the character projection law and the golden Glaisher
    band law are the same statement. -/
theorem chi5_projection_eq_band (hco : Nat.Coprime p 5)
    (hr : ¬ (p - 1) ∣ 1) :
    ladder p 1 (1 * p / 5) - ladder p 1 (2 * p / 5)
      - ladder p 1 (3 * p / 5) + ladder p 1 (4 * p / 5)
    = -2 * (ladder p 1 (2 * p / 5) - ladder p 1 (1 * p / 5)) := by
  haveI hp := Fact.out (p := p.Prime)
  have hlt : ∀ j : ℕ, 0 < j → j < 5 → j * p / 5 ≤ p - 1 := by
    intro j hj hj5
    have h1 : j * p < 5 * p := (Nat.mul_lt_mul_right hp.pos).mpr hj5
    have h2 : j * p / 5 < p := Nat.div_lt_of_lt_mul (by omega)
    omega
  have h4 : ladder p 1 (4 * p / 5) = ladder p 1 (1 * p / 5) := by
    have hfc := floor_complement (f := 5) (j := 1) hco (by norm_num)
      (by norm_num)
    rw [show (4 : ℕ) = 5 - 1 by norm_num, hfc,
      ladder_reflect hr (hlt 1 (by norm_num) (by norm_num))]
    norm_num
  have h3 : ladder p 1 (3 * p / 5) = ladder p 1 (2 * p / 5) := by
    have hfc := floor_complement (f := 5) (j := 2) hco (by norm_num)
      (by norm_num)
    rw [show (3 : ℕ) = 5 - 2 by norm_num, hfc,
      ladder_reflect hr (hlt 2 (by norm_num) (by norm_num))]
    norm_num
  rw [h4, h3]
  ring


/-- **The Faulhaber gate — first rung of the analytic half**: on the range
    `1 ≤ k ≤ m ≤ p−1` every summand of the ladder is a plain power,
    `(1/k)^r = k^(p−1−r)`, by Fermat's little theorem.  This rewrites the
    ladder into the polynomial power-sum form that Bernoulli/Faulhaber
    machinery speaks (`Finset.sum_range_pow`), which is where the analytic
    half of the parity-tower law — the coupling of the surviving projection
    to `(−1)^r (f^r/r) χ̄(p) B_{p−r,χ}` — lives. -/
theorem ladder_eq_sum_pow {r m : ℕ} (hrp : r ≤ p - 2) (hm : m ≤ p - 1) :
    ladder p r m = ∑ k ∈ Icc 1 m, ((k : ZMod p)) ^ (p - 1 - r) := by
  haveI hp := Fact.out (p := p.Prime)
  unfold ladder
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [mem_Icc] at hk
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff k p).mp h
    have hkp : k < p := by
      have := hp.two_le
      omega
    exact absurd (Nat.eq_zero_of_dvd_of_lt this hkp
      |>.symm ▸ hk.1) (by omega)
  have h1 : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
  have hmul : (k : ZMod p) ^ (p - 1 - r) * (k : ZMod p) ^ r = 1 := by
    rw [← pow_add]
    have hexp : p - 1 - r + r = p - 1 := by
      have := hp.two_le
      omega
    rw [hexp, h1]
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_left hmul).symm

/-- The range form: with the `k = 0` term dead (exponent positive), the
    ladder is literally the Faulhaber left-hand side `Σ_{k < m+1} k^(p−1−r)`. -/
theorem ladder_eq_range_pow {r m : ℕ} (hrp : r ≤ p - 2) (hm : m ≤ p - 1) :
    ladder p r m = ∑ k ∈ Finset.range (m + 1), ((k : ZMod p)) ^ (p - 1 - r) := by
  haveI hp := Fact.out (p := p.Prime)
  rw [ladder_eq_sum_pow hrp hm]
  have hIcc : Icc 1 m = Ioc 0 m := by
    ext k
    simp [Nat.lt_iff_add_one_le]
  have hrange : Finset.range (m + 1) = Icc 0 m := by
    ext k
    simp
  rw [hIcc, hrange, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le m)]
  have hzero : ((0 : ℕ) : ZMod p) ^ (p - 1 - r) = 0 := by
    have hpos : 0 < p - 1 - r := by
      have := hp.two_le
      omega
    simp [zero_pow hpos.ne']
  rw [hzero, add_zero]


/-! ### The Bernoulli half of the parity-tower law

Von Staudt–Clausen is dodged entirely: Bernoulli numbers are DEFINED over
`ZMod p` by the classical recurrence, and Faulhaber's formula is proven
formally from that recurrence — every division is by an invertible element.
`bmod p i` agrees with the true `B_i mod p` for `i ≤ p−2`; at `i = p−1`
(where the true denominator contains `p`) it is the regularized value. -/

/-- Bernoulli numbers over `ZMod p`: `B_0 = 1`,
    `B_{m+1} = −(m+2)⁻¹ · Σ_{j≤m} C(m+2,j)·B_j`. -/
def bmod (p : ℕ) : ℕ → ZMod p
  | 0 => 1
  | m + 1 =>
      -((m : ZMod p) + 2)⁻¹ *
        ∑ j ∈ (Finset.range (m + 1)).attach,
          (((m + 2).choose j.1 : ℕ) : ZMod p) * bmod p j.1
  decreasing_by exact Finset.mem_range.mp j.2

lemma bmod_zero : bmod p 0 = 1 := by rw [bmod]

/-- The defining recurrence, cleared of the inverse:
    `Σ_{j ≤ m+1} C(m+2,j)·B_j = 0` whenever `m+2` is invertible. -/
lemma bmod_step {m : ℕ} (hm0 : ((m : ZMod p) + 2) ≠ 0) :
    ∑ j ∈ Finset.range (m + 2), (((m + 2).choose j : ℕ) : ZMod p) * bmod p j
      = 0 := by
  rw [Finset.sum_range_succ]
  have hunf : bmod p (m + 1)
      = -((m : ZMod p) + 2)⁻¹ *
        ∑ j ∈ Finset.range (m + 1),
          (((m + 2).choose j : ℕ) : ZMod p) * bmod p j := by
    rw [bmod]
    congr 1
    exact Finset.sum_attach (Finset.range (m + 1))
      (fun a => (((m + 2).choose a : ℕ) : ZMod p) * bmod p a)
  rw [hunf, Nat.choose_succ_self_right]
  push_cast
  field_simp
  ring

/-- `Σ_{i ≤ M} C(M,i)·B_i = B_M` for `M ≥ 2` invertible. -/
lemma bmod_sum_choose {M : ℕ} (h2 : 2 ≤ M) (hM : ((M : ℕ) : ZMod p) ≠ 0) :
    ∑ i ∈ Finset.range (M + 1), ((M.choose i : ℕ) : ZMod p) * bmod p i
      = bmod p M := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  rw [Finset.sum_range_succ, Nat.choose_self]
  push_cast at hM
  rw [bmod_step hM]
  simp

/-- The δ-corrected form at every index: `Σ_{i≤M} C(M,i)·B_i = B_M + [M=1]`. -/
lemma bmod_sum_choose_all {M : ℕ}
    (hinv : ∀ M', 2 ≤ M' → M' ≤ M → ((M' : ℕ) : ZMod p) ≠ 0) :
    ∑ i ∈ Finset.range (M + 1), ((M.choose i : ℕ) : ZMod p) * bmod p i
      = bmod p M + (if M = 1 then 1 else 0) := by
  match M with
  | 0 => simp [bmod_zero]
  | 1 =>
      rw [Finset.sum_range_succ, Finset.sum_range_one, bmod_zero]
      simp [add_comm]
  | m + 2 =>
      rw [if_neg (by omega), add_zero]
      exact bmod_sum_choose (by omega) (hinv (m + 2) (by omega) le_rfl)

/-- Trinomial revision: `C(n,i)·C(n−i,k) = C(n,k)·C(n−k,i)`. -/
lemma choose_trinomial (n i k : ℕ) :
    n.choose i * (n - i).choose k = n.choose k * (n - k).choose i := by
  have h1 := Nat.choose_mul (n := n) (k := i + k) (s := i) (Nat.le_add_right i k)
  have h2 := Nat.choose_mul (n := n) (k := i + k) (s := k) (Nat.le_add_left k i)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel] at h2
  have hsym : (i + k).choose i = (i + k).choose k := by
    have := Nat.choose_symm (n := i + k) (k := k) (Nat.le_add_left k i)
    simpa [Nat.add_sub_cancel] using this
  rw [← h1, hsym, h2]

/-- Evaluation of the degree-`n` Bernoulli polynomial over `ZMod p`. -/
def bpolyEval (p n : ℕ) (x : ZMod p) : ZMod p :=
  ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ZMod p) * bmod p i * x ^ (n - i)

lemma bpolyEval_zero {n : ℕ} : bpolyEval p n 0 = bmod p n := by
  unfold bpolyEval
  rw [Finset.sum_range_succ]
  rw [Finset.sum_eq_zero fun i hi => by
    have : n - i ≠ 0 := by
      simp only [Finset.mem_range] at hi
      omega
    simp [zero_pow this]]
  simp

/-- **The telescoping step**: `B_n(x+1) = B_n(x) + n·x^(n−1)`. -/
lemma bpolyEval_step {n : ℕ} (hn : 1 ≤ n)
    (hinv : ∀ M, 2 ≤ M → M ≤ n → ((M : ℕ) : ZMod p) ≠ 0) (x : ZMod p) :
    bpolyEval p n (x + 1) = bpolyEval p n x + (n : ZMod p) * x ^ (n - 1) := by
  have hexp : ∀ i : ℕ, (x + 1) ^ (n - i)
      = ∑ k ∈ Finset.range (n + 1), (((n - i).choose k : ℕ) : ZMod p) * x ^ k := by
    intro i
    rw [add_pow]
    rw [show ∑ k ∈ Finset.range (n - i + 1),
          x ^ k * (1 : ZMod p) ^ (n - i - k) * ((n - i).choose k : ℕ)
        = ∑ k ∈ Finset.range (n - i + 1),
          (((n - i).choose k : ℕ) : ZMod p) * x ^ k from
      Finset.sum_congr rfl fun k _ => by ring]
    refine Finset.sum_subset
      (fun t ht => by
        simp only [Finset.mem_range] at ht ⊢
        omega) ?_
    intro k hk hknot
    have hlt : n - i < k := by
      simp only [Finset.mem_range] at hk hknot
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  have hswap : bpolyEval p n (x + 1)
      = ∑ k ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (n + 1),
            ((n.choose i : ℕ) : ZMod p) * (((n - i).choose k : ℕ) : ZMod p)
              * bmod p i) * x ^ k := by
    unfold bpolyEval
    simp_rw [hexp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hinner : ∀ k ∈ Finset.range (n + 1),
      (∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℕ) : ZMod p) * (((n - i).choose k : ℕ) : ZMod p)
            * bmod p i)
        = ((n.choose k : ℕ) : ZMod p)
            * (bmod p (n - k) + (if n - k = 1 then 1 else 0)) := by
    intro k hk
    have htri : ∀ i ∈ Finset.range (n + 1),
        ((n.choose i : ℕ) : ZMod p) * (((n - i).choose k : ℕ) : ZMod p)
            * bmod p i
          = ((n.choose k : ℕ) : ZMod p)
            * ((((n - k).choose i : ℕ) : ZMod p) * bmod p i) := by
      intro i _
      have := choose_trinomial n i k
      have hc : ((n.choose i * (n - i).choose k : ℕ) : ZMod p)
          = ((n.choose k * (n - k).choose i : ℕ) : ZMod p) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ZMod p)) this
      push_cast at hc
      linear_combination bmod p i * hc
    rw [Finset.sum_congr rfl htri, ← Finset.mul_sum]
    congr 1
    have hshrink : ∑ i ∈ Finset.range (n + 1),
        (((n - k).choose i : ℕ) : ZMod p) * bmod p i
          = ∑ i ∈ Finset.range (n - k + 1),
            (((n - k).choose i : ℕ) : ZMod p) * bmod p i := by
      symm
      refine Finset.sum_subset
        (fun t ht => by
          simp only [Finset.mem_range] at ht ⊢
          omega) ?_
      intro i hi hinot
      have hlt : n - k < i := by
        simp only [Finset.mem_range] at hi hinot
        omega
      simp [Nat.choose_eq_zero_of_lt hlt]
    rw [hshrink]
    exact bmod_sum_choose_all fun M' h2 hle =>
      hinv M' h2 (le_trans hle (Nat.sub_le n k))
  have hmid : bpolyEval p n (x + 1)
      = ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℕ) : ZMod p)
            * (bmod p (n - k) + (if n - k = 1 then 1 else 0)) * x ^ k := by
    rw [hswap]
    exact Finset.sum_congr rfl fun k hk => by rw [hinner k hk]
  have hsplit : ∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℕ) : ZMod p)
        * (bmod p (n - k) + (if n - k = 1 then 1 else 0)) * x ^ k
      = (∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℕ) : ZMod p) * bmod p (n - k) * x ^ k)
        + ∑ k ∈ Finset.range (n + 1),
          (if k = n - 1 then ((n.choose k : ℕ) : ZMod p) * x ^ k else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    by_cases hcase : k = n - 1
    · subst hcase
      rw [if_pos rfl, if_pos (by omega)]
      ring
    · rw [if_neg hcase, if_neg (by omega)]
      ring
  have hdelta : ∑ k ∈ Finset.range (n + 1),
      (if k = n - 1 then ((n.choose k : ℕ) : ZMod p) * x ^ k else 0)
        = (n : ZMod p) * x ^ (n - 1) := by
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) (n - 1)
      (fun k => ((n.choose k : ℕ) : ZMod p) * x ^ k)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    have hch : n.choose (n - 1) = n := by
      rw [Nat.choose_symm hn, Nat.choose_one_right]
    rw [hch]
  have hreflect : ∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℕ) : ZMod p) * bmod p (n - k) * x ^ k
        = bpolyEval p n x := by
    unfold bpolyEval
    rw [← Finset.sum_range_reflect
      (fun k => ((n.choose k : ℕ) : ZMod p) * bmod p (n - k) * x ^ k) (n + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have h1 : n + 1 - 1 - j = n - j := by omega
    have h2 : n - (n - j) = j := by omega
    have h3 : n.choose (n - j) = n.choose j := Nat.choose_symm (by omega)
    rw [h1, h2, h3]
  rw [hmid, hsplit, hdelta, hreflect]

/-- **Faulhaber over `ZMod p`**: `n·Σ_{k<m} k^(n−1) = B_n(m) − B_n`. -/
theorem sum_pow_bernoulli {n : ℕ} (m : ℕ) (hn : 1 ≤ n)
    (hinv : ∀ M, 2 ≤ M → M ≤ n → ((M : ℕ) : ZMod p) ≠ 0) :
    (n : ZMod p) * ∑ k ∈ Finset.range m, ((k : ZMod p)) ^ (n - 1)
      = bpolyEval p n (m : ℕ) - bmod p n := by
  induction m with
  | zero => simp [bpolyEval_zero]
  | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hcast : (((M + 1 : ℕ)) : ZMod p) = ((M : ℕ) : ZMod p) + 1 := by
        push_cast
        ring
      rw [hcast, bpolyEval_step hn hinv]
      ring

/-- **THE LADDER–BERNOULLI COUPLING** — the Bernoulli half of the
    parity-tower law: `(p−r)·H^(r)_m = B_{p−r}(m+1) − B_{p−r}` over `ZMod p`.  With
    `parity_vanish` and `floor_complement` this reduces the parity-tower law
    to the χ-projection of Bernoulli-polynomial values at the cuts. -/
theorem ladder_bernoulli {r m : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 2)
    (hm : m ≤ p - 1) :
    ((p - r : ℕ) : ZMod p) * ladder p r m
      = bpolyEval p (p - r) ((m + 1 : ℕ)) - bmod p (p - r) := by
  haveI hp := Fact.out (p := p.Prime)
  rw [ladder_eq_range_pow hrp hm]
  have hexp : p - 1 - r = (p - r) - 1 := by omega
  have hinv : ∀ M, 2 ≤ M → M ≤ p - r → ((M : ℕ) : ZMod p) ≠ 0 := by
    intro M h2 hle h0
    have hdvd := (ZMod.natCast_eq_zero_iff M p).mp h0
    have hMp : M < p := by
      have := hp.two_le
      omega
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hn : 1 ≤ p - r := by
    have := hp.two_le
    omega
  have := sum_pow_bernoulli (p := p) (n := p - r) (m + 1) hn hinv
  rw [hexp]
  exact this

/-- The cut value in `ZMod p`: `⌊jp/f⌋ ≡ −(jp mod f)·f⁻¹` — the seed of the
    `χ̄(p)` Euler factor (the residue `j·p mod f` drives the reindexing that
    produces the conjugate character). -/
lemma floor_cut_cast {f j : ℕ} (hf : ((f : ℕ) : ZMod p) ≠ 0) :
    ((j * p / f : ℕ) : ZMod p)
      = -((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹ := by
  have h := Nat.div_add_mod (j * p) f
  have hcast : ((f : ℕ) : ZMod p) * ((j * p / f : ℕ) : ZMod p)
      + ((j * p % f : ℕ) : ZMod p) = 0 := by
    have h2 := congrArg (fun t : ℕ => (t : ZMod p)) h
    push_cast at h2
    rw [h2]
    simp
  have hfi := mul_inv_cancel₀ hf
  linear_combination ((f : ℕ) : ZMod p)⁻¹ * hcast
    - ((j * p / f : ℕ) : ZMod p) * hfi


/-! ### The χ-projection assembly — the full parity-tower law

No reflection formula and no odd-Bernoulli vanishing are needed: the parity
hypothesis `χ(f−a) = ε·χ(a)` substitutes for both via the `a ↦ f−a` reindex,
and the conjugate Euler factor `χ̄(p)` is produced by the `j ↦ j·p mod f`
bijection (its seed is `floor_cut_cast`).  Everything is finite algebra over
`ZMod p`. -/

/-- Generalized Bernoulli number over `ZMod p`, census normalization
    `f^(n−1)·Σ_a χ(a)·B_n(a/f)`. -/
def genBern (p n f : ℕ) (χ : ℕ → ZMod p) : ZMod p :=
  ((f : ℕ) : ZMod p) ^ (n - 1) *
    ∑ a ∈ Finset.Icc 1 (f - 1),
      χ a * bpolyEval p n ((a : ZMod p) * ((f : ℕ) : ZMod p)⁻¹)

/-- **THE PARITY-TOWER LAW** (inverse-free form).  For any weight `χ` mod `f`
    with `Σχ = 0`, the multiplicative twist `χ(jp mod f) = χ(p mod f)·χ(j)`,
    and parity `χ(f−a) = ε·χ(a)`:
    `χ(p̄)·(p−r)·Σ_j χ(j)·H^(r)_{⌊jp/f⌋} = ε·Σ_a χ(a)·B_{p−r}(a/f)`.
    Unwinding mod p (`p−r ≡ −r`, `f^(p−1) ≡ 1`) this is the numerically
    verified law `Σ_j χ(j)·H^(r)_{⌊jp/f⌋} ≡ (−1)^r (f^r/r)·χ̄(p)·B_{p−r,χ}`
    — for BOTH parities at once (on the wrong
    parity `parity_vanish` makes the left side vanish, so this identity
    then proves `B_{p−r,χ} ≡ 0`, the mod-p shadow of the classical
    vanishing). -/
theorem parity_tower_law {f r : ℕ} (χ : ℕ → ZMod p) (ε : ZMod p)
    (hr : 1 ≤ r) (hrp : r ≤ p - 2) (hco : Nat.Coprime p f) (hf : 2 ≤ f)
    (hsum : ∑ j ∈ Finset.Icc 1 (f - 1), χ j = 0)
    (htw : ∀ j, χ (j * p % f) = χ (p % f) * χ j)
    (hpar : ∀ a, 0 < a → a < f → χ (f - a) = ε * χ a) :
    χ (p % f) * (((p - r : ℕ) : ZMod p)) *
        ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)
      = ε * ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            ((a : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
  haveI hp := Fact.out (p := p.Prime)
  have hF0 : ((f : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hdvd := (ZMod.natCast_eq_zero_iff f p).mp h
    have h1 : p ∣ Nat.gcd p f := Nat.dvd_gcd dvd_rfl hdvd
    rw [Nat.Coprime.gcd_eq_one hco] at h1
    have := Nat.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  -- Step A: Bernoulli-ize each ladder; the bmod tail dies on Σχ = 0
  have hdiv : ∀ j, 1 ≤ j → j ≤ f - 1 → j * p / f ≤ p - 1 := by
    intro j h1 h2
    have hlt : j * p < f * p := (Nat.mul_lt_mul_right hp.pos).mpr (by omega)
    have h3 : j * p / f < p := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hterm : ∀ j ∈ Finset.Icc 1 (f - 1),
      ((p - r : ℕ) : ZMod p) * (χ j * ladder p r (j * p / f))
        = χ j * bpolyEval p (p - r) ((j * p / f + 1 : ℕ))
          - χ j * bmod p (p - r) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hlb := ladder_bernoulli (p := p) (r := r) (m := j * p / f)
      hr hrp (hdiv j hj.1 hj.2)
    linear_combination χ j * hlb
  have hA : ((p - r : ℕ) : ZMod p) *
      ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)
      = ∑ j ∈ Finset.Icc 1 (f - 1),
          χ j * bpolyEval p (p - r) ((j * p / f + 1 : ℕ)) := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.Icc 1 (f - 1),
          ((p - r : ℕ) : ZMod p) * (χ j * ladder p r (j * p / f))
        = ∑ j ∈ Finset.Icc 1 (f - 1),
            (χ j * bpolyEval p (p - r) ((j * p / f + 1 : ℕ))
              - χ j * bmod p (p - r)) := Finset.sum_congr rfl hterm
      _ = (∑ j ∈ Finset.Icc 1 (f - 1),
            χ j * bpolyEval p (p - r) ((j * p / f + 1 : ℕ)))
          - (∑ j ∈ Finset.Icc 1 (f - 1), χ j) * bmod p (p - r) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = ∑ j ∈ Finset.Icc 1 (f - 1),
            χ j * bpolyEval p (p - r) ((j * p / f + 1 : ℕ)) := by
          rw [hsum]
          ring
  -- Step B: cast the cut argument via floor_cut_cast
  have hcut : ∀ j : ℕ, ((j * p / f + 1 : ℕ) : ZMod p)
      = 1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹ := by
    intro j
    push_cast
    rw [floor_cut_cast hF0]
    ring
  have hAB : ((p - r : ℕ) : ZMod p) *
      ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)
      = ∑ j ∈ Finset.Icc 1 (f - 1),
          χ j * bpolyEval p (p - r)
            (1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
    rw [hA]
    exact Finset.sum_congr rfl fun j _ => by rw [← hcut j]
  -- Step C: twist and reindex j ↦ j·p mod f (the Euler factor)
  obtain ⟨pinv, hpinvlt, hpinv⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  have hcopinv : Nat.Coprime f pinv := by
    have hq := Nat.div_add_mod (p * pinv) f
    rw [hpinv] at hq
    have h1 : Nat.gcd f pinv ∣ p * pinv :=
      Dvd.dvd.mul_left (Nat.gcd_dvd_right f pinv) p
    have h2 : Nat.gcd f pinv ∣ f * (p * pinv / f) :=
      Dvd.dvd.mul_right (Nat.gcd_dvd_left f pinv) _
    have h3 : p * pinv - f * (p * pinv / f) = 1 := by omega
    have h4 := Nat.dvd_sub h1 h2
    rw [h3] at h4
    exact Nat.dvd_one.mp h4
  have hmem : ∀ j, 1 ≤ j → j ≤ f - 1 → 1 ≤ j * p % f ∧ j * p % f ≤ f - 1 := by
    intro j h1 h2
    have hlt : j * p % f < f := Nat.mod_lt _ (by omega)
    have hne : j * p % f ≠ 0 := by
      intro h0
      have hdvd : f ∣ j * p := Nat.dvd_of_mod_eq_zero h0
      have hj : f ∣ j := (Nat.Coprime.dvd_of_dvd_mul_right hco.symm) hdvd
      have := Nat.le_of_dvd (by omega) hj
      omega
    omega
  have hmem' : ∀ a, 1 ≤ a → a ≤ f - 1 →
      1 ≤ a * pinv % f ∧ a * pinv % f ≤ f - 1 := by
    intro a h1 h2
    have hlt : a * pinv % f < f := Nat.mod_lt _ (by omega)
    have hne : a * pinv % f ≠ 0 := by
      intro h0
      have hdvd : f ∣ a * pinv := Nat.dvd_of_mod_eq_zero h0
      have ha : f ∣ a := (Nat.Coprime.dvd_of_dvd_mul_right hcopinv) hdvd
      have := Nat.le_of_dvd (by omega) ha
      omega
    omega
  have hC : χ (p % f) * ∑ j ∈ Finset.Icc 1 (f - 1),
      χ j * bpolyEval p (p - r)
        (1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹)
      = ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            (1 - ((a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
    rw [Finset.mul_sum]
    have h1 : ∀ j ∈ Finset.Icc 1 (f - 1),
        χ (p % f) * (χ j * bpolyEval p (p - r)
          (1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹))
        = χ (j * p % f) * bpolyEval p (p - r)
          (1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
      intro j _
      rw [htw j]
      ring
    rw [Finset.sum_congr rfl h1]
    refine Finset.sum_nbij' (fun j => j * p % f) (fun a => a * pinv % f)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      exact hmem j hj.1 hj.2
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      exact hmem' a ha.1 ha.2
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      rw [Nat.mod_mul_mod, mul_assoc, Nat.mul_mod j (p * pinv) f, hpinv,
        mul_one, Nat.mod_mod_of_dvd _ dvd_rfl, Nat.mod_eq_of_lt (by omega)]
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      rw [Nat.mod_mul_mod, mul_assoc, mul_comm pinv p,
        Nat.mul_mod a (p * pinv) f, hpinv, mul_one,
        Nat.mod_mod_of_dvd _ dvd_rfl, Nat.mod_eq_of_lt (by omega)]
    · intro j _
      rfl
  -- Step D: the parity flip a ↦ f−a
  have hFi : ((f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ hF0
  have hD : ∑ a ∈ Finset.Icc 1 (f - 1),
      χ a * bpolyEval p (p - r)
        (1 - ((a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹)
      = ε * ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            ((a : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
    have hre : ∑ a ∈ Finset.Icc 1 (f - 1),
        χ a * bpolyEval p (p - r)
          (1 - ((a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹)
        = ∑ a ∈ Finset.Icc 1 (f - 1),
            χ (f - a) * bpolyEval p (p - r)
              (1 - ((f - a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
      refine Finset.sum_nbij' (fun a => f - a) (fun a => f - a)
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        have : f - (f - a) = a := by omega
        rw [this]
    rw [hre]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_Icc] at ha
    have hcastfa : ((f - a : ℕ) : ZMod p)
        = ((f : ℕ) : ZMod p) - ((a : ℕ) : ZMod p) := by
      have : a ≤ f := by omega
      push_cast [this]
      ring
    have harg : (1 : ZMod p) - ((f - a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹
        = ((a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹ := by
      rw [hcastfa]
      linear_combination -hFi
    rw [hpar a (by omega) (by omega), harg]
    ring
  calc χ (p % f) * (((p - r : ℕ) : ZMod p)) *
        ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)
      = χ (p % f) * (((p - r : ℕ) : ZMod p) *
          ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f)) := by
        ring
    _ = χ (p % f) * ∑ j ∈ Finset.Icc 1 (f - 1),
          χ j * bpolyEval p (p - r)
            (1 - ((j * p % f : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := by
        rw [hAB]
    _ = ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            (1 - ((a : ℕ) : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := hC
    _ = ε * ∑ a ∈ Finset.Icc 1 (f - 1),
          χ a * bpolyEval p (p - r)
            ((a : ZMod p) * ((f : ℕ) : ZMod p)⁻¹) := hD

/-- The `genBern`-normalized form of the parity-tower law. -/
theorem parity_tower_genBern {f r : ℕ} (χ : ℕ → ZMod p) (ε : ZMod p)
    (hr : 1 ≤ r) (hrp : r ≤ p - 2) (hco : Nat.Coprime p f) (hf : 2 ≤ f)
    (hsum : ∑ j ∈ Finset.Icc 1 (f - 1), χ j = 0)
    (htw : ∀ j, χ (j * p % f) = χ (p % f) * χ j)
    (hpar : ∀ a, 0 < a → a < f → χ (f - a) = ε * χ a) :
    ((f : ℕ) : ZMod p) ^ (p - r - 1) *
        (χ (p % f) * (((p - r : ℕ) : ZMod p)) *
          ∑ j ∈ Finset.Icc 1 (f - 1), χ j * ladder p r (j * p / f))
      = ε * genBern p (p - r) f χ := by
  have h := parity_tower_law χ ε hr hrp hco hf hsum htw hpar
  rw [genBern]
  linear_combination ((f : ℕ) : ZMod p) ^ (p - r - 1) * h

/-! ### Instantiation: the golden and silver bands in Bernoulli closed form -/

/-- The quadratic character mod 5 (`χ₅(±1) = 1`, `χ₅(±2) = −1`), valued in
    `ZMod p`. -/
def chiFive (p : ℕ) : ℕ → ZMod p := fun j =>
  if j % 5 = 1 ∨ j % 5 = 4 then 1
  else if j % 5 = 2 ∨ j % 5 = 3 then -1 else 0

/-- The quadratic character mod 8 (`χ₈(±1) = 1`, `χ₈(±3) = −1`), valued in
    `ZMod p`. -/
def chiEight (p : ℕ) : ℕ → ZMod p := fun j =>
  if j % 8 = 1 ∨ j % 8 = 7 then 1
  else if j % 8 = 3 ∨ j % 8 = 5 then -1 else 0

lemma sum_Icc_one_four {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 4, g j = g 1 + g 2 + g 3 + g 4 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    Finset.Icc_self, Finset.sum_singleton]

lemma sum_Icc_one_seven {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 7, g j
      = g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 := by
  rw [show (7 : ℕ) = 6 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    show (6 : ℕ) = 5 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    show (5 : ℕ) = 4 + 1 by norm_num, Finset.sum_Icc_succ_top (by omega),
    sum_Icc_one_four]

lemma chiFive_tw (j : ℕ) :
    chiFive p (j * p % 5) = chiFive p (p % 5) * chiFive p j := by
  have hkey : j * p % 5 = j % 5 * (p % 5) % 5 := Nat.mul_mod j p 5
  unfold chiFive
  rw [hkey]
  have hmm : ∀ n : ℕ, n % 5 % 5 = n % 5 := fun n => Nat.mod_mod_of_dvd n dvd_rfl
  simp only [hmm]
  rcases show p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4
      by omega with hp'|hp'|hp'|hp'|hp' <;>
    rcases show j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4
        by omega with hj'|hj'|hj'|hj'|hj' <;>
      norm_num [hp', hj']

lemma chiEight_tw (j : ℕ) :
    chiEight p (j * p % 8) = chiEight p (p % 8) * chiEight p j := by
  have hkey : j * p % 8 = j % 8 * (p % 8) % 8 := Nat.mul_mod j p 8
  unfold chiEight
  rw [hkey]
  have hmm : ∀ n : ℕ, n % 8 % 8 = n % 8 := fun n => Nat.mod_mod_of_dvd n dvd_rfl
  simp only [hmm]
  rcases show p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4
      ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7
      by omega with hp'|hp'|hp'|hp'|hp'|hp'|hp'|hp' <;>
    rcases show j % 8 = 0 ∨ j % 8 = 1 ∨ j % 8 = 2 ∨ j % 8 = 3 ∨ j % 8 = 4
        ∨ j % 8 = 5 ∨ j % 8 = 6 ∨ j % 8 = 7
        by omega with hj'|hj'|hj'|hj'|hj'|hj'|hj'|hj' <;>
      norm_num [hp', hj']

/-- **THE GOLDEN BAND IN BERNOULLI CLOSED FORM** (golden case).
    Combining the collapse `chi5_projection_eq_band`
    with the parity-tower law: the golden Glaisher band
    `H_{⌊2p/5⌋} − H_{⌊p/5⌋}` equals an explicit generalized-Bernoulli value.
    Inverse-free form:
    `χ₅(p̄)·(p−1)·(−2)·(H_{⌊2p/5⌋} − H_{⌊p/5⌋}) = Σ_a χ₅(a)·B_{p−1}(a/5)`. -/
theorem golden_band_bernoulli (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    chiFive p (p % 5) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (2 * p / 5) - ladder p 1 (1 * p / 5)))
      = ∑ a ∈ Finset.Icc 1 4,
          chiFive p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((5 : ℕ) : ZMod p)⁻¹) := by
  haveI hp := Fact.out (p := p.Prime)
  have hco : Nat.Coprime p 5 :=
    (Nat.coprime_primes hp (by norm_num)).mpr hp5
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hnd1 : ¬ (p - 1) ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  have hmaster := parity_tower_law (f := 5) (r := 1) (chiFive p) 1
    le_rfl (by omega) hco (by norm_num)
    (by rw [show (5 : ℕ) - 1 = 4 by norm_num, sum_Icc_one_four]
        norm_num [chiFive])
    (fun j => chiFive_tw j)
    (fun a h1 h2 => by interval_cases a <;> norm_num [chiFive])
  rw [show (5 : ℕ) - 1 = 4 by norm_num] at hmaster
  have hT : ∑ j ∈ Finset.Icc 1 4, chiFive p j * ladder p 1 (j * p / 5)
      = ladder p 1 (1 * p / 5) - ladder p 1 (2 * p / 5)
        - ladder p 1 (3 * p / 5) + ladder p 1 (4 * p / 5) := by
    rw [sum_Icc_one_four]
    norm_num [chiFive]
    ring
  rw [hT, chi5_projection_eq_band hco hnd1] at hmaster
  calc chiFive p (p % 5) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (2 * p / 5) - ladder p 1 (1 * p / 5)))
      = chiFive p (p % 5) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (2 * p / 5) - ladder p 1 (1 * p / 5))) := rfl
    _ = 1 * ∑ a ∈ Finset.Icc 1 4,
          chiFive p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((5 : ℕ) : ZMod p)⁻¹) := hmaster
    _ = ∑ a ∈ Finset.Icc 1 4,
          chiFive p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((5 : ℕ) : ZMod p)⁻¹) := one_mul _

/-- **The collapse at f = 8**: the χ₈-projection equals the silver band form
    (mirror pairs 7↔1, 5↔3 at r = 1). -/
theorem chi8_projection_eq_band (hco : Nat.Coprime p 8)
    (hr : ¬ (p - 1) ∣ 1) :
    ladder p 1 (1 * p / 8) - ladder p 1 (3 * p / 8)
      - ladder p 1 (5 * p / 8) + ladder p 1 (7 * p / 8)
    = -2 * (ladder p 1 (3 * p / 8) - ladder p 1 (1 * p / 8)) := by
  haveI hp := Fact.out (p := p.Prime)
  have hlt : ∀ j : ℕ, 0 < j → j < 8 → j * p / 8 ≤ p - 1 := by
    intro j hj hj8
    have h1 : j * p < 8 * p := (Nat.mul_lt_mul_right hp.pos).mpr hj8
    have h2 : j * p / 8 < p := Nat.div_lt_of_lt_mul (by omega)
    omega
  have h7 : ladder p 1 (7 * p / 8) = ladder p 1 (1 * p / 8) := by
    have hfc := floor_complement (f := 8) (j := 1) hco (by norm_num)
      (by norm_num)
    rw [show (7 : ℕ) = 8 - 1 by norm_num, hfc,
      ladder_reflect hr (hlt 1 (by norm_num) (by norm_num))]
    norm_num
  have h5 : ladder p 1 (5 * p / 8) = ladder p 1 (3 * p / 8) := by
    have hfc := floor_complement (f := 8) (j := 3) hco (by norm_num)
      (by norm_num)
    rw [show (5 : ℕ) = 8 - 3 by norm_num, hfc,
      ladder_reflect hr (hlt 3 (by norm_num) (by norm_num))]
    norm_num
  rw [h7, h5]
  ring

/-- **THE SILVER BAND IN BERNOULLI CLOSED FORM** (silver case):
    `χ₈(p̄)·(p−1)·(−2)·(H_{⌊3p/8⌋} − H_{⌊p/8⌋}) = Σ_a χ₈(a)·B_{p−1}(a/8)`. -/
theorem silver_band_bernoulli (hp2 : p ≠ 2) :
    chiEight p (p % 8) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (3 * p / 8) - ladder p 1 (1 * p / 8)))
      = ∑ a ∈ Finset.Icc 1 7,
          chiEight p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((8 : ℕ) : ZMod p)⁻¹) := by
  haveI hp := Fact.out (p := p.Prime)
  have hco : Nat.Coprime p 8 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    intro hdvd
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd
    have h2 := hp.dvd_of_dvd_pow hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hnd1 : ¬ (p - 1) ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  have hmaster := parity_tower_law (f := 8) (r := 1) (chiEight p) 1
    le_rfl (by omega) hco (by norm_num)
    (by rw [show (8 : ℕ) - 1 = 7 by norm_num, sum_Icc_one_seven]
        norm_num [chiEight])
    (fun j => chiEight_tw j)
    (fun a h1 h2 => by interval_cases a <;> norm_num [chiEight])
  rw [show (8 : ℕ) - 1 = 7 by norm_num] at hmaster
  have hT : ∑ j ∈ Finset.Icc 1 7, chiEight p j * ladder p 1 (j * p / 8)
      = ladder p 1 (1 * p / 8) - ladder p 1 (3 * p / 8)
        - ladder p 1 (5 * p / 8) + ladder p 1 (7 * p / 8) := by
    rw [sum_Icc_one_seven]
    norm_num [chiEight]
    ring
  rw [hT, chi8_projection_eq_band hco hnd1] at hmaster
  calc chiEight p (p % 8) * (((p - 1 : ℕ) : ZMod p)) *
        (-2 * (ladder p 1 (3 * p / 8) - ladder p 1 (1 * p / 8)))
      = 1 * ∑ a ∈ Finset.Icc 1 7,
          chiEight p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((8 : ℕ) : ZMod p)⁻¹) := hmaster
    _ = ∑ a ∈ Finset.Icc 1 7,
          chiEight p a * bpolyEval p (p - 1)
            ((a : ZMod p) * ((8 : ℕ) : ZMod p)⁻¹) := one_mul _


