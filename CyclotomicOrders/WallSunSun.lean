/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# the Wall–Sun–Sun predicate (Fibonacci-unit Wieferich).
The Fibonacci/golden analogue of the Wieferich condition: p is Wall–Sun–Sun
when `p² ∣ F_{p − (5/p)}` — the golden unit's order fails to lift from p
to p².  No example is known (searched past 2·10¹⁷ in the literature).
  • `wssIndex` — the rank index `p − (5/p)` via `p % 5` (quadratic reciprocity
    for 5 reads the Legendre symbol off the residue);
  • `IsWallSunSun` — the predicate, decidable;
  • `fib_wssIndex_dvd` — sanity at depth 1: `p ∣ F_{p − (5/p)}` for every
    prime `p < 100` (the classical rank-of-apparition divisibility), kernel-
    decided — certifying the index convention is the right one;
  • `no_wallSunSun_below_100` — depth 2 is empty below 100, kernel-decided.
Declared at root level (no namespace): the definitions are part of the
challenge statement surface.
-/

/-- The Wall–Sun–Sun rank index `p − (5/p)`: `p − 1` when `5` is a quadratic
    residue mod `p` (`p ≡ ±1 (mod 5)`), `p + 1` when not (`p ≡ ±2 (mod 5)`),
    and `p` itself at `p = 5` (the ramified prime). -/
def wssIndex (p : ℕ) : ℕ :=
  if p % 5 = 1 ∨ p % 5 = 4 then p - 1
  else if p % 5 = 2 ∨ p % 5 = 3 then p + 1
  else p

/-- **The Wall–Sun–Sun condition**: `p² ∣ F_{p − (5/p)}` — the Fibonacci
    unit's Wieferich condition. -/
def IsWallSunSun (p : ℕ) : Prop := p ^ 2 ∣ Nat.fib (wssIndex p)

instance (p : ℕ) : Decidable (IsWallSunSun p) := by unfold IsWallSunSun; infer_instance

/-- Depth-1 sanity for the index convention: every prime `p < 100` divides
    `F_{p − (5/p)}` (the classical rank-of-apparition divisibility). -/
theorem fib_wssIndex_dvd : ∀ p < 100, p.Prime → p ∣ Nat.fib (wssIndex p) := by decide

/-- **No Wall–Sun–Sun prime below 100** (kernel-decided; the literature extends
    the null past 2·10¹⁷). -/
theorem no_wallSunSun_below_100 : ∀ p < 100, p.Prime → ¬ IsWallSunSun p := by decide

/-- 2 is not Wall–Sun–Sun (`4 ∤ F₃ = 2`). -/
theorem not_wallSunSun_two : ¬ IsWallSunSun 2 := by decide

/-- 5, the ramified prime of the Fibonacci unit, is not Wall–Sun–Sun
    (`25 ∤ F₅ = 5`). -/
theorem not_wallSunSun_five : ¬ IsWallSunSun 5 := by decide
