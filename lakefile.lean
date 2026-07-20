/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Lake
open Lake DSL

package cyclotomicorders where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0-rc1"

lean_lib Challenge where
  globs := #[.one `Challenge]

@[default_target]
lean_lib CyclotomicOrders where
  globs := #[.andSubmodules `CyclotomicOrders]
