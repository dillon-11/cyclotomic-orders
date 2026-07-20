import Lake
open Lake DSL

package cyclotomicorders where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0-rc1"

lean_lib Challenge where
  globs := #[.one `Challenge]

@[default_target]
lean_lib CyclotomicOrders where
  globs := #[.andSubmodules `CyclotomicOrders]
