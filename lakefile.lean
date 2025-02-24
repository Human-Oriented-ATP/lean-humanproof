import Lake
open Lake DSL

package «HumanProof» where
  -- add package configuration options here

lean_lib «HumanProof» where
  -- add library configuration options here
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_exe «humanproof» where
  root := `«HumanProof»

require "leanprover-community" / "mathlib"
