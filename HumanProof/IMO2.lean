import HumanProof.Basic
import Mathlib
/-
free variables a,b,n0 : Z
metavariables:
M : Z (context: a,b)
N : Z (context: a,b,n0)
Assumptions:
* a > 1
* b > 1
Constraints (goals):
* M > 1
* N > n0
* M | a^N + b
* M | b^N + a
-/
example (a b : ℤ) (ha : a > 1) (hb : b > 1) : ∃ M : ℤ, M > 1 ∧ ∀ n0 : ℤ, ∃ N : Nat, N > n0 ∧ M ∣ a^N + b ∧ M ∣ b^N + a := by
  box_proof
  refine ⟨?m, ?_, ?_⟩
  intro n0
  refine ⟨?N, ?_, ?_, ?_⟩
  apply Int.modEq_zero_iff_dvd.mp
  on_goal 2 => apply Int.modEq_zero_iff_dvd.mp
  apply Int.modEq_add_left_cancel' (-a)


#eval 0
#check Int.modEq_add_left_cancel'
