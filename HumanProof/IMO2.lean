import HumanProof.Basic
import Mathlib
import RwMod

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
  refine ⟨?N, ?_, ?goal2, ?goal1⟩
  apply Int.modEq_zero_iff_dvd.mp
  apply Int.ModEq.add_left_cancel' (-b ^ ?N); ring_nf
  on_goal 2 => apply Int.modEq_zero_iff_dvd.mp
  on_goal 2 => apply Int.ModEq.add_left_cancel' (-a ^ ?N); ring_nf
  rw_mod ?goal2

  skip

#eval 0
#check Int.ModEq._left_cancel'

#check modEq_add_
