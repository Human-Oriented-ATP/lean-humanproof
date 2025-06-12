import HumanProof.BoxIncremental
import HumanProof.RefinedDiscrTree.LibraryRewrite
import Mathlib.Tactic

open HumanProof

example (x : ℝ) : 1 ≤ 2 * Real.cosh x := by
  box_proofi
    rw [Real.cosh_eq x]
    rw [mul_div_cancel₀ (Real.exp x + Real.exp (-x)) (by simp)]
    #check Real.exp_pos
    backup
    grw [← Real.exp_pos]
    simp
    assume_goal hx
    push_neg at hx
    have : 0 < Real.exp (-x) := Real.exp_pos (-x)
    nth_grw 2 [← Real.exp_pos]
    simp
    grw [hx]


opaque bloom_bloom : Nat → Prop
opaque bla_bla : Nat → Prop

axiom bloom_axiom {n : Nat} (h : 100 < n) : bloom_bloom n

axiom bla_axiom {n : Nat} (h : 7 ∣ n) : bla_bla n

axiom exists_gt_and_dvd (a b : Nat) : ∃ c, a < c ∧ b ∣ c

example : ∃ n, bloom_bloom n ∧ bla_bla n := by
  box_proofi
    use ?_
    set_goal h
    constructor
    refine bloom_axiom ?_
    set_goal h.right
    refine bla_axiom ?_
    have := exists_gt_and_dvd 100 7
    box_obtain ⟨n, hn⟩ := this
    exact hn.2
    exact hn.1
