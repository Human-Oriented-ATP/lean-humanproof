import HumanProof.BoxIncremental
import Mathlib

example (a : Nat) (l : List Nat) (h1 : a ∉ l) (h2 : l.Nodup)
: (a::l).Nodup := by exact List.Nodup.cons h1 h2

theorem add_distinct {α : Type} (a : α) (l : List α) (goal : Prop)
  (hPrev : (a::l).Nodup → goal)
  (h : a ∉ l)
  : (l.Nodup → goal) := by
  intro hNodup
  apply hPrev
  apply List.Nodup.cons
  apply h
  apply hNodup

theorem distinct_start {α : Type} (l : List α) :
    (([] : List α).Nodup → l.Nodup) → l.Nodup := by
  intro h
  apply h
  exact List.nodup_nil

theorem distinct_finish {α : Type} {l : List α} :
    (l.Nodup → l.Nodup) := id

open HumanProof in
theorem group_problem (G : Type) [Group G]
    (a b : G) (hab : a*b ≠ b*a) :
    -- (hncomm : ¬ ∀ a b : G, a*b = b*a) :
    ∃ elems : List G, elems.length ≥ 6 ∧ elems.Nodup := by
  box_proofi
    -- simp at hncomm
    -- induction hncomm
    existsi ?elems
    constructor
    apply distinct_start
    backup
    apply add_distinct a
    simp only [List.not_mem_nil, not_false_eq_true]
    backup
    apply add_distinct b
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro eq
    rw [eq] at hab
    exact hab rfl
    backup
    apply add_distinct 1
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    intro eq
    simp only [← eq, one_mul, mul_one, ne_eq, not_true_eq_false] at hab
    intro eq
    simp only [← eq, mul_one, one_mul, ne_eq, not_true_eq_false] at hab
    backup
    apply add_distinct (a*b)
    simp only [List.mem_cons, mul_eq_right, mul_eq_left, List.not_mem_nil, or_false,
      not_or]
    refine ⟨?_,?_,?_⟩
    intro eq
    simp only [eq, mul_one, one_mul, ne_eq, not_true_eq_false] at hab
    intro eq
    simp only [eq, one_mul, mul_one, ne_eq, not_true_eq_false] at hab
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    simp only [eq, one_div, inv_mul_cancel, mul_inv_cancel, ne_eq, not_true_eq_false] at hab
    backup
    apply add_distinct (b*a)
    simp only [List.mem_cons, mul_eq_left, mul_eq_right, List.not_mem_nil, or_false,
      not_or]
    refine ⟨?_,?_,?_,?_⟩
    intro eq
    simp only [eq, mul_one, one_mul, ne_eq, not_true_eq_false] at hab
    intro eq
    simp only [eq, one_mul, mul_one, ne_eq, not_true_eq_false] at hab
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    simp only [eq, one_div, mul_inv_cancel, inv_mul_cancel, ne_eq, not_true_eq_false] at hab
    intro eq
    exact hab eq.symm
    backup
    apply add_distinct (a*a)
    simp only [List.mem_cons, mul_left_inj, mul_right_inj, mul_eq_left, List.not_mem_nil,
      or_false, or_self_left, not_or]
    refine ⟨?_,?_,?_,?_⟩
    intro eq
    simp only [eq, one_mul, mul_one, ne_eq, not_true_eq_false] at hab
    intro eq
    simp only [← eq, mul_assoc, ne_eq, not_true_eq_false] at hab
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    rw [eq] at hab
    simp at hab
    revert eq
    simp
    assume_goal ainv
    intro eq
    simp [eq] at hab
    exact distinct_finish
    simp!
    simp only [not_not] at ainv
    backup
    apply add_distinct (b*b)
    simp only [List.mem_cons, mul_right_inj, mul_left_inj, mul_eq_left, List.not_mem_nil,
      or_false, or_self_left, not_or]
    refine ⟨?_,?_,?_,?_⟩
    intro eq
    rw [← eq] at hab
    simp! [mul_assoc] at hab
    intro eq
    simp! [eq] at hab
    assume_goal hbb
    intro eq
    simp [eq] at hab
    exact distinct_finish
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ge_iff_le, le_refl]
    backup
    apply add_distinct (a*b*a)
    simp only [List.mem_cons, mul_left_inj, mul_eq_right, mul_eq_left, List.not_mem_nil,
      or_false, or_self_left, not_or]
    refine ⟨?_,?_,?_,?_⟩
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    simp [eq] at hab
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    rw [div_eq_mul_inv, ← ainv] at eq
    exact hab eq
    intro eq
    apply eq_div_iff_mul_eq'.mpr at eq
    rw [one_div, ← ainv, mul_eq_left] at eq
    simp only [eq, mul_one, one_mul, ne_eq, not_true_eq_false] at hab
    intro eq
    simp only [eq, one_mul, mul_one, ne_eq, not_true_eq_false] at hab
    exact distinct_finish
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ge_iff_le, le_refl]
