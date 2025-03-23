
universe u

variable {α : Type u}

theorem _root_.List.merge_ne_nil_of_right {le} {xs ys : List α} (hy : ys ≠ []) : xs.merge ys le ≠ [] := by
  cases xs with
  | nil => simp [hy]
  | cons =>
    cases ys with
    | nil => contradiction
    | cons => unfold List.merge; split <;> simp

theorem _root_.List.merge_ne_nil_of_left {le} {xs ys : List α} (hx : xs ≠ []) : xs.merge ys le ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons =>
    cases ys with
    | nil => simp
    | cons => unfold List.merge; split <;> simp

@[simp]
theorem _root_.List.count_merge [BEq α] {le : α → α → Bool} (l₁ l₂ : List α) (a : α) :
    (l₁.merge l₂ le).count a = l₁.count a + l₂.count a := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simp
    | cons y l₂ ih₂ =>
      unfold List.merge
      split <;> simp only [List.count_cons, ih₁, ih₂] <;> split <;> omega
