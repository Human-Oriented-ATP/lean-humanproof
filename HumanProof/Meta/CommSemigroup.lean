import HumanProof.Meta.BinTree
import Mathlib.Logic.Basic
import Mathlib.Util.AtomM

universe u v

class CommSemigroup (α : Type u) extends Add α where
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a

variable {α : Type u}

theorem CommSemigroup.add_left_comm [inst : CommSemigroup α] (a b c : α) :
    a + (b + c) = b + (a + c) := by
  rw [← inst.add_assoc, ← inst.add_assoc, inst.add_comm a b]

inductive CommSemigroupExpr where
| add  : CommSemigroupExpr → CommSemigroupExpr → CommSemigroupExpr
| atom : Nat → CommSemigroupExpr

namespace CommSemigroupExpr

variable {n : Nat}

-- class AbstractedExpr (α : Type u) (ι : outParam (Type v)) where
--   eval : (ι → Expr) → α → Expr
section EquivOfCount

def count (i : Nat) : CommSemigroupExpr → Nat
  | .add a b => a.count i + b.count i
  | .atom j => if j == i then 1 else 0

noncomputable def toSortedList : CommSemigroupExpr → List Nat
  | .add a b => a.toSortedList.merge b.toSortedList (· ≤ ·)
  | .atom i => [i]

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
theorem toSortedList_ne_nil (e : CommSemigroupExpr) : e.toSortedList ≠ [] := by
  induction e with unfold toSortedList
  | atom => simp
  | add a b ih_a ih_b =>
    exact List.merge_ne_nil_of_right ih_b



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

theorem count_toSortedList_eq_count (e : CommSemigroupExpr) (i : Nat) :
    e.toSortedList.count i = e.count i := by
  induction e with unfold count toSortedList
  | atom j => by_cases h : j = i <;> simp (disch := symm; assumption) [h]
  | add a b ih_a ih_b => simp [ih_a, ih_b]

theorem sorted_toSortedList (e : CommSemigroupExpr) :
    e.toSortedList.Pairwise (· ≤ ·) := by
  suffices e.toSortedList.Pairwise (decide <| · ≤ ·) by simpa
  induction e with
  | atom i => simp [toSortedList]
  | add a b ih_a ih_b =>
    unfold toSortedList
    apply List.sorted_merge (by simp; omega) (by simp; omega)
    · apply ih_a
    · apply ih_b

def eval [inst : CommSemigroup α] (eval_atom : Nat → α) : CommSemigroupExpr → α
  | .add a b => a.eval eval_atom + b.eval eval_atom
  | .atom i => eval_atom i

theorem lift_add [inst : CommSemigroup α] (eval_atom : Nat → α) (e₁ e₂ : CommSemigroupExpr) :
    (e₁.add e₂).eval eval_atom = e₁.eval eval_atom + e₂.eval eval_atom :=
  rfl

def Equiv (e₁ e₂ : CommSemigroupExpr) : Prop :=
  ∀ {α : Type u} [CommSemigroup α] (eval_atom : Nat → α),
    e₁.eval eval_atom = e₂.eval eval_atom

def evalList [inst : CommSemigroup α] (eval_atom : Nat → α) (l : List (Nat)) (hl : l ≠ []) : α :=
  match l with
  | a :: l =>
  if h : l = [] then
    eval_atom a
  else
    eval_atom a + evalList eval_atom l h

theorem evalList_merge [inst : CommSemigroup α] (eval_atom : Nat → α) (l₁ l₂ : List (Nat)) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    evalList eval_atom (l₁.merge l₂) (List.merge_ne_nil_of_left h₁) = evalList eval_atom l₁ h₁ + evalList eval_atom l₂ h₂ := by
  induction l₁ generalizing l₂ with
  | nil => contradiction
  | cons a₁ l₁' ih₁ =>
    induction l₂ with
    | nil => contradiction
    | cons a₂ l₂' ih₂ =>
      specialize ih₁ (a₂ :: l₂')
      by_cases h₁ : l₁' = [] <;> (try rcases h₁ with rfl)
        <;> by_cases h₂ : l₂' = [] <;> (try rcases h₂ with rfl)
        <;> unfold List.merge <;> split
        <;> simp only [h₁, h₂, evalList, List.merge_ne_nil_of_left,
          List.nil_merge, List.merge_right,
          ↓reduceDIte, reduceCtorEq,
          ne_eq, not_true_eq_false, not_false_eq_true, forall_const, forall_false, forall_true_left] at ih₁ ih₂ ⊢
      · rw [inst.add_comm]
      · rw [ih₂, inst.add_left_comm]
      · rw [ih₁, inst.add_assoc]
      · rw [inst.add_comm]
      · rw [ih₁, inst.add_assoc]
      · rw [ih₂, inst.add_left_comm]

theorem evalList_toSortedList [inst : CommSemigroup α] (eval_atom : Nat → α) (e : CommSemigroupExpr) :
    evalList eval_atom e.toSortedList (toSortedList_ne_nil e) = e.eval eval_atom := by
  induction e with unfold eval toSortedList
  | atom i => simp [evalList]
  | add a b ih_a ih_b => rw [evalList_merge eval_atom _ _ (toSortedList_ne_nil a) (toSortedList_ne_nil b), ih_a, ih_b]

theorem equiv_of_count_eq (e₁ e₂ : CommSemigroupExpr) (h : ∀ i : Nat, e₁.count i = e₂.count i) : e₁.Equiv e₂ := by
  intro α inst eval_atom
  simp [← evalList_toSortedList]
  congr 1
  apply List.Perm.eq_of_sorted (fun _ _ _ _ => Nat.le_antisymm)
  · apply sorted_toSortedList
  · apply sorted_toSortedList
  · apply List.perm_iff_count.mpr
    simpa [count_toSortedList_eq_count]

end EquivOfCount

/-

  def maxAux (n : Nat) : CommSemigroupExpr → Nat
    | .add a b =>
  def max : CommSemigroupExpr → Nat := maxAux 0

  def boundedBy (n : Nat) : CommSemigroupExpr → Prop
    | .add a b => a.boundedBy n ∧ b.boundedBy n
    | .atom i => i < n

  def reduceAux (vec : Vector Nat n) (e : CommSemigroupExpr) (h : e.boundedBy n) : Vector Nat n :=
    match e with
    | .add a b => b.reduceAux (a.reduceAux vec h.1) h.2
    | .atom i => vec.set i (vec[i] + 1)

  def reduce (e : CommSemigroupExpr) (n : Nat) (h : e.boundedBy n) : Vector Nat n :=
    e.reduceAux (.mkVector _ 0) h

  theorem getElem_reduce_eq_count (e : CommSemigroupExpr) (i : Fin n) : (reduce e)[i] = e.count i := by
    suffices h : ∀ (vec : Vector Nat n), (reduceAux vec e)[i] = vec[i] + e.count i by
      simpa using h (.mkVector _ 0)
    induction e with (intro vec; unfold reduceAux count)
    | atom j => by_cases h : j = i <;> simp (disch := omega) [h]
    | add a b a_ih b_ih => rw [b_ih, a_ih, Nat.add_assoc]

  theorem equiv_of_reduce_eq (e₁ e₂ : CommSemigroupExpr) (h : e₁.reduce = e₂.reduce) : e₁.Equiv e₂ := by
    apply equiv_of_count_eq
    intro i
    simp only [← getElem_reduce_eq_count]
    rw [h]
-/

section Decide

def equalListLength : List Nat → List Nat → Bool
  | _ :: l₁, _ :: l₂ => equalListLength l₁ l₂
  | [], [] => true
  | _, _ => false

def splitListByAux (mid : Nat) (left right : List Nat) : List Nat → List Nat × List Nat
  | x :: xs =>
    if x < mid then
      splitListByAux mid (x :: left) right xs
    else
      splitListByAux mid left (x :: right) xs
  | [] => (left, right)

def splitListBy (mid : Nat) : List Nat → List Nat × List Nat := splitListByAux mid [] []

def equalCountBetween (l₁ l₂ : List Nat) (lo hi fuel : Nat) : Bool :=
  if lo = ((lo+hi)/2) then
    equalListLength l₁ l₂
  else
    match fuel with
    | 0 => default
    | fuel+1 =>
      let l₁ := splitListBy ((lo+hi)/2) l₁
      let l₂ := splitListBy ((lo+hi)/2) l₂
      Bool.and (equalCountBetween l₁.1 l₂.1 lo ((lo+hi)/2) fuel) (equalCountBetween l₁.2 l₂.2 ((lo+hi)/2) hi fuel)

def isBound (n : Nat) : List Nat → Bool
  | x :: xs => Bool.and (x < n) (isBound n xs)
  | [] => true

def toListAux (list : List Nat) : CommSemigroupExpr → List Nat
  | .add a b => a.toListAux (b.toListAux list)
  | .atom i => i :: list

def toList : CommSemigroupExpr → List Nat := toListAux []

def equalCountAndBelow (l₁ l₂ : List Nat) (n : Nat) : Bool :=
  Bool.and (isBound n l₁) <|
  Bool.and (isBound n l₂) <|
    equalCountBetween l₁ l₂ 0 n n

def decideEquiv (e₁ e₂ : CommSemigroupExpr) (n : Nat) : Bool :=
  equalCountAndBelow e₁.toList e₂.toList n

end Decide

section ProveDecide

theorem count_toList_eq_count (e : CommSemigroupExpr) (i : Nat) : e.toList.count i = e.count i := by
  unfold toList
  suffices h : ∀ list : List Nat, (e.toListAux list).count i = e.count i + list.count i by apply h
  induction e with (unfold toListAux count; intro list)
  | atom j => rw [Nat.add_comm]; by_cases h : j = i <;> simp (disch := symm; assumption) [h]
  | add a b ih_a ih_b => rw [ih_a, ih_b]; omega

theorem isBound_spec {l : List Nat} (h : isBound n l) : ∀ i ∈ l, i < n := by
  intro i
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [isBound, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.mem_cons]
    rintro (rfl | hi)
    · exact h.1
    · exact ih h.2 hi

theorem count_eq_zero {l : List Nat} (h : ∀ i ∈ l, i < n) {i : Nat} (hi : n ≤ i) : l.count i = 0 :=
  List.count_eq_zero_of_not_mem (mt (h i) (Nat.not_lt.mpr hi))

-- theorem splitListBy_between (lo mid hi : Nat) (l : List Nat) (h : ∀ i ∈ l, lo ≤ i ∧ i < hi) :
--     ∀ i ∈ (splitListBy mid l).1, lo ≤ i ∧ i < mid := by
--   unfold splitListBy
--   suffices h : ∀ l₁ l₂, (∀ i ∈ l₁, lo ≤ i ∧ i < mid) → (∀ i ∈ l₂, lo ≤ i ∧ i < mid) →
--       ∀ i ∈ (splitListByAux mid l₁ l₂ l).1, lo ≤ i ∧ i < mid by apply h <;> simp
--   intro l₁ l₂ h₁ h₂ i hi

--   induction l with simp [splitListByAux] at hi
--   | nil => exact h₁ i hi
--   | cons a l ih =>
--     by_cases ha : a < mid <;> simp [ha] at hi
--     · sorry
--     · sorry

-- theorem splitListBy_bound_1 (lo mid hi : Nat) (l : List Nat) (i : Nat) (hi : i < lo ∨ mid ≤ i) :


theorem count_splitListBy_fst (mid : Nat) (l : List Nat) (i : Nat) :
    (splitListBy mid l).fst.count i = if i < mid then l.count i else 0 := by
  unfold splitListBy
  suffices h : ∀ l₁ l₂, (splitListByAux mid l₁ l₂ l).fst.count i =
      (if i < mid then l.count i else 0) + l₁.count i by apply h
  induction l with simp [splitListByAux]
  | cons j l ih =>
    intro l₁ l₂
    split
      <;> simp [ih, List.count_cons]
      <;> by_cases hi : i < mid
      <;> simp [hi]
      <;> omega

theorem count_splitListBy_snd (mid : Nat) (l : List Nat) (i : Nat) :
    (splitListBy mid l).snd.count i = if i < mid then 0 else l.count i := by
  unfold splitListBy
  suffices h : ∀ l₁ l₂, (splitListByAux mid l₁ l₂ l).snd.count i =
      (if i < mid then 0 else l.count i) + l₂.count i by apply h
  induction l with simp [splitListByAux]
  | cons j l ih =>
    intro l₁ l₂
    split
      <;> simp [ih, List.count_cons]
      <;> by_cases hi : i < mid
      <;> simp [hi]
      <;> omega

theorem mem_of_mem_splitListBy_fst {mid : Nat} {l : List Nat} : ∀ i ∈ (splitListBy mid l).fst, i ∈ l := by
  intro i
  simp only [← List.one_le_count_iff, count_splitListBy_fst]
  split <;> omega

theorem mem_of_mem_splitListBy_snd {mid : Nat} {l : List Nat} : ∀ i ∈ (splitListBy mid l).snd, i ∈ l := by
  intro i
  simp only [← List.one_le_count_iff, count_splitListBy_snd]
  split <;> omega

theorem lt_of_mem_splitListBy_fst {mid : Nat} {l : List Nat} : ∀ i ∈ (splitListBy mid l).fst, i < mid := by
  intro i
  simp only [← List.one_le_count_iff, count_splitListBy_fst]
  split <;> omega

theorem lt_of_mem_splitListBy_snd {mid : Nat} {l : List Nat} : ∀ i ∈ (splitListBy mid l).snd, mid ≤ i := by
  intro i
  simp only [← List.one_le_count_iff, count_splitListBy_snd]
  split <;> omega

theorem eq_of_equalListLength {l₁ l₂ : List Nat} (i : Nat) (h : equalListLength l₁ l₂)
    (h₁ : ∀ j ∈ l₁, j = i) (h₂ : ∀ j ∈ l₂, j = i) :
    l₁ = l₂ :=
  match l₁, l₂ with
  | [], [] => rfl
  | _ :: _, [] => by contradiction
  | [], _ :: _ => by contradiction
  | a₁ :: l₁, a₂ :: l₂ => by
    simp only [List.mem_cons, forall_eq_or_imp] at h₁ h₂
    simp only [h₁.1, h₂.1, List.cons.injEq, true_and]
    exact eq_of_equalListLength i h h₁.2 h₂.2

theorem equalCountBetween_spec {l₁ l₂ : List Nat} (lo hi fuel : Nat) (h_fuel : hi ≤ lo + fuel)
    {i : Nat} (h_lo : lo ≤ i) (h_hi : i < hi) (h : equalCountBetween l₁ l₂ lo hi fuel)
    (h₁_lo : ∀ i ∈ l₁, lo ≤ i) (h₂_lo : ∀ i ∈ l₂, lo ≤ i) (h₁_hi : ∀ i ∈ l₁, i < hi) (h₂_hi : ∀ i ∈ l₂, i < hi) :
    l₁.count i = l₂.count i := by
  unfold equalCountBetween at h
  split at h
  · congr
    apply eq_of_equalListLength i h
    · intro j hj; specialize h₁_lo j hj; specialize h₁_hi j hj
      omega
    · intro j hj; specialize h₂_lo j hj; specialize h₂_hi j hj
      omega
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp at h
    obtain ⟨h_fst, h_snd⟩ := h
    by_cases h : i < (lo+hi)/2
    · have := equalCountBetween_spec lo ((lo+hi)/2) fuel (by omega) h_lo h h_fst ?_ ?_ ?_ ?_
      simp [count_splitListBy_fst, h] at this; exact this
      · intro i hi; exact h₁_lo i (mem_of_mem_splitListBy_fst i hi)
      · intro i hi; exact h₂_lo i (mem_of_mem_splitListBy_fst i hi)
      · exact lt_of_mem_splitListBy_fst
      · exact lt_of_mem_splitListBy_fst
    · have := equalCountBetween_spec ((lo+hi)/2) hi fuel (by omega) (by omega) h_hi h_snd ?_ ?_ ?_ ?_
      simp [count_splitListBy_snd, h] at this; exact this
      · exact lt_of_mem_splitListBy_snd
      · exact lt_of_mem_splitListBy_snd
      · intro i hi; exact h₁_hi i (mem_of_mem_splitListBy_snd i hi)
      · intro i hi; exact h₂_hi i (mem_of_mem_splitListBy_snd i hi)

theorem Equiv_of_decide (e₁ e₂ : CommSemigroupExpr) (n : Nat) (h : decideEquiv e₁ e₂ n) :
    Equiv e₁ e₂ := by
  apply equiv_of_count_eq
  intro i
  simp only [← count_toList_eq_count]
  unfold decideEquiv at h
  generalize e₁.toList = l₁, e₂.toList = l₂ at h
  simp [equalCountAndBelow] at h
  obtain ⟨h₁, h₂, h⟩ := h
  replace h₁ := isBound_spec h₁
  replace h₂ := isBound_spec h₂
  by_cases hi : n ≤ i
  · rw [count_eq_zero h₁ hi, count_eq_zero h₂ hi]
  · simp at hi
    apply equalCountBetween_spec 0 n n
      <;> first | assumption | simp

end ProveDecide


open Lean Meta Qq Mathlib.Tactic AtomM

partial def ofExpr {u : Level} {α : Q(Type $u)} (inst : Q(CommSemigroup $α)) (e : Q($α)) : AtomM Q(CommSemigroupExpr) := do
  let els := do
    let ⟨n, _⟩ ← addAtomQ e
    let n : Q(Nat) := mkNatLit n
    return q(CommSemigroupExpr.atom $n)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) => return q(CommSemigroupExpr.add $(← ofExpr inst a) $(← ofExpr inst b))
    | _ => els
  | _ => els

/-- Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "my amazing tactic failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let inst ← synthInstanceQ q(CommSemigroup $α)
  let eq ← ringCore inst e₁ e₂
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemigroup`,
  and returns a proof that they are equal (or fails). -/
  ringCore {v : Level} {α : Q(Type v)} (inst : Q(CommSemigroup $α)) (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "ring" (← getOptions) do
      let e₁' ← ofExpr inst e₁
      let e₂' ← ofExpr inst e₂

      let pf ← mkDecideProof expectedType
      -- Get instance from `pf`
      let s := pf.appFn!.appArg!
      let r ← withAtLeastTransparency .default <| whnf s
      if r.isAppOf ``isTrue then
        -- Success!
        -- While we have a proof from reduction, we do not embed it in the proof term,
        -- and instead we let the kernel recompute it during type checking from the following more
        -- efficient term. The kernel handles the unification `e =?= true` specially.
        return pf
      else
        diagnose expectedType s r

      unless va.eq vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
      return q(of_eq $pa $pb)
example : True := by decide


open Elab.Tactic in
/--
Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[inherit_doc ring1] macro "ring1!" : tactic => `(tactic| ring1 !)


#check Elab.Tactic.setGoals

open Elab Tactic in
elab "my_amazing_semigroup_tactic" : tactic => do
  let mvarId ← getMainGoal
  let type ← inferType (.mvar mvarId)

  let a ←
  _

-- If we want to use a normal form tactic, then we need a way to compute the new normal form.
-- def toExpr {u : Level} {α : Q(Type $u)} (i : Q(CommSemigroup $α)) (atoms : Array Q($α)) ()

end CommSemigroupExpr
example := by decide
