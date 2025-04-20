import Qq


universe u

inductive BinTree (α : Type u) where
| leaf : α → BinTree α
| node : Nat → BinTree α → BinTree α → BinTree α

namespace BinTree

variable {α : Type u}

def get (tree : BinTree α) (n : Nat) : α :=
  match tree with
  | leaf a => a
  | node m l r => if n < m then l.get n else r.get n

open Lean Qq

def mkExpr {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : Q(BinTree $α) :=
  if _ : atoms.size = 0 then
    panic! "empty array"
  else
    go 0 atoms.size
where
  go (lo hi : Nat) (h_lo : lo < hi := by omega) (h_hi : hi ≤ atoms.size := by omega) : Q(BinTree $α) :=
    let mid := (lo + hi)/2
    if h : lo = mid then
      q(leaf $(atoms[lo]))
    else
      let l := go lo mid
      let r := go mid hi
      let n : Q(Nat) := mkNatLit mid
      q(node $n $l $r)
  termination_by hi - lo

def mkFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : Q(Nat → $α) :=
  let tree := BinTree.mkExpr atoms
  q(($tree).get)


/-
The avobe is sufficient to use `BinTree` purely as an lookup index expression
However, we may also like to use it as an index that is created and modifies by the kernel.

Thus, we introduce more operations, such as a boolean equality, and modification.
-/

def modify (f : α → α) (n : Nat) : BinTree α → BinTree α
| .leaf a     => .leaf (f a)
| .node m l r => if n < m then .node m (l.modify f n) r else .node m l (r.modify f n)

def beq [BEq α] : BinTree α → BinTree α → Bool
| .leaf a, .leaf b => a == b
| .node _ l r, .node _ l' r' => Bool.and (beq l l') (beq r r')
| _, _ => false


inductive Equiv : BinTree α → BinTree α → Prop where
| leaf (a b : α)            : Equiv (.leaf a) (.leaf b)
| node (m : Nat) (l l' r r' : BinTree α) : Equiv l l' → Equiv r r' → Equiv (.node m l r) (.node m l' r')


theorem trans (t₁ t₂ t₃ : BinTree α) (h : t₁.Equiv t₂) (h' : t₂.Equiv t₃) : t₁.Equiv t₃ := by
  induction t₁ generalizing t₂ t₃ with
  | leaf a => cases h with
    | leaf _ b => cases h' with
      | leaf _ c => exact Equiv.leaf a c
  | node m l r ih_l ih_r => cases h with
    | node _ _ l' _ r' h'' h''' => cases h' with
      | node _ _ l'' _ r'' h'''' h''''' =>
        exact Equiv.node m l l'' r r'' (ih_l l' l'' h'' h'''') (ih_r r' r'' h''' h''''')

theorem symm (t₁ t₂ : BinTree α) (h : t₁.Equiv t₂) : t₂.Equiv t₁ := by
  induction t₁ generalizing t₂ with
  | leaf a => cases t₂ with
    | leaf b => exact Equiv.leaf b a
    | node => contradiction
  | node m l r ih_l ih_r =>
    cases h with
    | node _ _ l' _ r' h h' => exact Equiv.node m l' l r' r (ih_l l' h) (ih_r r' h')

theorem refl (t : BinTree α) : t.Equiv t := by
  induction t with
  | leaf a => exact Equiv.leaf a a
  | node m l r ih_l ih_r => exact Equiv.node m l l r r ih_l ih_r

theorem equiv_modify (f : α → α) (n : Nat) (t : BinTree α) : t.Equiv (t.modify f n) := by
  induction t with
  | leaf a => apply Equiv.leaf
  | node m l r ih_l ih_r =>
    by_cases h : n < m <;> simp [modify, h] <;> apply Equiv.node <;> first | assumption | apply refl


inductive WF : Nat → Nat → BinTree α → Prop where
| leaf (n : Nat) (a : α) : WF n (n+1) (.leaf a)
| node (x y z : Nat) (l r : BinTree α) : x < y → y < z → WF x y l → WF y z r → WF x z (.node y l r)

abbrev btw (x n y : Nat) := x ≤ n ∧ n < y

theorem WF_modify (f : α → α) (n x y : Nat) (t : BinTree α) (h : WF x y t) : WF x y (t.modify f n) := by
  induction t generalizing x y with
  | leaf a => cases h with
    | leaf n b => exact WF.leaf x (f a)
  | node m l r ih_l ih_r => cases h with
    | node x y z _ _ xy yz hl hr =>
      unfold modify
      split <;> apply WF.node <;> try assumption
      exact ih_l x m hl
      exact ih_r m y hr


theorem get_modify (f : α → α) (n n' x y : Nat) (t : BinTree α) (ht : WF x y t) (hn : btw x n y) (hn' : btw x n' y) :
    (t.modify f n').get n = if n = n' then f (t.get n) else t.get n := by
  by_cases h : n = n' <;> simp [h]
  · induction t generalizing x y with
    | leaf a => cases ht with
      | leaf _ _ =>
        obtain rfl : x = n := by omega
        obtain rfl : x = n' := by omega
        unfold modify get
        rfl
    | node m l r ih_l ih_r => cases ht with
      | node x y z _ _ xy yz hl hr =>
        unfold modify
        by_cases h : n' < m <;> by_cases h' : n < m <;> (try omega) <;> simp only [h, ↓reduceIte, get]
        · apply ih_l x m <;> simp_all [btw]
        · apply ih_r m y <;> simp_all [btw]
  · induction t generalizing x y with
    | leaf a => cases ht with | leaf _ _ => omega
    | node m l r ih_l ih_r => cases ht with
      | node x y z _ _ xy yz hl hr =>
        unfold modify
        by_cases h : n' < m <;> by_cases h' : n < m <;> simp only [h, ↓reduceIte, get, h']
        · apply ih_l x m <;> simp_all [btw]
        · apply ih_r m y <;> simp_all [btw]

def initial (lo hi fuel : Nat) (a : α) : BinTree α :=
  if lo = ((lo + hi)/2) then
    .leaf a
  else
    match fuel with
    | 0 => .leaf a
    | fuel+1 => .node ((lo + hi)/2) (initial lo ((lo + hi)/2) fuel a) (initial ((lo + hi)/2) hi fuel a)

theorem WF_initial (lo hi fuel : Nat) (a : α) (h_bound : lo < hi) (h_fuel : hi ≤ lo + fuel) : WF lo hi (initial lo hi fuel a) := by
  unfold initial
  split
  · obtain rfl : hi = lo+1 := by omega
    apply WF.leaf
  match fuel with
  | 0 => omega
  | fuel+1 =>
    dsimp only
    apply WF.node _ _ _ _ _ (by omega) (by omega)
      <;> apply WF_initial <;> omega

theorem get_initial (n lo hi fuel : Nat) (a : α) : (initial lo hi fuel a).get n = a := by
  induction fuel generalizing lo hi with
  | zero => simp [initial, get]
  | succ fuel ih =>
    simp [initial]
    split <;> simp [get]
    split <;> apply ih
