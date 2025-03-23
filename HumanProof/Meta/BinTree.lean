import Qq


universe u

inductive BinTree (α : Type u) where
| leaf : α → BinTree α
| node : Nat → BinTree α → BinTree α → BinTree α

variable {α : Type u}

def BinTree.get (tree : BinTree α) (n : Nat) : α :=
  match tree with
  | leaf a => a
  | node m l r => if n < m then l.get n else r.get n

open Lean Qq

def BinTree.mkExpr {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : Q(BinTree $α) :=
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

def BinTree.mkFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : Q(Nat → $α) :=
  let tree := BinTree.mkExpr atoms
  q(($tree).get)
