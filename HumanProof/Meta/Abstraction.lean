import Lean
import Qq
import Mathlib.Util.AtomM

namespace Abstraction

open Lean Qq Mathlib.Tactic

class Denote {u : Level} (α : outParam (Q(Type $u))) (ε : Type) where
  denote : ε → Q($α)

export Denote (denote)

class Reify {u : Level} (α : outParam Q(Type $u)) (ε : Type) (m : Type → Type) where
  reify : Q($α) → m ε

export Reify (reify)

structure AtomExpr {u : Level} (α : Q(Type $u)) where
  id   : Nat
  expr : Q($α)
deriving Inhabited

instance {u : Level} (α : Q(Type $u)) : BEq (AtomExpr α) where
  beq a b := a.id == b.id

instance {u : Level} (α : Q(Type $u)) : Hashable (AtomExpr α) where
  hash a := hash a.id

instance {u : Level} (α : Q(Type $u)) : Reify α (AtomExpr α) AtomM where
  reify e := (fun (id, expr) => { id, expr }) <$> AtomM.addAtom e

instance {u : Level} (α : Q(Type $u)) : Denote α (AtomExpr α) where
  denote a := a.expr


class DenoteEq {u : Level} (α : outParam Q(Type $u)) (ε : Type) extends Denote α ε where
  denoteEq! : ∀ e₁ e₂ : ε, Q($(denote e₁) = $(denote e₂))
  -- denoteEq? : ∀ e₁ e₂ : ε, Option Q($(denote e₁) = $(denote e₂)) := fun e₁ e₂ => some (denoteEq! e₁ e₂)

export DenoteEq (denoteEq!)

-- instance (priority := low) {u : Level} (α : Q(Type $u)) (ε : Type) [Denote α ε] [BEq ε] : DenoteEq α ε where
--   denoteEq! e₁ _ := (q(@rfl $α $(denote e₁)):)
--   -- denoteEq? e₁ e₂ := if e₁ == e₂ then
--   --   some (denoteEq! (α := α) e₁ e₂)
--   -- else
--   --   none

def _root_.Qq.mkExpectedTypeHint {α : Expr} (e : Expr) : MetaM (Quoted α) :=
  Meta.mkExpectedTypeHint e α



-- open Lean Qq

-- class EqClass (α : Type) (ε : outParam (α → α → Type)) where
--   refl  : ∀ a : α, ε a a
--   symm  : ∀ {a b : α}, ε a b → ε b a
--   trans : ∀ {a b c : α}, ε a b → ε b c → ε a c

-- export EqClass (refl symm trans)

-- /-- In a `DecidableEqClass α ε`, one can check whether two expressions are equal. -/
-- class DecidableEqClass (α : Type) (ε : outParam (α → α → Type)) extends EqClass α ε where
--   decideEq : ∀ a b : α, Option (ε a b)

-- export DecidableEqClass (decideEq)

-- class NormalingEqClass (α : Type) (ε : outParam (α → α → Type)) extends EqClass α ε where
--   normalize         : α → α
--   normalize_eq      : ∀ a : α, ε a (normalize a)
--   normalize_eq_symm : ∀ a : α, ε (normalize a) a := fun a => symm (normalize_eq a)

-- export NormalingEqClass (normalize normalize_eq normalize_eq_symm)

-- instance {α} {ε} [BEq α] [LawfulBEq α] [NormalingEqClass α ε] : DecidableEqClass α ε where
--   decideEq a b :=
--     if h : normalize a == normalize b then
--       have h' := eq_of_beq h
--       some (trans (normalize_eq a) (h' ▸ normalize_eq_symm b))
--     else
--       none

-- /- Unfortunately, this instance cannot be nicely extended to an instance of `NormalizingEqClass` and `DecidableEqClass`,
-- because `isDefEq` and `reduce`/`simp` require the `MetaM` monad. -/
-- instance {u : Level} {α : Q(Sort u)} : EqClass Q($α) (fun a b => Q($a = $b)) where
--   refl _ := q(rfl)
--   symm h := q(($h).symm)
--   trans h₁ h₂ := q($(h₁).trans $h₂)

-- instance {u : Level} {α : Q(Sort u)} : DecidableEqClass Q($α) (fun a b => Q($a = $b)) where
--   decideEq a b :=
--     if a.equal b then
--       some (refl a:)
--     else
--       none



-- /--
-- An `ExprEqClass α ε` is a type that can represent expressions (in `α`)
-- and reason about their equality (in `ε`).
-- -/
-- class ExprEqClass (α : Type) (ε : outParam (α → α → Type)) extends EqClass α ε where
--   u : Level
--   αExpr : Q(Type $u)
--   denote : α → Q($αExpr)
--   toProofExpr : ∀ a b : α, (eq : ε a b) → Q($(toExpr a) = $(toExpr b))

-- -- /--
-- -- An `Abstraction α β` represents that expressions in `α` can be used to reason about
-- -- expressions in `β`.
-- -- -/
-- -- class Abstraction (α : Type → Type)  where
-- --   abstract : ∀ β, β → α β
-- --   original : ∀ β, α β → β
-- -- #check Pure
