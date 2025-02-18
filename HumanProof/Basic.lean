import Lean

namespace HumanProof

open Lean

inductive Box : Type where
| forallB (name : Name) (type : Expr) (body : Box)
| metaVar (name : Name) (type : Expr) (body : Box)
| result (r : Expr)
| and (name : Name) (type : Expr) (value body : Box)
| or (inl : Box) (inr : Box)
-- | letB (name : Name) (type value : Expr) (body : Box)

namespace Box

def getResults : Box → Array Expr
  | .forallB name type body =>
    (getResults body).map (.forallE name type · .default)
  | metaVar _ _ body =>
    (getResults body).filterMap fun e =>
      if e.hasLooseBVar 0 then
        none
      else
        some (e.lowerLooseBVars 1 1)
  | .result r => #[r]
  | .and name type inl inr =>
    (getResults inl).flatMap fun e =>
      (getResults inr).map (mkLet name type e ·)
  | .or inl inr =>
    getResults inl ++ getResults inr


inductive Coord where
| forallB | metaVar | andL | andR | orL | orR

abbrev Address := List Coord

inductive PathItem where
  | forallB (name : Name) (type : Expr)
  | metaVarB (name : Name) (type : Expr)
  | andL (name : Name) (type : Expr) (body : Box)
  | andR (name : Name) (type : Expr) (value : Box)
  | orL (inr : Box)
  | orR (inl : Box)

structure Zipper where
  path   : List PathItem
  cursor : Box
  lctx   : LocalContext
  mctx   : MetavarContext
  vars   : Array Expr

#check Meta.mkLambdaFVars
#check mkLambda

def Zipper.up (zipper : Zipper) : Option Zipper := do
  let item :: path := zipper.path | failure
  let zipper := { zipper with path }
  let cursor := zipper.cursor
  let vars   := zipper.vars
  match item with
  | .forallB name type =>
    let fvar := vars.back!
    return { zipper with
      cursor := .forallB name type cursor
      lctx   := zipper.lctx.erase fvar.fvarId!
      vars   := vars.pop
    }
  | .metaVarB name type => sorry
  | .andL name type body => return { zipper with cursor := .and name type cursor body }
  | .andR name type value => return { zipper with cursor := .and name type value cursor }
  | .orL inr => return { zipper with cursor := .or cursor inr }
  | .orR inl => return { zipper with cursor := .or inl cursor }







end Box

end HumanProof
