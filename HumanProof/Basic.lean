import Lean

namespace HumanProof

open Lean Meta

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
  deriving Repr

abbrev Address := List Coord

inductive PathItem where
  | forallB (name : Name) (type : Expr)
  | metaVar (name : Name) (type : Expr)
  | andL (name : Name) (type : Expr) (body : Box)
  | andR (name : Name) (type : Expr) (value : Box)
  | orL (inr : Box)
  | orR (inl : Box)

structure Zipper where
  path           : List PathItem
  cursor         : Box
  vars           : Array Expr
  lctx           : LocalContext
  localInstances : LocalInstances
  mctx           : MetavarContext

def Zipper.up (zipper : Zipper) : Option Zipper := do
  let item :: path := zipper.path | failure
  let { cursor, vars, .. } := zipper
  let zipper := { zipper with path }
  match item with
  | .forallB name type =>
    let fvar := vars.back!
    return { zipper with
      cursor := .forallB name type cursor
      lctx   := zipper.lctx.erase fvar.fvarId!
      vars   := vars.pop }
  | .metaVar name type => return { zipper with cursor := .metaVar name type cursor, vars := vars.pop }
  | .andL name type body => return { zipper with cursor := .and name type cursor body }
  | .andR name type value => return { zipper with cursor := .and name type value cursor }
  | .orL inr => return { zipper with cursor := .or cursor inr }
  | .orR inl => return { zipper with cursor := .or inl cursor }


def Zipper.down (zipper : Zipper) (coord : Coord) : MetaM Zipper := do
  let { path, cursor, vars, lctx, localInstances, mctx ..} := zipper
  let withFVar (name : Name) (type : Expr) (pathItem : PathItem) (body : Box) : MetaM Zipper := do
    withLCtx lctx localInstances do
      withLocalDeclD name type fun fvar => do
        return { zipper with
          path := pathItem :: path
          cursor := body
          vars := vars.push fvar
          lctx := ← getLCtx
          localInstances := ← getLocalInstances }
  match coord, cursor with
  | .forallB, .forallB name type body => withFVar name type (.forallB name type) body
  | .metaVar, .metaVar name type body =>
    setMCtx mctx
    let mvar ← mkFreshExprMVarAt lctx localInstances type (kind := .syntheticOpaque) (userName := name)
    return { zipper with
      path := .metaVar name type :: path
      cursor := body
      vars := vars.push mvar
      mctx := ← getMCtx}
  | .andL   , .and name type value body => return { zipper with path := .andL name type body :: path, cursor := value }
  | .andR   , .and name type value body => withFVar name type (.andR name type value) body
  | .orL    , .or inl inr => return { zipper with path := .orL inr :: path, cursor := inl }
  | .orR    , .or inl inr => return { zipper with path := .orR inl :: path, cursor := inr }
  | _       , _ => throwError "Zipper down coordinate is wrong: {repr coord}"


end Box

end HumanProof
