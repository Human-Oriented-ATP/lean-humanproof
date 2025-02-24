import Lean

namespace HumanProof

open Lean Meta

inductive Box : Type where
| forallB (decl : LocalDecl) (body : Box) (hidden : Bool := false)
| metaVar (mvarId : MVarId) (decl : MetavarDecl) (body : Box)
| result (r : Expr)
| and (decl : LocalDecl) (value body : Box)
| or (inl : Box) (inr : Box)
| haveB (decl : LocalDecl) (value : Expr) (body : Box)
deriving Inhabited

namespace Box

-- def getResults : Box → Array Expr
--   | .forallB name type body =>
--     (getResults body).map (.forallE name type · .default)
--   | metaVar _ _ body =>
--     (getResults body).filterMap fun e =>
--       if e.hasLooseBVar 0 then
--         none
--       else
--         some (e.lowerLooseBVars 1 1)
--   | .result r => #[r]
--   | .and name type inl inr =>
--     (getResults inl).flatMap fun e =>
--       (getResults inr).map (mkLet name type e ·)
--   | .or inl inr =>
--     getResults inl ++ getResults inr


inductive Coord where
  | forallB | metaVar | andL | andR | orL | orR | haveB
  deriving Repr

inductive PathItem where
  | forallB (decl : LocalDecl) (hidden : Bool)
  | metaVar (mvarId : MVarId) (decl : MetavarDecl)
  | andL (decl : LocalDecl) (body : Box)
  | andR (decl : LocalDecl) (value : Box)
  | orL (inr : Box)
  | orR (inl : Box)
  | haveB (decl : LocalDecl) (value : Expr)

structure Zipper where
  path           : List PathItem
  cursor         : Box
  lctx           : LocalContext
  localInstances : LocalInstances
  mctx           : MetavarContext

def Zipper.up (zipper : Zipper) : Option Zipper := do
  let item :: path := zipper.path | failure
  let { cursor, .. } := zipper
  let zipper := { zipper with path }
  match item with
  | .forallB decl hidden =>
    return { zipper with
      cursor := .forallB decl cursor hidden
      lctx   := zipper.lctx.erase decl.fvarId  }
  | .metaVar mvarId decl => return { zipper with cursor := .metaVar mvarId decl cursor }
  | .andL decl body => return { zipper with cursor := .and decl cursor body }
  | .andR decl value => return { zipper with cursor := .and decl value cursor }
  | .orL inr => return { zipper with cursor := .or cursor inr }
  | .orR inl => return { zipper with cursor := .or inl cursor }
  | .haveB decl value => return { zipper with cursor := .haveB decl value cursor }

partial def Zipper.zip (zipper : Zipper) : Box :=
  if let some zipper := zipper.up then
    zipper.zip
  else
    zipper.cursor

def Zipper.down (zipper : Zipper) (coord : Coord) : MetaM Zipper := do
  let { path, cursor, lctx, localInstances, mctx ..} := zipper
  let withFVar (decl : LocalDecl) (pathItem : PathItem) (body : Box) : MetaM Zipper := do
    withLCtx lctx localInstances do
      withExistingLocalDecls [decl] do
        return { zipper with
          path := pathItem :: path
          cursor := body
          lctx := ← getLCtx
          localInstances := ← getLocalInstances }
  match coord, cursor with
  | .forallB, .forallB decl body hidden => withFVar decl (.forallB decl hidden) body
  | .metaVar, .metaVar mvarId decl body =>
    let {userName, lctx, type, localInstances, kind, .. } := decl
    return { zipper with
      path := .metaVar mvarId decl :: path
      cursor := body
      mctx := mctx.addExprMVarDeclExp mvarId userName lctx localInstances type kind }
  | .andL   , .and decl value body => return { zipper with path := .andL decl body :: path, cursor := value }
  | .andR   , .and decl value body => withFVar decl (.andR decl value) body
  | .orL    , .or inl inr => return { zipper with path := .orL inr :: path, cursor := inl }
  | .orR    , .or inl inr => return { zipper with path := .orR inl :: path, cursor := inr }
  | .haveB  , .haveB decl value body => withFVar decl (.haveB decl value) body
  | _       , _ => throwError "Zipper down coordinate is wrong: {repr coord}"


def Zipper.unzip (box : Box) (address : List Coord) : MetaM Zipper := do
  go { path := [], cursor := box, lctx := {}, localInstances := {}, mctx := {} } address
where
  go (zipper : Zipper) (address : List Coord) : MetaM Zipper := do
    let coord :: address := address | return zipper
    let zipper ← zipper.down coord
    go zipper address



example (h : 1 + 1 = 2) (g : False) (hh : h = h) : True := by
  change 2 = 2 at  h
  simp at h

/-
(1) define addMVar and assign mvar.
  - define/find metavariable dependency relation.
  -
(2) DONE -- collectDelayMVarApps : Expr → MetaM (HashSet MVarId × HashMap MvarId (Array Expr))

(3) DONE -- Box.instantiate1 : Expr → Expr → Expr. Actually just instantiate mvars. Except for delay assigned mvars, because with will deal with those using And binders.


-/

/-- Replace all occurrences of a variable with `new`. -/
def instantiateMVarWith (var e new : Expr) : CoreM Expr :=
  Core.transform e (post := (if · == var then return .done new else return .continue))


/--
Collect the metavariables that appear in an expression.
This is used after running a tactic, on the metavariable goal.
-/
def collectDelayMVarApps (mvarId : MVarId) : MetaM (Std.HashSet MVarId × Std.HashMap MVarId (Array Expr)) := do
  let e ← instantiateMVars (.mvar mvarId)
  let (_, res) ← StateT.run (s := ({}, {})) <| Core.transform e (pre := fun e => do
    if let .mvar mvarId := e then
      let s : Std.HashSet MVarId × Std.HashMap MVarId (Array Expr) ← get
      if ← mvarId.isDelayedAssigned then
        let args := e.getAppArgs
        if !s.2.contains mvarId then
          set (s.1, s.2.insert mvarId args)
      else
        set (s.1.insert mvarId, s.2)
    return .continue)
  return res
#check collectMVars
#check Tactic.getU
#check MetavarContext.collectForwardDeps

#check Core.transform

#check Lean.Expr.instantiate1
end Box

end HumanProof
/-
?a : Nat
h : ?a = 1
?b : Nat

⊢

-/

/-
let ?a := ?b + 1
-/
open Lean Meta Elab

elab "test" e:tactic : tactic => do
  -- let e ← Term.elabTerm e none
  -- logInfo m! "{e}"
  let mvarId ← Tactic.getMainGoal
  Tactic.evalTactic e
  let mvarIdNew ← Tactic.getMainGoal
  liftMetaM do
  logInfo m! "{repr mvarId}; {← instantiateMVars <| Expr.mvar mvarId}"
  logInfo m! "{repr mvarIdNew}; {← instantiateMVars <| Expr.mvar mvarIdNew}"
  let (_, mvars) ← collectMVars (.mvar mvarId) |>.run {}
  for mvar in mvars.result do
    logInfo m! "{repr mvar}; {← instantiateMVars <| Expr.mvar mvar}; {mvar}"
    if let some x ← getDelayedMVarAssignment? mvar then
      logInfo m! "delayed assigment of {Expr.mvar mvar}: {Expr.mvar x.mvarIdPending}"
set_option pp.instantiateMVars false
example {P : α → Prop} (x : α) (y : α) {β : Type} (h': True) (h : α = β) (z : Nat) : P x := by
  -- -- clear y
  -- rw [h] at y
  test rw [h] at y
#check Exists.casesOn
example {P : α → Prop} (h : ∃ x, P x) (a : Nat) : False := by
  test cases h

example {α β : Nat} (P : Nat → Prop) (h : P α) (h' : α = β) : False := by
  test rw [h'] at h

example {α β : Nat} (h' : 15 = β) (h : True) : False := by
  test induction β generalizing h

example {p q : Prop} (h : p) (g : False) : q := by
  contrapose h
