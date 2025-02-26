import Lean

namespace HumanProof

open Lean Meta

section Notation

syntax:10 term:10 "%." noWs ident term:max : term

macro_rules
| `($struct %.$field:ident $f) => `({ $struct with $field:ident := $f $struct.$field })

syntax ident ":=." noWs ident term : doElem

macro_rules
| `(doElem| $var:ident :=.$field:ident $f) => `(doElem| $var:ident := $var %.$field $f)

/-- test -/
syntax ident ":>" term : doElem

macro_rules
| `(doElem| $var:ident :> $f) => `(doElem| $var:ident := $f $var)

syntax ident ":->" term : doElem

macro_rules
| `(doElem| $var:ident :-> $f:term) => `(doElem| $var:ident ← $f:term $var)

end Notation


/-

TODO: simplifications in Box

- remove metaVar binders when they aren't used
- Propagate solved boxes in `.forallB`, `.haveB`, `or` (either side), `.and` (value)
- Reduce `.and` (body):
  - `let x := box; ▸ x` ↦ `box`
  - `let x := (let y := box; ▸ g y); ▸ f x` ↦ `let y := box; ▸ f (g y)`

-/

inductive Box where
| forallB (decl : LocalDecl) (body : Box) (hidden : Bool := false)
| metaVar (mvarId : MVarId) (name : Name) (type : Expr) (body : Box)
| result (r : Expr)
| and (decl : LocalDecl) (value body : Box)
| or (inl : Box) (inr : Box)
| haveB (decl : LocalDecl) (value : Expr) (body : Box)
deriving Inhabited

namespace Box

def _root_.Lean.LocalDecl.mkLambda (decl : LocalDecl) (e : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  .lam decl.userName decl.type e decl.binderInfo

def _root_.Lean.LocalDecl.mkLet (decl : LocalDecl) (e value : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  Lean.mkLet decl.userName decl.type value e

def getResults (box : Box) : MetaM (Array Expr) := do
  return (← go box).filter (!·.hasMVar)
where
  go : Box → MetaM (Array Expr)
  | .forallB decl body _hidden =>
    withExistingLocalDecls [decl] do
    if !decl.type.hasMVar then
      return (← go body).map decl.mkLambda
    else
      return #[]
  | .metaVar _ _ _ body => go body
  | .result r => if r.hasMVar then return #[] else return #[r]
  | .and decl value body => do
    (← go value).flatMapM fun value => withExistingLocalDecls [decl] do
      return (← go body).map (decl.mkLet · value)
  | .or inl inr => return (← go inl) ++ (← go inr)
  | .haveB decl value body => withExistingLocalDecls [decl] do
    (← go body).mapM fun e => do
      let f := decl.mkLambda e
      let ety ← inferType e
      let α ← inferType value
      let β := decl.mkLambda ety
      let u1 ← getLevel α
      let u2 ← getLevel ety
      return mkAppN (.const ``letFun [u1, u2]) #[α, β, value, f]

-- inductive Coord where
--   | forallB | metaVar | andL | andR | orL | orR | haveB
--   deriving Repr, BEq

inductive PathItem where
  | forallB (decl : LocalDecl) (hidden : Bool)
  | metaVar (mvarId : MVarId) (name : Name) (type : Expr)
  | andL (decl : LocalDecl) (body : Box)
  | andR (decl : LocalDecl) (value : Box)
  | orL (inr : Box)
  | orR (inl : Box)
  | haveB (decl : LocalDecl) (value : Expr)

def PathItem.format : PathItem → MessageData
  | forallB (decl : LocalDecl) (_hidden : Bool) => m!"forallB {decl.type}"
  | metaVar (_mvarId : MVarId) (_name : Name) (type : Expr) => m!"metaVar {type}"
  | andL (_decl : LocalDecl) (_body : Box) => m!"andL"
  | andR (decl : LocalDecl) (_value : Box) => m!"andR {decl.type}"
  | orL (_inr : Box) => m!"orL"
  | orR (_inl : Box) => m!"orR"
  | haveB (decl : LocalDecl) (value : Expr) => m!"haveB {decl.type}, value: {value}"

instance : BEq PathItem where
  beq
    | .forallB .., .forallB ..
    | .metaVar .., .metaVar ..
    | .andL .., .andL ..
    | .andR .., .andR ..
    | .orL .., .orL ..
    | .orR .., .orR ..
    | .haveB .., .haveB .. => true
    | _, _ => false

instance : Hashable PathItem where
  hash
    | .forallB .. => 0
    | .metaVar .. => 1
    | .andL ..    => 2
    | .andR ..    => 3
    | .orL ..     => 4
    | .orR ..     => 5
    | .haveB ..   => 6

def PathItem.getLocalDecl? : PathItem → Option LocalDecl
| .forallB decl _ | andR decl _ | haveB decl _ => decl
| _ => none

-- structure Zipper where
--   path           : List PathItem
--   cursor         : Box
--   lctx           : LocalContext
--   localInstances : LocalInstances
--   mctx           : MetavarContext

-- def Zipper.up (zipper : Zipper) : Option Zipper := do
--   let item :: path := zipper.path | failure
--   let { cursor, .. } := zipper
--   let zipper := { zipper with path }
--   match item with
--   | .forallB decl hidden =>
--     return { zipper with
--       cursor := .forallB decl cursor hidden
--       lctx   := zipper.lctx.erase decl.fvarId  }
--   | .metaVar mvarId name type => return { zipper with cursor := .metaVar mvarId name type cursor }
--   | .andL decl body => return { zipper with cursor := .and decl cursor body }
--   | .andR decl value => return { zipper with cursor := .and decl value cursor }
--   | .orL inr => return { zipper with cursor := .or cursor inr }
--   | .orR inl => return { zipper with cursor := .or inl cursor }
--   | .haveB decl value => return { zipper with cursor := .haveB decl value cursor }

-- partial def Zipper.zip (zipper : Zipper) : Box :=
--   if let some zipper := zipper.up then
--     zipper.zip
--   else
--     zipper.cursor

-- def Zipper.down (zipper : Zipper) (coord : Coord) : MetaM Zipper := do
--   let { path, cursor, lctx, localInstances, mctx ..} := zipper
--   let withFVar (decl : LocalDecl) (pathItem : PathItem) (body : Box) : MetaM Zipper := do
--     withLCtx lctx localInstances do
--       withExistingLocalDecls [decl] do
--         return { zipper with
--           path := pathItem :: path
--           cursor := body
--           lctx := ← getLCtx
--           localInstances := ← getLocalInstances }
--   match coord, cursor with
--   | .forallB, .forallB decl body hidden => withFVar decl (.forallB decl hidden) body
--   | .metaVar, .metaVar mvarId name type body =>
--     -- let { userName, lctx, type, localInstances, kind, .. } := decl
--     return { zipper with
--       path := .metaVar mvarId name type :: path
--       cursor := body
--       mctx := mctx.addExprMVarDeclExp mvarId name lctx localInstances type (kind := .syntheticOpaque) }
--   | .andL   , .and decl value body => return { zipper with path := .andL decl body :: path, cursor := value }
--   | .andR   , .and decl value body => withFVar decl (.andR decl value) body
--   | .orL    , .or inl inr => return { zipper with path := .orL inr :: path, cursor := inl }
--   | .orR    , .or inl inr => return { zipper with path := .orR inl :: path, cursor := inr }
--   | .haveB  , .haveB decl value body => withFVar decl (.haveB decl value) body
--   | _       , _ => throwError "Zipper down coordinate is wrong: {repr coord}"


-- def Zipper.unzip (box : Box) (address : List Coord) : MetaM Zipper := do
--   go { path := [], cursor := box, lctx := {}, localInstances := {}, mctx := {} } address
-- where
--   go (zipper : Zipper) (address : List Coord) : MetaM Zipper := do
--     let coord :: address := address | return zipper
--     let zipper ← zipper.down coord
--     go zipper address


/-- Replace all occurrences of a variable with `new`. -/
def instantiateMVarWith (var e new : Expr) : CoreM Expr :=
  Core.transform e (post := (if · == var then return .done new else return .continue))

open Elab Tactic

def refreshIds (box : Box) : MetaM Box := sorry

def createTacticState (box : Box) : TacticM (Std.HashMap MVarId (List PathItem)) := do
  setGoals []
  setMCtx {}
  let (_, s) ← withLCtx {} {} <| ((go box).run []).run {}
  return s
where
  go : Box → (ReaderT (List PathItem) <| StateT (Std.HashMap MVarId (List PathItem)) TacticM) Unit
  | forallB decl body hidden =>
    withReader (.forallB decl hidden :: ·) do
      if hidden then go body else withExistingLocalDecls [decl] do go body
  | metaVar mvarId name type body =>
    withReader (.metaVar mvarId name type :: ·) do
      modifyMCtx (·.addExprMVarDeclExp mvarId name (← getLCtx) (← getLocalInstances) type (kind := .syntheticOpaque))
      pushGoal mvarId
      let address := (← read).reverse
      modify (·.insert mvarId address)
      go body
  | result _ => return
  | and decl value body => do
    withReader (.andL decl body :: ·) do go value
    withReader (.andR decl body :: ·) do withExistingLocalDecls [decl] do go body
  | or inl inr => do
    -- We should think about how to name the goals so that it helps the user.
    withReader (.orL inr :: ·) do go inl
    withReader (.orR inl :: ·) do go inr
  | haveB decl value body => do
    withReader (.haveB decl value :: ·) do withExistingLocalDecls [decl] do go body





def _root_.List.commonPrefix {α} [BEq α] (as bs : List α) : List α :=
  match as, bs with
  | a :: as, b :: bs => if a == b then a :: (as.commonPrefix bs) else []
  | _, _ => []

def minimalAddressFor (decl : LocalDecl) (value : Expr) (address : List PathItem) : MetaM (List PathItem) := do
  let type ← instantiateMVars decl.type
  let value ← instantiateMVars value
  let fvars := collectFVars {} type
  let fvars := collectFVars fvars value
  if fvars.fvarSet.isEmpty then return []
  let mut remainingFVars := fvars.fvarSet
  let mut addressArr := #[]
  for item in address do
    addressArr := addressArr.push item
    if let some decl := item.getLocalDecl? then
      remainingFVars := remainingFVars.erase decl.fvarId
      if remainingFVars.isEmpty then
        return addressArr.toList
  throwError "CACKLE CACKLE CACKLE can't bind {value} : {type} in path {address.map (·.format)}"


structure CleanUpTacticState where
  newMVars      : Std.HashMap MVarId (List PathItem) := {}
  newHaves      : Array (LocalDecl × Expr × List PathItem) := #[]
  assignedMVars : Array MVarId := #[]

/--
Collect the metavariables that appear in a goal after a tactic has been run, which modified the
metavariable context.
-/
def traverseAssignedMVarIds (addresses : Std.HashMap MVarId (List PathItem)) : StateT CleanUpTacticState TacticM Unit := do
  let goals ← getGoals
  for mvarId in goals do
    let some address := addresses[mvarId]? | throwError "NANANA incomplete addresses"
    if ← mvarId.isAssigned then
      modify fun s => { s with assignedMVars := s.assignedMVars.push mvarId }
      mvarId.withContext do
      let e ← instantiateMVars (.mvar mvarId)
      let newE ← Core.transform e (pre := fun e => do
        if let .mvar mvarId := e.getAppFn then
          if let some address' := (← get).newMVars[mvarId]? then
            let address' := address'.commonPrefix address
            modify fun s => { s with newMVars := s.newMVars.insert mvarId address' }
            return .continue (← instantiateMVars e)
          if let some { mvarIdPending, fvars } ← getDelayedMVarAssignment? mvarId then
            mvarIdPending.withContext do
              let allArgs := e.getAppArgs
              if allArgs.size < fvars.size then
                throwError "HOHOHO this isn't supported yet :("
              let mut args : Array (LocalDecl × Expr) := #[]
              for arg in allArgs, fvar in fvars do
                if arg.isFVar then
                  continue
                if arg.hasLooseBVars then
                  throwError "LALALA this isn't supported yet :("
                let fvarDecl ← getFVarLocalDecl fvar
                let shortenedPath ← minimalAddressFor fvarDecl arg address
                modify fun s => { s with newHaves := s.newHaves.push (fvarDecl, arg, shortenedPath) }
                args := args.push (← getFVarLocalDecl fvar, arg)
              let replacement := (← mvarIdPending.getDecl).lctx.mkLambda fvars (← instantiateMVars (.mvar mvarIdPending))
              mvarId.assign replacement
              return .continue (← instantiateMVars e)
          else
            modify fun s => { s with newMVars := s.newMVars.insert mvarId address }
            return .continue
        else
          return .continue)
      mvarId.assign newE



/-- The addresses in this structure are stored in reverse order. -/
structure UpdateBoxContext where
  removeMVar : Std.HashMap (List PathItem) (Array MVarId) := {}  -- no need to store the `mvarId` here. We do it just for sanity
  newMVars   : Std.HashMap (List PathItem) (Array MVarId) := {}
  newHaves   : Std.HashMap (List PathItem) (Array (LocalDecl × Expr)) := {}
  address    : List PathItem := []

def withPathItem {α m} [Monad m] [MonadWithReader UpdateBoxContext m] (item : PathItem) : m α → m α :=
  withReader (· %.address (item :: ·))

def _root_.Std.HashMap.insertInArray {α} {β} [BEq α] [Hashable α] (m : Std.HashMap α (Array β)) (a : α) (b : β) : Std.HashMap α (Array β) :=
  m.alter a fun
    | none => #[b]
    | some arr => arr.push b

def CleanUpTacticState.toUpdateBoxContext (addresses : Std.HashMap MVarId (List PathItem)) : CleanUpTacticState → MetaM UpdateBoxContext
  | { newMVars, newHaves, assignedMVars } => do
    let mut ctx := {}
    for mvarId in assignedMVars do
      let some address := addresses[mvarId]? | throwError "QWERTY No Address available for {mvarId}"
      ctx :=.removeMVar (·.insertInArray address.reverse mvarId)
    for (decl, value, address) in newHaves do
      ctx :=.newHaves (·.insertInArray address.reverse (decl, value))
    for (mvarId, address) in newMVars do
      ctx :=.newMVars (·.insertInArray address.reverse mvarId)
    return ctx

nonrec def _root_.Lean.LocalDecl.instantiateMVars : LocalDecl → MetaM LocalDecl
  | .cdecl index fvarId userName type bi kind           => return .cdecl index fvarId userName (← instantiateMVars type) bi kind
  | .ldecl index fvarId userName type value nonDep kind => return .ldecl index fvarId userName (← instantiateMVars type) (← instantiateMVars value) nonDep kind


def updateBox (box : Box) (addresses : Std.HashMap MVarId (List PathItem)) : TacticM Box := do
  let (_, state) ← traverseAssignedMVarIds addresses |>.run {}
  let box ← go box |>.run (← state.toUpdateBoxContext addresses)
  setMCtx {}
  setGoals []
  return box
where
  go (box : Box) : ReaderT UpdateBoxContext MetaM Box := do
    let mut box : Box ← (do match box with
      | .forallB decl body hidden =>
        let decl ← decl.instantiateMVars
        let body ← withPathItem (.forallB decl hidden) <| go body
        return .forallB decl body hidden
      | .metaVar mvarId name type body =>
        let type ← instantiateMVars type
        let body ← withPathItem (.metaVar mvarId name type) <| go body
        return .metaVar mvarId name type body
      | .result r => return .result (← instantiateMVars r)
      | .and decl value body =>
        let decl ← decl.instantiateMVars
        let value ← withPathItem (.andL decl body) <| go value
        let body ← withPathItem (.andR decl value) <| go body
        return .and decl value body
      | .or inl inr =>
        let inl ← withPathItem (.orL inr) <| go inl
        let inr ← withPathItem (.orR inl) <| go inr
        return .or inl inr
      | .haveB decl value body =>
        let decl ← decl.instantiateMVars
        let value ← instantiateMVars value
        let body ← withPathItem (.haveB decl value) <| go body
        return .haveB decl value body)

    let { removeMVar, newMVars, newHaves, address } ← read
    if let some mvarIds := removeMVar[address]? then
      let #[mvarId] := mvarIds | throwError "Didn't get 1 mvarId: {mvarIds}"
      let .metaVar mvarId' _ _ body := box | throwError "Expected a metavar goal"
      unless mvarId' == mvarId do throwError "metavar MVarId doesn't match: {mvarId} ≠ {mvarId'}"
      box := body
    if let some mvarIds := newMVars[address]? then
      -- need to ensure `mvarId`s are in the right order (we don't care right now)
      for mvarId in mvarIds do
        let { userName, type, .. } ← mvarId.getDecl
        box := .metaVar mvarId userName type box
    if let some haves := newHaves[address]? then
      for (decl, value) in haves do
        box := .haveB decl value box
    return box


/-
TODO:

- for a new have binder, find the prefix of the path for its location

- for new metavariables, find the location/address by intersecting the addresses.

- while traversing the metavariables assignments, replace delayed assigned metavariables.

-/

section RunTactic

open Elab Tactic



def runTactic (box : Box) (address : List PathItem) (tac : TacticM Unit) : MetaM Box := do
  sorry

end RunTactic


section Elab

structure State where
  box       : Box
  goals     : Array MVarId
  addresses : Std.HashMap MVarId (List PathItem)

open Elab Parser Tactic

declare_syntax_cat box_tactic

@[inline] def boxTacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `box_tactic rbp

def boxTacticSeq1Indented : Parser := leading_parser
  sepBy1IndentSemicolon boxTacticParser

def boxTacticSeqBracketed : Parser := leading_parser
  "{" >> sepByIndentSemicolon boxTacticParser >> ppDedent (ppLine >> "}")

def boxTacticSeq := leading_parser
  boxTacticSeqBracketed <|> boxTacticSeq1Indented

syntax (name := lean_tactic) tactic : box_tactic

def evalBoxTactic (stx : Syntax) (box : Box) (address : List PathItem) : MetaM Box := do
  match stx with
  | `(box_tactic| $tac:tactic) => runTactic box (evalTactic tac)
  | _ => throwUnsupportedSyntax

-- @[incremental]
-- def evalBoxTacticSeq : Tactic :=
--   Term.withNarrowedArgTacticReuse (argIdx := 0) evalBoxTactic


end Elab


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
-- open Lean Meta Elab

-- elab "test" e:tactic : tactic => do
--   -- let e ← Term.elabTerm e none
--   -- logInfo m! "{e}"
--   let mvarId ← Tactic.getMainGoal
--   Tactic.evalTactic e
--   let mvarIdNew ← Tactic.getMainGoal
--   liftMetaM do
--   logInfo m! "{repr mvarId}; {← instantiateMVars <| Expr.mvar mvarId}"
--   logInfo m! "{repr mvarIdNew}; {← instantiateMVars <| Expr.mvar mvarIdNew}"
--   let (_, mvars) ← collectMVars (.mvar mvarId) |>.run {}
--   for mvar in mvars.result do
--     logInfo m! "{repr mvar}; {← instantiateMVars <| Expr.mvar mvar}; {mvar}"
--     if let some x ← getDelayedMVarAssignment? mvar then
--       logInfo m! "delayed assigment of {Expr.mvar mvar}: {Expr.mvar x.mvarIdPending}"
-- set_option pp.instantiateMVars false
-- example {P : α → Prop} (x : α) (y : α) {β : Type} (h': True) (h : α = β) (z : Nat) : P x := by
--   -- -- clear y
--   -- rw [h] at y
--   test rw [h] at y
-- #check Exists.casesOn
-- example {P : α → Prop} (h : ∃ x, P x) (a : Nat) : False := by
--   test cases h

-- example {α β : Nat} (P : Nat → Prop) (h : P α) (h' : α = β) : False := by
--   test rw [h'] at h

-- example {α β : Nat} (h' : 15 = β) (h : True) : False := by
--   test induction β generalizing h

-- example {p q : Prop} (h : p) (g : False) : q := by
--   contrapose h
