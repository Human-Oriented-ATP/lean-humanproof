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

def Box.show (box : Box) : MetaM (MessageData) := do
  match box with
  | forallB decl body _hidden =>
    withExistingLocalDecls [decl] do
      addMessageContext m! "∀ ({decl.userName} : {decl.type}),\n{← body.show}"
  | metaVar mvarId name type body => do
    modifyMCtx (·.addExprMVarDeclExp mvarId name (← getLCtx) (← getLocalInstances) type (kind := .syntheticOpaque))
    addMessageContext m! "{mkMVar mvarId} : {type},\n{← body.show}"
  | result r => return m! "▸ {r}"
  | and decl value body =>
    withExistingLocalDecls [decl] do
      addMessageContext m! "And {decl.userName} : {decl.type} := {← value.show}\n{← body.show}"
  | or inl inr =>
    return m! "{← inl.show} Or\n{← inr.show}"
  | haveB decl value body =>
    withExistingLocalDecls [decl] do
      addMessageContext m! "Have {decl.userName} : {decl.type} := {value}\n{← body.show}"

namespace Box

def _root_.Lean.LocalDecl.mkLambda (decl : LocalDecl) (e : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  .lam decl.userName decl.type e decl.binderInfo

def _root_.Lean.LocalDecl.mkLet (decl : LocalDecl) (e value : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  Lean.mkLet decl.userName decl.type value e

def getResults (box : Box) : MetaM (Array Expr) := do
  let results ← go box
  return results.filter (!·.hasMVar)
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

def getResult (box : Box) : MetaM (Option Expr) := do
  let results ← box.getResults
  if h : results.size ≠ 0 then
    return results[0]
  else
    return none

inductive PathItem where
  | forallB (decl : LocalDecl) (hidden : Bool)
  | metaVar (mvarId : MVarId) (name : Name) (type : Expr)
  | andL (decl : LocalDecl) (body : Box)
  | andR (decl : LocalDecl) (value : Box)
  | orL (inr : Box)
  | orR (inl : Box)
  | haveB (decl : LocalDecl) (value : Expr)

def PathItem.format : PathItem → MessageData
  | forallB (decl : LocalDecl) (_hidden : Bool) => m!"forallB {decl.userName} : {decl.type}"
  | metaVar (_mvarId : MVarId) (_name : Name) (type : Expr) => m!"metaVar {type}"
  | andL (_decl : LocalDecl) (_body : Box) => m!"andL"
  | andR (decl : LocalDecl) (_value : Box) => m!"andR {decl.type}"
  | orL (_inr : Box) => m!"orL"
  | orR (_inl : Box) => m!"orR"
  | haveB (decl : LocalDecl) (value : Expr) => m!"haveB {decl.userName} : {decl.type}, value: {value}"

instance : ToMessageData PathItem := ⟨PathItem.format⟩

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


/-- Replace all occurrences of a variable with `new`. -/
def instantiateMVarWith (var e new : Expr) : CoreM Expr :=
  Core.transform e (post := (if · == var then return .done new else return .continue))

open Elab Tactic




structure CreateTacticState where
  addresses        : Std.HashMap MVarId (List PathItem) := {}
  mvarReplacements : Std.HashMap MVarId Expr := {}
  fvarReplacements : Std.HashMap FVarId Expr := {}

abbrev CreateTacticM := ReaderT (List PathItem) StateRefT CreateTacticState TacticM

def _root_.Lean.Expr.replaceVars (eIn : Expr) : CreateTacticM Expr := do
  Core.transform eIn (pre := fun e => do
    match e with
    | .mvar mvarId =>
      if let some e := (← get).mvarReplacements[mvarId]? then
        return .done e
      else
        throwError "Meta variable {mvarId} isn't bound :((( in {eIn}"
    | .fvar fvarId =>
      if let some e := (← get).fvarReplacements[fvarId]? then
        return .done e
      else
        throwError "Free variable {e} isn't bound :((("
    | _ => return .continue)

def _root_.Lean.LocalDecl.withReplaceVars {α} (k : LocalDecl → CreateTacticM α) (hidden : Bool := false) : LocalDecl → CreateTacticM α
  | .cdecl index fvarId userName type bi kind =>
    (if hidden then fun k => do k <| .fvar (← mkFreshFVarId) else withLocalDecl userName bi type) fun fvar => do
      modify (· %.fvarReplacements (·.insert fvarId fvar))
      k <| .cdecl index fvar.fvarId! userName (← type.replaceVars) bi kind
  | .ldecl index fvarId userName type value nonDep kind => do
    withLetDecl userName type value fun fvar => do
    modify (· %.fvarReplacements (·.insert fvarId fvar))
    k <| .ldecl index fvar.fvarId! userName (← type.replaceVars) (← value.replaceVars) nonDep kind


def createTacticState (box : Box) : ExceptT Expr TacticM (Box × Std.HashMap MVarId (List PathItem)) := do
  setGoals []
  let (box, s) ← (go box).run [] |>.run {}
  liftMetaM <| logInfo m! "renamed box: {← box.show}"

  if (← getGoals).isEmpty then
    if let some proof ← box.getResult then
      throwThe _ proof
    else
      throwError "couldn't get the result from {← box.show}"
  else
    return (box, s.addresses)
where
  go : Box → (ReaderT (List PathItem) StateRefT CreateTacticState TacticM) Box
  | forallB decl body hidden => do
      if hidden then
        let body ← withReader (.forallB decl hidden :: ·) do go body
        return .forallB decl body hidden
      else
        decl.withReplaceVars (hidden := hidden) fun decl => do
          let body ← withReader (.forallB decl hidden :: ·) do go body
          return .forallB decl body hidden
  | metaVar mvarId name type body => do
    let type ← type.replaceVars
    let mvar ← mkFreshExprMVar type (userName := name)
    modify (· %.mvarReplacements (·.insert mvarId mvar))
    let mvarId := mvar.mvarId!
    pushGoal mvarId
    let address := (← read).reverse
    modify (· %.addresses (·.insert mvarId address))
    .metaVar mvarId name type <$> withReader (.metaVar mvarId name type :: ·) do go body
  | result r => return .result (← r.replaceVars)
  | and decl value body => do
    let value ← withReader (.andL decl body :: ·) do go value
    decl.withReplaceVars fun decl => do
      let body ← withReader (.andR decl body :: ·) do go body
      return .and decl value body
  | or inl inr => do
    -- We should think about how to name the goals so that it helps the user.
    let inl ← withReader (.orL inr :: ·) do go inl
    let inr ← withReader (.orR inl :: ·) do go inr
    return .or inl inr
  | haveB decl value body => do
    let value ← value.replaceVars
    decl.withReplaceVars fun decl => do
      let body ← withReader (.haveB decl value :: ·) do go body
      return .haveB decl value body



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
  throwError "CACKLE CACKLE CACKLE can't bind {value} : {type} in path {address.map (·.format)}, with remaining variables {remainingFVars.toList.map mkFVar}"


structure CleanUpTacticState where
  newMVars      : Std.HashMap MVarId (List PathItem) := {}
  newHaves      : Array (LocalDecl × Expr × List PathItem) := #[]
  assignedMVars : Array MVarId := #[]

/--
Collect the metavariables that appear in a goal after a tactic has been run, which modified the
metavariable context.
-/
def traverseAssignedMVarIds (goals : List MVarId) (addresses : Std.HashMap MVarId (List PathItem)) : StateT CleanUpTacticState MetaM Unit := do
  for mvarId in goals do
    let some address := addresses[mvarId]? | throwError m!"NANANA incomplete addresses {addresses.values}"
    if ← mvarId.isAssigned then
      modify fun s => { s with assignedMVars := s.assignedMVars.push mvarId }
      mvarId.withContext do
      let e ← instantiateMVars (.mvar mvarId)
      let newE ← Core.transform e (pre := fun e => do
        if let .mvar mvarId := e.getAppFn then
          if goals.contains mvarId then
            return .continue
          logInfo m!"looking at {mkMVar mvarId}"
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
              return .visit (← instantiateMVars e)
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

abbrev UpdateBoxM α := ReaderT UpdateBoxContext MetaM α

def withPathItem {α} (item : PathItem) : UpdateBoxM α → UpdateBoxM α :=
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


def updateBox (box : Box) (goals : List MVarId) (addresses : Std.HashMap MVarId (List PathItem)) : TacticM Box := do
  let (_, state) ← traverseAssignedMVarIds goals addresses |>.run {}
  go box |>.run (← state.toUpdateBoxContext addresses)
where
  go (box : Box) : UpdateBoxM Box := do
    let mut box : Box ← (do match box with
      | .forallB decl body hidden =>
        let decl ← decl.instantiateMVars
        let body ← withPathItem (.forallB decl hidden) <| go body
        return .forallB decl body hidden
      | .metaVar mvarId name type body =>
        logInfo m! "instantiated {type}"
        let type ← instantiateMVars type
        let body ← withPathItem (.metaVar mvarId name type) <| go body
        return .metaVar mvarId name type body
      | .result r => logInfo m! "{r}"; return .result (← instantiateMVars r)
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
      unless mvarId' == mvarId do throwError "metavar MVarId doesn't match: {repr mvarId} ≠ {repr mvarId'}"
      box := body
    if let some mvarIds := newMVars[address]? then
      -- need to ensure `mvarId`s are in the right order (we don't care right now)
      for mvarId in mvarIds.reverse do
        let { userName, type, .. } ← mvarId.getDecl
        let type ← instantiateMVars type
        box := .metaVar mvarId userName type box
    if let some haves := newHaves[address]? then
      for (decl, value) in haves do
        box := .haveB decl value box
    return box


section RunTactic

open Elab Parser Tactic

declare_syntax_cat box_tactic
syntax (name := lean_tactic) tactic : box_tactic

@[inline] def boxTacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `box_tactic rbp

def boxTacticSeq1Indented : Parser := leading_parser
  sepBy1IndentSemicolon boxTacticParser

def boxTacticSeqBracketed : Parser := leading_parser
  "{" >> sepByIndentSemicolon boxTacticParser >> ppDedent (ppLine >> "}")

def boxTacticSeq := leading_parser
  ppIndent (boxTacticSeqBracketed <|> boxTacticSeq1Indented)

def evalBoxTactic (stx : TSyntax `box_tactic) : TacticM Unit := do
  match stx with
  | `(box_tactic| $tac:tactic) => evalTactic tac
  | _ => throwUnsupportedSyntax

syntax (name := box_proof) "box_proof" ppLine boxTacticSeq : tactic

def createProofBox (mvarId : MVarId) : MetaM (Array Expr × Box) := do
  let { userName, type, kind, .. } ← mvarId.getDecl
  let mvar' ← mkFreshExprMVar type kind userName
  let mut box : Box := .metaVar mvar'.mvarId! userName type (.result mvar')
  let lctxArr := (← mvarId.getDecl).lctx.decls.toArray.filterMap id |>.filter (!·.isAuxDecl)
  for decl in lctxArr.reverse do -- reversing to add in the right order
    box := .forallB decl box
  return (lctxArr.map LocalDecl.toExpr, box)


def runBoxTactic (box : Box) (tactic : TSyntax `box_tactic) (addresses : Std.HashMap MVarId (List PathItem)) : TacticM Box := withRef tactic do
  match tactic with
  | `(box_tactic| $tactic:tactic) =>
    let goalsBefore ← getGoals
    evalTactic tactic
    let goalsAfter ← getGoals
    liftMetaM <| logInfo m! "after tactic: {← box.show}"
    let box ← updateBox box goalsBefore addresses
    liftMetaM <| logInfo m! "after update: {← box.show}"
    return box
  | _ => throwUnsupportedSyntax

def boxLoop (box : Box) (tactics : Syntax.TSepArray `box_tactic "") : ExceptT Expr TacticM Box := do
  let box ← tactics.getElems.foldlM (init := box) fun box (tactic : TSyntax `box_tactic) => do
    let (box, addresses) ← withRef tactic do createTacticState box
    runBoxTactic box tactic addresses
  let (box, _addresses) ← createTacticState box
  return box


@[incremental, tactic box_proof]
def boxProofElab : Tactic
  | `(tactic| box_proof%$start $tactics*) => withMainContext do
    if (← getGoals).length > 1 then
      logWarning "Box proofs are meant to be initialized when there is just one goal."
    let mainGoal ← getMainGoal
    let (lctxArr, box) ← createProofBox mainGoal
    withLCtx {} {} do

    match ← boxLoop box tactics with
    | .error proof =>
      mainGoal.assign (mkAppN proof lctxArr)
      mainGoal.withContext <| logInfo m!"Done, with proof term {indentExpr proof}"
    | .ok box =>
      throwError "Box proof is not finished\n{← box.show}"
  | _ => throwUnsupportedSyntax

end RunTactic

section Test

example (g : 1 = 1) (h : 3 = 2 + 1) : (2 + 1) = 3 := by
  skip
  box_proof
    rw [← h]

example (n m k : Nat) (h: n = m) (h' : m = k) : n = k ∧ n = k := by
  box_proof
    constructor
    rw [← h] at h'
    rw [h']
    exact h'


end Test

section Elab


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
