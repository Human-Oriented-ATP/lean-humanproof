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
  | metaVar mvarId _name type body => do
    -- modifyMCtx (·.addExprMVarDeclExp mvarId name (← getLCtx) (← getLocalInstances) type (kind := .syntheticOpaque))
    addMessageContext m! "{mkMVar mvarId} : {type},\n{← body.show}"
  | result r => return m! "▸ {r}"
  | and decl value body =>
    let value ← value.show
    withExistingLocalDecls [decl] do
      addMessageContext m! "And {decl.userName} : {decl.type} := {value}\n{← body.show}"
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

-- TODO: remove some unused arguments from the constructors
inductive PathItem where
  | forallB (decl : LocalDecl) (hidden : Bool)
  | metaVar (mvarId : MVarId) (name : Name) (type : Expr)
  | andL (decl : LocalDecl) (body : Box)
  | andR (decl : LocalDecl) (value : Box)
  | imaginaryAnd (fvarId : FVarId)
  | orL (inr : Box)
  | orR (inl : Box)
  | haveB (decl : LocalDecl) (value : Expr)

def PathItem.toMessageData : PathItem → MessageData
  | forallB decl _hidden => m!"forallB {decl.userName} : {decl.type}"
  | metaVar _mvarId _name type => m!"metaVar {type}"
  | andL _decl _body => m!"andL"
  | andR decl _value => m!"andR {decl.type}"
  | imaginaryAnd fvarId => m!"imaginary and for {mkFVar fvarId}"
  | orL _inr => m!"orL"
  | orR _inl => m!"orR"
  | haveB decl value => m!"haveB {decl.userName} : {decl.type}, value: {value}"

instance : ToMessageData PathItem := ⟨PathItem.toMessageData⟩

instance : BEq PathItem where
  beq
    | .forallB .., .forallB ..
    | .metaVar .., .metaVar ..
    | .andL .., .andL ..
    | .andR .., .andR ..
    | .orL .., .orL ..
    | .orR .., .orR ..
    | .haveB .., .haveB .. => true
    | .imaginaryAnd fvarId, .imaginaryAnd fvarId' => fvarId == fvarId'
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
    | .imaginaryAnd fvarId => hash fvarId

def PathItem.getLocalDecl? : PathItem → Option LocalDecl
| .forallB decl _ | andR decl _ | haveB decl _ => decl
| _ => none


/-- Replace all occurrences of a variable with `new`. -/
def instantiateMVarWith (var e new : Expr) : CoreM Expr :=
  Core.transform e (post := (if · == var then return .done new else return .continue))

open Elab Tactic


section ToTacticState

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
  | .cdecl index fvarId userName type bi kind => do
    let type ← type.replaceVars
    if hidden then
      let fvarId' ← mkFreshFVarId
      modify (· %.fvarReplacements (·.insert fvarId (.fvar fvarId')))
      k (.cdecl index fvarId' userName type bi kind)
    else
      withLocalDecl userName bi type (kind := kind) fun fvar => do
        modify (· %.fvarReplacements (·.insert fvarId fvar))
        k <| (← fvar.fvarId!.getDecl)
  | .ldecl _ fvarId userName type value _ kind => do
    let type ← type.replaceVars
    let value ← value.replaceVars
    withLetDecl userName type value (kind := kind) fun fvar => do
    modify (· %.fvarReplacements (·.insert fvarId fvar))
    k <| (← fvar.fvarId!.getDecl)


def createTacticState (box : Box) : ExceptT Expr TacticM (Box × Std.HashMap MVarId (List PathItem)) := do
  setGoals []
  let (box, s) ← (go box).run [] |>.run {}
  -- liftMetaM <| logInfo m! "renamed box: {← box.show}"

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

end ToTacticState


section FixTacticState

def commonPrefix2 {α} [BEq α] (as bs : List α) : List α :=
  match as, bs with
  | a :: as, b :: bs => if a == b then a :: (commonPrefix2 as bs) else []
  | _, _ => []

def commonPrefix {α} [BEq α] (ass : List (List α)) : List α :=
  match ass with
  | [] => panic! "empty list passed to `commonPrefix`"
  | as :: ass => ass.foldl (init := as) commonPrefix2

inductive BoxOrigin where
| goal (mvarId : MVarId) | newAnd (fvarId : FVarId)
deriving BEq, Hashable

instance : ToMessageData BoxOrigin where
  toMessageData
    | .goal mvarId => m! "goal {mkMVar mvarId}"
    | .newAnd fvarId => m! "new And {mkFVar fvarId}"

abbrev BoxOrigins := Std.HashSet BoxOrigin

structure CleanUpTacticState where
  newMVars      : Std.HashMap MVarId BoxOrigins := {}
  newMVarsArr   : Array MVarId := #[] -- This is to avoid depending on order of hash values
  newAnds       : Std.HashMap FVarId (BoxOrigins × LocalDecl × Array Expr × MVarId) := {}
  newHaves      : Array (LocalDecl × Expr × BoxOrigin) := #[]
  assignedMVars : Array MVarId := #[]


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
  throwError "CACKLE CACKLE CACKLE can't bind {value} : {type} in path {address.map (·.toMessageData)}, with remaining variables {remainingFVars.toList.map mkFVar}"


partial def computeAndAddress (fvarId : FVarId)
    (newAnds : Std.HashMap FVarId (BoxOrigins × LocalDecl × Array Expr × MVarId)) :
    StateT (Std.HashMap BoxOrigin (List PathItem)) MetaM (List PathItem) := do
  let map ← get
  if let some address := map[BoxOrigin.newAnd fvarId]? then
    return address
  let some (origins, _, fvars, mvarId) := newAnds[fvarId]? | throwError "fvar {mkFVar fvarId} isn't in {newAnds.keys.map mkFVar}"
  let paths ← origins.toList.mapM fun
    | .goal mvarId   => map[BoxOrigin.goal mvarId]?.getDM do throwError "mvar {mkMVar mvarId} isn't in {map.keys}"
    | .newAnd fvarId => computeAndAddress fvarId newAnds
  let path := commonPrefix paths
  let tail ← mvarId.withContext do fvars.toList.mapM fun fvar => return .forallB (← fvar.fvarId!.getDecl) (hidden := false)
  let path := path ++ .imaginaryAnd fvarId :: tail
  modify (·.insert (.newAnd fvarId) path)
  return path

/-- The addresses in this structure are stored in reverse order. -/
structure UpdateBoxContext where
  removeMVar : Std.HashMap (List PathItem) (Array MVarId) := {}  -- no need to store the `mvarId` here. We do it just for sanity
  newMVars   : Std.HashMap (List PathItem) (Array MVarId) := {}
  newAnds    : Std.HashMap (List PathItem) (Array (LocalDecl × Array Expr × MVarId)) := {}
  newHaves   : Std.HashMap (List PathItem) (Array (LocalDecl × Expr)) := {}
  address    : List PathItem := []

def _root_.Std.HashMap.insertInArray {α} {β} [BEq α] [Hashable α] (m : Std.HashMap α (Array β)) (a : α) (b : β) : Std.HashMap α (Array β) :=
  m.alter a fun
    | none => #[b]
    | some arr => arr.push b

/--
Collect the metavariables that appear in a goal after a tactic has been run, which modified the
metavariable context.
-/
partial def traverseAssignedMVarIds (goals : List MVarId) (addresses : Std.HashMap MVarId (List PathItem)) : MetaM UpdateBoxContext := do
  let (_, { newMVars, newMVarsArr, newAnds, newHaves, assignedMVars }) ← StateT.run (s := {}) <| goals.forM fun mvarId => do
    if ← mvarId.isAssigned then
      modify (· %.assignedMVars (·.push mvarId))
      traverse mvarId (.goal mvarId)
  -- Now we compute for each origin the corresponding address
  let addresses := addresses.fold (init := {}) fun map mvarId address => map.insert (.goal mvarId) address
  let (_, addresses) ← (newAnds.forM fun fvarId _ => discard <| computeAndAddress fvarId newAnds).run addresses

  let mut ctx := {}
  for mvarId in assignedMVars do
    let some address := addresses[BoxOrigin.goal mvarId]? | throwError "QWERTY No Address available for {mvarId}"
    ctx :=.removeMVar (·.insertInArray address.reverse mvarId)
  for (decl, value, origin) in newHaves do
    let address := addresses[origin]!
    let address ← minimalAddressFor decl value address
    let address := address.reverse
    ctx :=.newHaves (·.insertInArray address (decl, value))
  for mvarId in newMVarsArr do
    let origins := newMVars[mvarId]!
    let address := (commonPrefix <| origins.toList.map (addresses[·]!)).reverse
    ctx :=.newMVars (·.insertInArray address mvarId)
  for (fvarId, origins, rest) in newAnds do
    let address := (commonPrefix <| origins.toList.map (addresses[·]!)).reverse
    ctx :=.newAnds (·.insertInArray address rest)
  return ctx
where
  mkNewAnd (fvars : Array Expr) (i : Nat) (mvarId mvarIdPending : MVarId) (origin : BoxOrigin) : StateT CleanUpTacticState MetaM Unit := do
    let type ← mvarIdPending.getType
    let type := (← mvarIdPending.getDecl).lctx.mkForall fvars[i:] type
    let type ← instantiateMVars type
    let decl ← withLocalDeclD (← mvarId.getTag) type (·.fvarId!.getDecl)
    let fvarId := decl.fvarId
    mvarId.assign <| (← mvarIdPending.getDecl).lctx.mkLambda fvars[:i] (.fvar fvarId)
    modify (· %.newAnds (·.insert fvarId ({origin}, decl, fvars[i:], mvarIdPending)))
    traverse mvarIdPending (.newAnd fvarId)

  traverse (mvarId : MVarId) (origin : BoxOrigin) : StateT CleanUpTacticState MetaM Unit :=
    discard <| mvarId.withContext do Core.transform (← instantiateMVars (.mvar mvarId)) (pre := fun e => do
      match e.getAppFn with
      | .fvar fvarId =>
        modify (· %.newAnds (·.modify fvarId fun (app, rest) => (app.insert origin, rest)))
        return .continue
      | .mvar mvarId =>
        if ← mvarId.isAssigned then
          return .visit (← instantiateMVars e)
        if goals.contains mvarId then return .continue
        -- logInfo m!"looking at {mkMVar mvarId}"
        if let some { mvarIdPending, fvars } ← getDelayedMVarAssignment? mvarId then
          mvarIdPending.withContext do
            let allArgs := e.getAppArgs
            let mut args : Array (LocalDecl × Expr) := #[]
            let mut i := 0
            repeat
              if h : i ≥ fvars.size then
                mvarId.assign <| (← mvarIdPending.getDecl).lctx.mkLambda fvars (← instantiateMVars (.mvar mvarIdPending))
                break
              else
              let fvar := fvars[i]
              let some arg := allArgs[i]? | mkNewAnd fvars i mvarId mvarIdPending origin; break
              if arg.isFVar then
                continue
              if arg.hasLooseBVars then
                mkNewAnd fvars i mvarId mvarIdPending origin; break
              let fvarDecl ← getFVarLocalDecl fvar
              modify (· %.newHaves (·.push (fvarDecl, arg, origin))) -- shortenedPath)))
              args := args.push (← getFVarLocalDecl fvar, arg)
              i := i + 1
            return .continue -- .visit (← instantiateMVars e)
        else
          unless (← get).newMVars.contains mvarId do
            modify (· %.newMVarsArr (·.push mvarId))
          modify (· %.newMVars (·.alter mvarId fun | none => some {origin} | some origins => origins.insert origin))
          return .continue
      | _ => return .continue)


nonrec def _root_.Lean.LocalDecl.instantiateMVars : LocalDecl → MetaM LocalDecl
  | .cdecl index fvarId userName type bi kind           => return .cdecl index fvarId userName (← instantiateMVars type) bi kind
  | .ldecl index fvarId userName type value nonDep kind => return .ldecl index fvarId userName (← instantiateMVars type) (← instantiateMVars value) nonDep kind


abbrev UpdateBoxM α := ReaderT UpdateBoxContext MetaM α

def withPathItem {α} (item : PathItem) : UpdateBoxM α → UpdateBoxM α :=
  withReader (· %.address (item :: ·))

partial def updateBox (box : Box) (goals : List MVarId) (addresses : Std.HashMap MVarId (List PathItem)) : TacticM Box := do
  let ctx ← traverseAssignedMVarIds goals addresses
  go box |>.run ctx
where
  go (box : Box) : UpdateBoxM Box := do
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

    let { removeMVar, newMVars, newAnds, newHaves, address } ← read
    if let some mvarIds := removeMVar[address]? then
      let #[mvarId] := mvarIds | throwError "Didn't get 1 mvarId: {mvarIds}"
      let .metaVar mvarId' _ _ body := box | throwError "Expected a metavar goal"
      unless mvarId' == mvarId do throwError "metavar MVarId doesn't match: {repr mvarId} ≠ {repr mvarId'}"
      box := body
    if let some mvarIds := newMVars[address]? then
      -- need to ensure `mvarId`s are in the right order (we don't care right now)
      -- HACK: reverse the array
      for mvarId in mvarIds.reverse do
        let { userName, type, .. } ← mvarId.getDecl
        let type ← instantiateMVars type
        box := .metaVar mvarId userName type box
    if let some newAnds := newAnds[address]? then
      for (decl, fvars, mvarId) in newAnds do
        let e ← instantiateMVars (.mvar mvarId)
        let value := .result e
        let value ← mvarId.withContext do fvars.foldrM (init := value) fun fvar box =>
          return Box.forallB (← fvar.fvarId!.getDecl) box (hidden := false)
        let value ← withPathItem (.imaginaryAnd decl.fvarId) <| go value
        box := .and decl value box

    if let some haves := newHaves[address]? then
      for (decl, value) in haves do
        box := .haveB decl value box
    return box

end FixTacticState

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
    -- liftMetaM <| logInfo m! "after tactic: {← box.show}"
    let box ← updateBox box goalsBefore addresses
    -- liftMetaM <| logInfo m! "after update: {← box.show}"
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
      -- mainGoal.withContext <| logInfo m!"Done, with proof term {indentExpr proof}"
    | .ok box =>
      throwError "Box proof is not finished"--\n{← box.show}"
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

example (x y : Int) : True ∧ ∀ a b c : Nat, a = b → a = c → b = c := by
  box_proof
    constructor
    skip
    intro a
    skip
    intro b
    intro c
    intro h
    intro g
    rw [h] at g
    exact g
    trivial



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


-- fun x => ?f x
-- ?f
