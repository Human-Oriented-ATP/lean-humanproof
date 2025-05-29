import HumanProof.Defs
import Batteries
import Qq

namespace HumanProof.Box

open Lean Meta Elab Tactic

section ToTacticState

structure BoxState where
  box : Box
  addresses : Std.HashMap MVarId (List Box.PathItem) := {}
  focus : MVarId
  mvarReplacements : Std.HashMap MVarId Expr := {}
  fvarReplacements : Std.HashMap FVarId Expr := {}

abbrev BoxM := StateRefT BoxState TacticM

def BoxM.run {α} (box : Box) (focus : MVarId) (x : BoxM α) : TacticM α :=
  StateRefT'.run' x { box, focus }

abbrev CreateTacticM := ReaderT (List PathItem) BoxM

def _root_.Lean.Expr.replaceVars (eIn : Expr) (throw : Bool := true) : CreateTacticM Expr := do
  Core.transform eIn (pre := fun e => do
    match e with
    | .mvar mvarId =>
      if let some e := (← get).mvarReplacements[mvarId]? then
        return .done e
      else
        if throw then
          throwError "Meta variable {mvarId} isn't bound :((( in {eIn}"
        return .continue
    | .fvar fvarId =>
      if let some e := (← get).fvarReplacements[fvarId]? then
        return .done e
      else
        if throw then
          throwError "Free variable {e} isn't bound :((( in {eIn}"
        return .continue
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


def createTacticState : ExceptT Expr BoxM Unit := do
  setGoals []
  let box ← (go true (← get).box).run []
  if (← getGoals).isEmpty then
    if let some proof ← box.getResult then
      throwThe _ proof
    else
      throwError "couldn't get the result from {← box.show}"
  else
    modify ({ · with box })
where
  go (inMain : Bool) : Box → ReaderT (List PathItem) BoxM Box
  | forallB decl body hidden => do
      decl.withReplaceVars (hidden := hidden) fun decl => do
        let body ← withReader (.forallB decl hidden :: ·) do go inMain body
        return .forallB decl body hidden
  | metaVar mvarId name type body => do
    let type ← type.replaceVars
    let mvar ← mkFreshExprMVar type (userName := (if inMain then name else .anonymous)) (kind := .syntheticOpaque)
    modify (· %.mvarReplacements (·.insert mvarId mvar))
    let mvarId := mvar.mvarId!
    if inMain then
      pushGoal mvarId
      let address := (← read).reverse
      modify (· %.addresses (·.insert mvarId address))
    .metaVar mvarId name type <$> withReader (.metaVar mvarId name type :: ·) do go inMain body
  | result r => return .result (← r.replaceVars)
  | and decl value body => do
    let decl ← decl.withReplaceVars pure
    let value ← withReader (.andL decl body :: ·) do go inMain value
    let body ← withReader (.andR decl body :: ·) do go inMain body
    return .and decl value body
  | or inl inr => do
    -- We should think about how to name the goals so that it helps the user.
    let inl ← withReader (.orL inr :: ·) do go inMain inl
    let inr ← withReader (.orR inl :: ·) do go inMain inr
    return .or inl inr
  | haveB decl value body hidden => do
    let value ← value.replaceVars
    decl.withReplaceVars (hidden := hidden) fun decl => do
      let body ← withReader (.haveB decl value hidden :: ·) do go inMain body
      return .haveB decl value body hidden
  | savedBox saved body => do
    let saved ← go false saved
    let body ← withReader (.savedBox saved :: ·) <| go inMain body
    return savedBox saved body

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
      | .const ``letFun _ =>
        if e.getAppNumArgs = 4 then
          let f := e.appArg!
          let v := e.appFn!.appArg!
          return .visit (f.betaRev #[v])
        return .continue
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
            let mut i := 0
            repeat
              if h : fvars.size ≤ i then
                mvarId.assign <| (← mvarIdPending.getDecl).lctx.mkLambda fvars (← instantiateMVars (.mvar mvarIdPending))
                break
              else
              let fvar := fvars[i]
              let some arg := allArgs[i]? |
                mkNewAnd fvars i mvarId mvarIdPending origin
                break
              if arg.hasLooseBVars then
                mkNewAnd fvars i mvarId mvarIdPending origin
                break
              unless arg.isFVar do
                let fvarDecl ← getFVarLocalDecl fvar
                modify (· %.newHaves (·.push (fvarDecl, arg, origin)))
              i := i + 1
            return .continue -- .visit (← instantiateMVars e)
        else
          unless (← get).newMVars.contains mvarId do
            modify (· %.newMVarsArr (·.push mvarId))
          modify (· %.newMVars (·.alter mvarId fun | none => some {origin} | some origins => origins.insert origin))
          return .continue
      | _ => return .continue)


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
        let decl ← decl.mapM instantiateMVars
        let body ← withPathItem (.forallB decl hidden) <| go body
        return .forallB decl body hidden
      | .metaVar mvarId name type body =>
        let type ← instantiateMVars type
        let body ← withPathItem (.metaVar mvarId name type) <| go body
        return .metaVar mvarId name type body
      | .result r => return .result (← instantiateMVars r)
      | .and decl value body =>
        let decl ← decl.mapM instantiateMVars
        let value ← withPathItem (.andL decl body) <| go value
        let body ← withPathItem (.andR decl value) <| go body
        return .and decl value body
      | .or inl inr =>
        let inl ← withPathItem (.orL inr) <| go inl
        let inr ← withPathItem (.orR inl) <| go inr
        return .or inl inr
      | .haveB decl value body hidden =>
        let decl ← decl.mapM instantiateMVars
        let value ← instantiateMVars value
        let body ← withPathItem (.haveB decl value hidden) <| go body
        return .haveB decl value body hidden
      | .savedBox saved box =>
        let box ← withPathItem (.savedBox saved) <| go box
        return .savedBox saved box)

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
        let decl ← decl.mapM instantiateMVars
        let value := .result (← instantiateMVars (.mvar mvarId))
        let value ← mvarId.withContext do fvars.foldrM (init := value) fun fvar box =>
          return Box.forallB (← fvar.fvarId!.getDecl) box (hidden := false)
        let value ← withPathItem (.imaginaryAnd decl.fvarId) <| go value
        box := .and decl value box

    if let some haves := newHaves[address]? then
      for (decl, value) in haves do
        let decl ← decl.mapM instantiateMVars
        let value ← instantiateMVars value
        box := .haveB decl value box (hidden := false)
    return box

end FixTacticState

section SavedBox

def makeBackup (box : Box) : MetaM Box :=
  match box with
  | .forallB decl body hidden     => return .forallB decl (← makeBackup body) hidden
  | .haveB decl value body hidden => return .haveB decl value (← makeBackup body) hidden
  | .savedBox saved body          => return .savedBox saved (← makeBackup body)
  | .result _                     => throwError "couldn't make a back-up"
  | _ => return .savedBox box box


partial def Zipper.zipUntilBackup (zipper : Zipper) (skip : Nat := 0) : Zipper × Option Box :=
  if let some (item, zipper) := zipper.up then
    if let .savedBox saved := item.item then
      match skip with
      | 0      => (zipper, saved)
      | skip+1 => zipper.zipUntilBackup skip
    else
      zipper.zipUntilBackup skip
  else
    (zipper, none)

def mkNewLocalDecl (name : Name) (type : Expr) : MetaM LocalDecl := do
  let fvarId ← mkFreshFVarId
  return LocalDecl.cdecl default fvarId name type .default .default


theorem Classical_ite (q : Prop) (p : Prop) (caseFalse : ¬ p → q) (caseTrue : p → q) : q := by
  by_cases h : p <;> simp [*]

def useBackup (box : Box) (address : List PathItem) (hypName : Name) : MetaM Box := do
  let zipper ← Zipper.unzip box address
  let .metaVar mvarId _ type box := zipper.cursor | throwError "expected a meta variable box: {← box.show}"
  let decl ← mkNewLocalDecl hypName type
  mvarId.assign decl.toExpr
  let box ← box.mapM instantiateMVars
  let (zipper, some boxFalse) := { zipper with cursor := box }.zipUntilBackup 0 | throwError "couldn't find a saved state to backup to"
  zipper.withLCtx do withExistingLocalDecls [decl] do
  -- let boxType ← zipper.withLCtx do withExistingLocalDecls [decl] do inferType boxTrue
  let boxFalse := .forallB (← mkNewLocalDecl hypName (mkNot type)) boxFalse (hidden := false)
  let boxTrue := .forallB decl zipper.cursor (hidden := false)
  let caseFalse ← mkNewLocalDecl `caseFalse (← boxFalse.inferType)
  let caseTrue  ← mkNewLocalDecl `caseTrue  (← boxTrue.inferType)
  let proof := mkApp4 (.const ``Classical_ite []) (← inferType zipper.cursor) type caseFalse.toExpr caseTrue.toExpr
  let box : Box :=
    .and caseFalse boxFalse <|
    .and caseTrue boxTrue <|
    .result proof
  return { zipper with cursor := box }.zip

end SavedBox

section Obtain

def telescopeAux (name : Name) (hide : Bool) (k : LocalDecl → Box → MetaM Box) : Box → OptionT MetaM Box
  | .forallB decl body hidden => do
    if hidden then
      return .forallB decl (← telescopeAux name hide k body) hidden
    else
      withExistingLocalDecls [decl] do
      if decl.userName == name then
        let body' ← k decl body
        return .forallB decl body' (hidden := hide)
      else
        return .forallB decl (← telescopeAux name hide k body) hidden
  | .metaVar mvarId name type body =>
    return .metaVar mvarId name type (← telescopeAux name hide k body)
  | .result _ => failure
  | .and decl value body => do
    match ← OptionT.run <| telescopeAux name hide k value with
    | some value' => return .and decl value' body
    | none => withExistingLocalDecls [decl] do
      return .and decl value (← telescopeAux name hide k body)
  | .or inl inr => do
    match ← OptionT.run <| telescopeAux name hide k inl with
    | some inl' => return .or inl' inr
    | none => return .or inl (← telescopeAux name hide k inr)
  | .haveB decl value body hidden =>
    if hidden then
      return .haveB decl value (← telescopeAux name hide k body) hidden
    else
      withExistingLocalDecls [decl] do
      if decl.userName == name then
        let body' ← k decl body
        return .haveB decl value body' (hidden := hide)
      else
        return .haveB decl value (← telescopeAux name hide k body) hidden
  | .savedBox saved body =>
    return .savedBox saved (← telescopeAux name hide k body)

def telescope (b : Box) (name : Name) (hide : Bool) (k : LocalDecl → Box → MetaM Box) : MetaM Box := do
  match ← b.telescopeAux name hide k |>.run with
  | some b => return b
  | none => throwError "unknown variable '{name}' in box"


section Replace

def replaceFVarInExpr (e : Expr) (var : Expr) (subst : Expr) : Expr :=
  e.abstract #[var] |>.instantiate1 subst

def replaceFVarInLocalDecl (decl : LocalDecl) (var : Expr) (subst : Expr) : LocalDecl :=
  match decl with
  | .cdecl index fvarId userName type bi kind => .cdecl index fvarId userName (replaceFVarInExpr type var subst) bi kind
  | .ldecl index fvarId userName type value nonDep kind => .ldecl index fvarId userName (replaceFVarInExpr type var subst) (replaceFVarInExpr value var subst) nonDep kind

def replaceFVar (b : Box) (var : Expr) (subst : Expr) : Box :=
  match b with
  | forallB decl body hidden => forallB (replaceFVarInLocalDecl decl var subst) (body.replaceFVar var subst) hidden
  | metaVar mvarId name type body => metaVar mvarId name (replaceFVarInExpr type var subst) (body.replaceFVar var subst)
  | result r => result r
  | and decl value body => and (replaceFVarInLocalDecl decl var subst) (value.replaceFVar var subst) (body.replaceFVar var subst)
  | or inl inr => or (inl.replaceFVar var subst) (inr.replaceFVar var subst)
  | haveB decl value body hidden => haveB (replaceFVarInLocalDecl decl var subst) (replaceFVarInExpr value var subst) (body.replaceFVar var subst) hidden
  | savedBox saved body => savedBox saved (body.replaceFVar var subst)

end Replace

open Qq in
def obtainExists (aName pName : Name) (decl : LocalDecl) (b : Box) : MetaM Box := do
  let ⟨1, ~q(Prop), ~q(@Exists $α $p)⟩ ← inferTypeQ decl.type
    | throwError "expected `∃ a, p a`, not {decl.type}"
  withLocalDeclDQ aName α fun a => do
  withLocalDeclDQ pName q($p $a) fun p' => do
  have subst := q(Exists.intro $a $p')
  let motive ← b.inferType
  let b := b.replaceFVar decl.toExpr subst
  let b := forallB (← p'.fvarId!.getDecl) b (hidden := false)
  let b := forallB (← a.fvarId!.getDecl) b (hidden := false)
  have motive : Q(Exists $p → Prop) := ← mkLambdaFVars #[decl.toExpr] motive
  have hVar : Q(Exists $p) := decl.toExpr
  withLocalDeclDQ `intro q(∀ w : $α, ∀ h : $p w, $motive (Exists.intro w h)) fun intro => do
  let result : Q($motive $hVar) := q(Exists.casesOn (motive := $motive) $hVar $intro)
  return and (← intro.fvarId!.getDecl) b <| .result result

def obtainExistsAt (h a p : Name) (b : Box) : MetaM Box := do
  b.telescope h true (obtainExists a p)

end Obtain

section Clear

def clear (h : Name) (b : Box) : MetaM Box := do
  b.telescope h true (fun _ => pure)

end Clear

section RunTactic

open Elab Parser Tactic

declare_syntax_cat box_tactic

syntax (name := lean_tactic) tactic : box_tactic
syntax "backup" : box_tactic
syntax "admit_goal" ident (num)? : box_tactic
syntax "box_obtain" ident ident ":=" ident : box_tactic
syntax "box_clear" ident : box_tactic
syntax "set_goal" ident : box_tactic

@[inline] def boxTacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `box_tactic rbp

def boxTacticSeq1Indented : Parser := leading_parser
  sepBy1IndentSemicolon boxTacticParser

def boxTacticSeq := leading_parser
  ppIndent (boxTacticSeq1Indented)

syntax (name := box_proof) "box_proof" ppLine boxTacticSeq : tactic

def createProofBox (mvarId : MVarId) : MetaM (Array Expr × Box × MVarId) := do
  let { userName, type, kind, .. } ← mvarId.getDecl
  let mvar' ← mkFreshExprMVar type kind userName
  let mut box : Box := .metaVar mvar'.mvarId! userName type (.result mvar')
  let lctxArr := (← mvarId.getDecl).lctx.decls.toArray.filterMap id |>.filter (!·.isAuxDecl)
  for decl in lctxArr.reverse do -- reversing to add in the right order
    box := .forallB decl box (hidden := false)
  return (lctxArr.map LocalDecl.toExpr, box, mvar'.mvarId!)


def runBoxTactic (tactic : TSyntax `box_tactic) : BoxM Unit := do
  match tactic with
  | `(box_tactic| backup) =>
    let { box, .. } ← get
    let box ← makeBackup box
    modify ({ · with box })
  | `(box_tactic| admit_goal $h $[$n]?) =>
    let n := n.elim 0 (·.getNat)
    let h := h.getId
    let some goal := (← getGoals)[n]? | throwError "index {n} is out of bounds"
    let { box, addresses, .. } ← get
    let box ← useBackup box addresses[goal]! h
    modify ({ · with box })
  | `(box_tactic| box_obtain $a $p := $h) =>
    let box ← obtainExistsAt h.getId a.getId p.getId (← get).box
    modify ({ · with box })
  | `(box_tactic| box_clear $h) =>
    let box ← clear h.getId (← get).box
    modify ({ · with box })
  | `(box_tactic| $tactic:tactic) =>
    let focus := (← get).focus
    let goalsBefore ← getGoals
    let goalsBefore :=
      if goalsBefore.contains focus then
        (focus :: goalsBefore.filter (· != focus))
      else
        goalsBefore
    setGoals goalsBefore
    evalTactic tactic
    let _goalsAfter ← getGoals
    let { box, addresses, .. } ← get
    trace[box_proof] "after tactic: {← box.show}"
    let box ← updateBox box goalsBefore addresses
    modify ({ · with box })
  | `(box_tactic| set_goal $h) =>
    let some focus_ := (← getMCtx).findUserName? h.getId | throwError "no goal with user name {h}"
    modify ({ · with focus := focus_ })
  | _ => throwUnsupportedSyntax

@[inline] def mapTacticM {m} [MonadControlT TacticM m] [Monad m] (f : forall {α}, TacticM α → TacticM α) {α} (x : m α) : m α :=
  controlAt TacticM fun runInBase => f <| runInBase x

@[inline] def withTacticInfoContext' {m α} [Monad m] [MonadControlT TacticM m] (stx : Syntax) (x : m α) : m α := do
  mapTacticM (fun x => withTacticInfoContext stx x) x

def boxLoop (start : Syntax) (tactics : Syntax.TSepArray `box_tactic "") : ExceptT Expr BoxM Unit := do
  withRef start createTacticState
  tactics.getElems.forM fun (tactic : TSyntax `box_tactic) =>
    withRef tactic do withTacticInfoContext' tactic do
      runBoxTactic tactic
      trace[box_proof] "after update: {← (← get).box.show}"
      createTacticState

@[tactic box_proof]
def boxProofElab : Tactic
  | `(tactic| box_proof%$start $tactics*) => withMainContext do
    unless (← getGoals).length == 1 do
      logWarning "Box proofs are meant to be initialized when there is just one goal."
    let mainGoal ← getMainGoal
    let (lctxArr, box, focus_) ← createProofBox mainGoal
    BoxM.run box focus_ do
    withLCtx {} {} do

    match ← boxLoop start tactics with
    | .error proof =>
      trace[box_proof]"proof term{indentExpr proof}"
      mainGoal.assign (mkAppN proof lctxArr)
      -- mainGoal.withContext <| logInfo m!"Done, with proof term {indentExpr proof}"
    | .ok _ =>
      trace[box_proof]"unfinished box: {← (← get).box.show}"
      throwError "Box proof is not finished"--\n{← box.show}"
  | _ => throwUnsupportedSyntax

end RunTactic

-- set_option trace.box_proof true

section Test

example (h : ∃ a : Nat, a +1 = a*2) : ∃ b : Nat, b * 2 = b + 1 := by
  box_proof
    constructor
    have := trivial
    box_obtain a h := h
    box_clear this
    on_goal 2 => exact a
    symm
    exact h


example (g : 1 = 1) (h : 3 = 2 + 1) : (2 + 1) = 3 := by
  skip
  box_proof
    rw [← h]

example (n m k : Nat) (h: n = m) (h' : m = k) : n = k ∧ n = k := by
  box_proof
    constructor
    have x : 1 = 1 := rfl
    rw [← h] at h'
    rw [h']
    exact h'

example (x y : Int) : True ∧ ∀ a b c : Nat, a = b → a = c → b = c := by
  box_proof
    backup
    admit_goal h 0
    skip
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

example (p : Prop) (h : ¬ p → p) : p := by
  box_proof
    backup
    apply h
    admit_goal h'
    rw [Classical.not_not] at h'
    exact h'



example (a b c : Prop) (ha : a) (hb : b) (h : a → b → c) : c := by
  box_proof
    apply h
    exact hb
    exact ha


example (a b c : Prop) (h1 : a → c) (h2 : b → c) (h3 : ¬a → ¬b → c) : c := by
  box_proof
    backup
    apply h1
    admit_goal ha
    backup
    apply h2
    admit_goal hb
    apply h3
    exact hb
    exact ha


end Test

end Box

end HumanProof
