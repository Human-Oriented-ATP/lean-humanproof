import Lean
import ProofWidgets

namespace HumanProof

open Lean Meta ProofWidgets

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


initialize registerTraceClass `box_proof

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
| savedBox (saved body : Box)
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
  | savedBox _ body => return m! "Some saved box\n{← body.show}"

section Map

@[specialize]
def _root_.Lean.LocalDecl.mapM {m} [Monad m] (f : Expr → m Expr) : LocalDecl → m LocalDecl
  | .cdecl index fvarId userName type bi kind           => return .cdecl index fvarId userName (← f type) bi kind
  | .ldecl index fvarId userName type value nonDep kind => return .ldecl index fvarId userName (← f type) (← f value) nonDep kind

@[specialize]
def Box.mapM {m} [Monad m] (f : Expr → m Expr) : Box → m Box
| .forallB decl body hidden => do
  let decl ← decl.mapM f
  let body ← body.mapM f
  return .forallB decl body hidden
| .metaVar mvarId name type body => do
  let type ← f type
  let body ← body.mapM f
  return .metaVar mvarId name type body
| .result r => return .result (← f r)
| .and decl value body => do
  let decl ← decl.mapM f
  let value ← value.mapM f
  let body ← body.mapM f
  return .and decl value body
| .or inl inr => do
  let inl ←  inl.mapM f
  let inr ←  inr.mapM f
  return .or inl inr
| .haveB decl value body => do
  let decl ← decl.mapM f
  let value ← f value
  let body ← body.mapM f
  return .haveB decl value body
| .savedBox saved box => do
  let box ←  box.mapM f
  return .savedBox saved box

end Map

namespace Box

def _root_.Lean.LocalDecl.mkLambda (decl : LocalDecl) (e : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  .lam decl.userName decl.type e decl.binderInfo

def _root_.Lean.LocalDecl.mkForall (decl : LocalDecl) (e : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  .forallE decl.userName decl.type e decl.binderInfo

def _root_.Lean.LocalDecl.mkLet (decl : LocalDecl) (e value : Expr) : Expr :=
  let e := e.abstract #[decl.toExpr]
  Lean.mkLet decl.userName decl.type value e

def inferType : Box → MetaM Expr
  | .forallB decl body _hidden =>
    withExistingLocalDecls [decl] do
    return decl.mkForall (← inferType body)
  | .metaVar _ _ _ body => inferType body
  | .result r => Meta.inferType r
  | .and decl _value body => do
    withExistingLocalDecls [decl] do
      inferType body
  | .or inl _inr => inferType inl
  | .haveB decl value body => withExistingLocalDecls [decl] do
    let e ← inferType body
    let f := decl.mkLambda e
    let ety ← Meta.inferType e
    let α ← Meta.inferType value
    let β := decl.mkLambda ety
    let u1 ← getLevel α
    let u2 ← getLevel ety
    return mkAppN (.const ``letFun [u1, u2]) #[α, β, value, f]
  | .savedBox _ body => inferType body

open scoped Jsx Json
/-- Mirek's code -/
partial
def toHtmlMirek (box : Box) : MetaM Html :=
  singleton box
where
  singleton : Box → MetaM Html
  | box@(.and _ _ _) => do
    let items ← andItems box
    match items with
    | [] => return .text "Done"
    | [x] => return x
    | _ =>
      return .element "ol" #[]
        (items.toArray.map (<li>{·}</li>))
  | box => do
    let items ← ctxItems box
    match items with
    | [] => return .text "Done"
    | [x] => return x
    | _ =>
      return .element "ul" #[]
        (items.toArray.map (<li>{·}</li>))
  ctxItems : Box → MetaM (List Html)
  | .forallB decl box hidden? => do
    if hidden? then
      ctxItems box
    else withExistingLocalDecls [decl] do
      let displayName : Html := <span «class»="font-code goal-hyp"><b>{.text decl.userName.toString}</b></span>
      let displayType : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged decl.type} />
      let item := <span>{displayName} : {displayType}</span>
      return item :: (← ctxItems box)
  | .metaVar _mvarId name type box => do
    let displayType := <InteractiveCode fmt={← Lean.Widget.ppExprTagged type} />
    let item := <div>
        <span «class»=".font-code goal-goals">Goal {.text name.toString}</span>
        <span «class»=".font-code goal-vdash"><b> ⊢ </b></span>
        <span>{displayType}</span>
      </div>
      return item :: (← ctxItems box)
  | .haveB decl value box => withExistingLocalDecls [decl] do
    let displayName : Html := <span «class»="font-code goal-hyp"><b>{.text decl.userName.toString}</b></span>
    let displayType : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged decl.type} />
    let displayValue : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged value} />
    let item := <span>{displayName} : {displayType} := {displayValue}</span>
    return item :: (← ctxItems box)
  | .result _ => do return []
  | box@(.and _ _ _) => return [← singleton box]
  | .or _ _ => throwError "What? We don't use Or, or? ..."
  | .savedBox _ box => ctxItems box
  andItems : Box → MetaM (List Html)
  | .and _declName value body => do
    let value ← andItems value
    let body ← andItems body
    return value ++ body
  | .result _ => do return []
  | .savedBox _ box => ctxItems box
  | x => return [← singleton x]

/-- Anand's code -/
def toHtmlList : Box → MetaM (List Html)
  | .forallB decl box hidden? => do
    if hidden? then
      toHtmlList box
    else withExistingLocalDecls [decl] do
      let displayName : Html := <span «class»="font-code goal-hyp"><b>{.text decl.userName.toString}</b></span>
      let displayType : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged decl.type} />
      let item := <span>{displayName} : {displayType}</span>
      return item :: <br /> :: (← toHtmlList box)
  | .metaVar _mvarId name type box => do
    let displayType := <InteractiveCode fmt={← Lean.Widget.ppExprTagged type} />
    let item := <div>
        <span «class»=".font-code goal-goals">Goal {.text name.toString}</span>
        <span «class»=".font-code goal-vdash"><b> ⊢ </b></span>
        <span>{displayType}</span>
      </div>
    return item :: <br /> :: (← toHtmlList box)
  | .haveB decl value box => withExistingLocalDecls [decl] do
    let displayName : Html := <span «class»="font-code goal-hyp"><b>{.text decl.userName.toString}</b></span>
    let displayType : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged decl.type} />
    let displayValue : Html := <InteractiveCode fmt={← Lean.Widget.ppExprTagged value} />
    let item := <span>{displayName} : {displayType} := {displayValue}</span>
    return item :: <br /> :: (← toHtmlList box)
  | .result _ => return []
  | .and decl value box => do
    let displayName : Html := <span «class»="font-code goal-hyp"><b>{.text decl.userName.toString}</b></span>
    let displayType : Html := <InteractiveCode fmt={← withOptions (·.setNat `pp.deepTerms.threshold 2) <| Lean.Widget.ppExprTagged decl.type} />
    let summary : Html := <summary>{displayName} : {displayType}</summary>
    let value : Html := .element "details" #[("open", true)] (summary :: (← toHtmlList value)).toArray
    withExistingLocalDecls [decl] do
      return value :: <br /> :: (← toHtmlList box)
  | .or left right => do
    let left : Html := .element "details" #[] (← toHtmlList left).toArray
    let right : Html := .element "details" #[] (← toHtmlList right).toArray
    let container : Html := .element "div"
      #[("style", .str "display: flex; gap: 1em;")]
      #[left, right]
    return [container]
  | .savedBox _ box => toHtmlList box

def renderWidget (stx : Syntax) (box : Box) : MetaM Unit := do
  let boxDisplayMirek : Html := .element "details" #[("open", true)]
    #[<summary>Mirek infoview</summary>, ← box.toHtmlMirek]
  Widget.savePanelWidgetInfo (hash HtmlDisplay.javascript)
    (return json% { html: $(← Server.rpcEncode boxDisplayMirek ) })
    stx
  let boxDisplayAnand : Html := .element "details" #[("open", true)]
    (<summary>Anand infoview</summary> :: (← box.toHtmlList)).toArray
  Widget.savePanelWidgetInfo (hash HtmlDisplay.javascript)
    (return json% { html: $(← Server.rpcEncode boxDisplayAnand ) })
    stx

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
      let ety ← Meta.inferType e
      let α ← Meta.inferType value
      let β := decl.mkLambda ety
      let u1 ← getLevel α
      let u2 ← getLevel ety
      return mkAppN (.const ``letFun [u1, u2]) #[α, β, value, f]
  | .savedBox _ body => go body

def getResult (box : Box) : MetaM (Option Expr) := do
  let results ← box.getResults
  if h : results.size ≠ 0 then
    return results[0]
  else
    return none

section Zipper

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
  | savedBox (saved : Box)

def PathItem.toMessageData : PathItem → MessageData
  | forallB decl _hidden => m!"forallB {decl.userName} : {decl.type}"
  | metaVar _mvarId _name type => m!"metaVar {type}"
  | andL _decl _body => m!"andL"
  | andR decl _value => m!"andR {decl.type}"
  | imaginaryAnd fvarId => m!"imaginary and for {mkFVar fvarId}"
  | orL _inr => m!"orL"
  | orR _inl => m!"orR"
  | haveB decl value => m!"haveB {decl.userName} : {decl.type}, value: {value}"
  | savedBox _ => "some saved box"

instance : ToMessageData PathItem := ⟨PathItem.toMessageData⟩

instance : BEq PathItem where
  beq
    | .forallB ..  => (· matches .forallB ..)
    | .metaVar ..  => (· matches .metaVar ..)
    | .andL ..     => (· matches .andL ..)
    | .andR ..     => (· matches .andR ..)
    | .orL ..      => (· matches .orL ..)
    | .orR ..      => (· matches .orR ..)
    | .haveB ..    => (· matches .haveB ..)
    | .savedBox .. => (· matches .savedBox ..)
    | .imaginaryAnd fvarId => fun
      | .imaginaryAnd fvarId' => fvarId == fvarId'
      | _ => false

instance : Hashable PathItem where
  hash
    | .forallB ..  => 0
    | .metaVar ..  => 1
    | .andL ..     => 2
    | .andR ..     => 3
    | .orL ..      => 4
    | .orR ..      => 5
    | .haveB ..    => 6
    | .savedBox .. => 7
    | .imaginaryAnd fvarId => hash fvarId

def PathItem.getLocalDecl? : PathItem → Option LocalDecl
| .forallB decl _ | andR decl _ | haveB decl _ => decl
| _ => none

structure ZipperItem where
  item : PathItem
  lctx : LocalContext
  localInstances : LocalInstances

abbrev ZipperPath := List ZipperItem

structure Zipper where
  path           : ZipperPath
  cursor         : Box

@[inline] def ZipperPath.getLCtxs (path : ZipperPath) : LocalContext × LocalInstances :=
  match path with
  | [] => ({}, {})
  | item :: _ => (item.lctx, item.localInstances)

@[specialize] def Zipper.withLCtx {n : Type → Type _} [MonadControlT MetaM n] [Monad n] {α : Type} (zipper : Zipper) : n α → n α :=
  let (lctx, localInstances) := zipper.path.getLCtxs
  Meta.withLCtx lctx localInstances

@[inline]
def Zipper.up (zipper : Zipper) : Option (ZipperItem × Zipper) := do
  let { cursor, path } := zipper
  let item :: path := path | none
  match item.1 with
  | .forallB decl hidden      => some (item, { path, cursor := .forallB decl cursor hidden })
  | .metaVar mvarId name type => some (item, { path, cursor := .metaVar mvarId name type cursor })
  | .andL decl body           => some (item, { path, cursor := .and decl cursor body })
  | .andR decl value          => some (item, { path, cursor := .and decl value cursor })
  | .orL inr                  => some (item, { path, cursor := .or cursor inr })
  | .orR inl                  => some (item, { path, cursor := .or inl cursor })
  | .haveB decl value         => some (item, { path, cursor := .haveB decl value cursor })
  | .savedBox saved           => some (item, { path, cursor := .savedBox saved cursor })
  | .imaginaryAnd _           => panic! "imaginary PathItems aren't real"

partial def Zipper.zip (zipper : Zipper) : Box :=
  if let some (_, zipper) := zipper.up then
    zipper.zip
  else
    zipper.cursor

def ZipperPath.extend (path : ZipperPath) (item : PathItem) : ZipperPath :=
  let (lctx, localInstance) := path.getLCtxs
  ⟨item, lctx, localInstance⟩ :: path

def Zipper.down (zipper : Zipper) (item : PathItem) : MetaM Zipper := do
  let { path, cursor } := zipper
  let withFVar (decl : LocalDecl) (pathItem : PathItem) (body : Box) : MetaM Zipper := do
    zipper.withLCtx do
      withExistingLocalDecls [decl] do
        return { path := ⟨pathItem, ← getLCtx, ← getLocalInstances⟩ :: path, cursor := body }
  let err : MetaM Zipper := throwError "Zipper down coordinate is wrong: {item}"
  match item with
  | .forallB ..      => if let .forallB decl body hidden      := cursor then withFVar decl (.forallB decl hidden) body else err
  | .metaVar ..      => if let .metaVar mvarId name type body := cursor then return { path := path.extend (.metaVar mvarId name type), cursor := body } else err
  | .andL ..         => if let .and decl value body           := cursor then return { path := path.extend (.andL decl body), cursor := value } else err
  | .andR ..         => if let .and decl value body           := cursor then withFVar decl (.andR decl value) body else err
  | .orL ..          => if let .or inl inr                    := cursor then return { path := path.extend (.orL inr), cursor := inl } else err
  | .orR ..          => if let .or inl inr                    := cursor then return { path := path.extend (.orR inl), cursor := inr } else err
  | .haveB ..        => if let .haveB decl value body         := cursor then withFVar decl (.haveB decl value) body else err
  | .savedBox ..     => if let .savedBox saved body           := cursor then return { path := path.extend (.savedBox saved), cursor := body } else err
  | .imaginaryAnd .. => err
  -- | _           => throwError "Zipper down coordinate is wrong: {item}"


def Zipper.unzip (box : Box) (address : List PathItem) : MetaM Zipper := do
  go { path := [], cursor := box } address
where
  go (zipper : Zipper) (address : List PathItem) : MetaM Zipper := do
    let coord :: address := address | return zipper
    let zipper ← zipper.down coord
    go zipper address

end Zipper

end Box

end HumanProof
