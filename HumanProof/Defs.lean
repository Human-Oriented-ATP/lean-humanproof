import Lean
import ProofWidgets
import Batteries

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
| forallB (decl : LocalDecl) (body : Box) (hidden : Bool)
| metaVar (mvarId : MVarId) (name : Name) (type : Expr) (body : Box)
| result (r : Expr)
| and (decl : LocalDecl) (value body : Box)
| or (inl : Box) (inr : Box)
| haveB (decl : LocalDecl) (value : Expr) (body : Box) (hidden : Bool)
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
  | haveB decl value body _hidden =>
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
| .haveB decl value body hidden => do
  let decl ← decl.mapM f
  let value ← f value
  let body ← body.mapM f
  return .haveB decl value body hidden
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
  | .haveB decl value body _hidden => withExistingLocalDecls [decl] do
    let e ← inferType body
    let f := decl.mkLambda e
    let ety ← Meta.inferType e
    let α ← Meta.inferType value
    let β := decl.mkLambda ety
    let u1 ← getLevel α
    let u2 ← getLevel ety
    return mkAppN (.const ``letFun [u1, u2]) #[α, β, value, f]
  | .savedBox _ body => inferType body

namespace Mirek

structure TreeLine where
  isGoal : Bool
  name : Name
  type : Expr
  value? : Option Expr := none
  ctx : List LocalDecl

structure Tree where
  lines : List TreeLine
  subtrees : List Tree

def Tree.empty : Tree := ⟨[], []⟩
def Tree.isEmpty (t : Tree) := t.lines.isEmpty && t.subtrees.isEmpty
def Tree.toSubtrees (t : Tree) : List Tree :=
  match t.lines with | [] => t.subtrees | _ => [t]

def Tree.ofBox (box : Box) : Tree :=
  aux box []
where aux (box : Box) : ReaderM (List LocalDecl) Tree := do
match box with
| .forallB decl body hidden =>
  withReader (flip List.concat decl) do
    if hidden then aux body
    else
      let line : TreeLine := {
        isGoal := false, name := decl.userName, type := decl.type, ctx := ← read }
      let tree ← aux body
      if tree.isEmpty then return tree
      else return ⟨(line::tree.lines), tree.subtrees⟩
| .metaVar _ name type body =>
  let line : TreeLine := {
    isGoal := true, name := name, type := type, ctx := ← read }
  let tree ← aux body
  return ⟨(line::tree.lines), tree.subtrees⟩
| .result _ => return .empty
| .and _ value body => do
  return match ((← aux value).toSubtrees ++ (← aux body).toSubtrees) with
  | [x] => x
  | xs => ⟨[], xs⟩
| .or _ _ => return ⟨[], []⟩
| .haveB decl value body hidden =>
  withReader (flip List.concat decl) do
    if hidden then aux body
    else
      let line : TreeLine := {
        isGoal := false, name := decl.userName, type := decl.type,
        value? := value, ctx := ← read }
      let tree ← aux body
      if tree.isEmpty then return tree
      else return ⟨(line::tree.lines), tree.subtrees⟩
| .savedBox _ body => aux body

open Jsx in
def TreeLine.toHtml (tl : TreeLine) : MetaM Html := do
withExistingLocalDecls tl.ctx do
  let tlIsProp ← isProp tl.type
  let displayType := <InteractiveCode fmt={← Lean.Widget.ppExprTagged tl.type} />
  let nameStyle : String := if tl.isGoal then "goal-goals" else "goal-hyp"
  let nameString : String := if tl.name.isAnonymous then "_" else tl.name.toString
  let pref : String := if tl.isGoal then
    if tlIsProp then "Goal " else "?"
  else ""
  let displayName : Html :=
    .element "span" #[("class", toJson (".font-code "++nameStyle))]
      #[<b>{.text (pref ++ nameString)}</b>]
  let separator : Html := if tl.isGoal && tlIsProp then
    <span «class»=".font-code goal-vdash"><b style={json%{"white-space": "pre"}}>   ⊢   </b></span>
  else
    <b style={json%{"white-space": "pre"}}>   :   </b>
  let displayValue? : Option Html ← match tl.value? with
  | none => pure none
  | some value =>
    if tlIsProp then pure none
    else
      pure <| some <InteractiveCode fmt={← Lean.Widget.ppExprTagged value} />
  let items : Array Html := #[displayName, separator, displayType]
  let items : Array Html := match displayValue? with
  | none => items
  | some displayValue => items.append
    #[<b style={json%{"white-space": "pre"}}>   :=   </b>, displayValue]
  return .element "div" #[] items

open Jsx in
partial
def Tree.toHtml (tree : Tree) : MetaM Html := do
  let htmls ← toHtmlList tree
  return .element "div" #[] htmls.toArray
where
  toHtmlList (tree : Tree) : MetaM (List Html) := do
    if tree.lines.isEmpty then
      if tree.subtrees.isEmpty then return [.text "Done"]
      let n := tree.subtrees.length
      tree.subtrees.zipIdx.mapM <| fun (subtree, i) => do
        match subtree with
        | ⟨[line], []⟩ => line.toHtml
        | _ =>
          let (first::rest) ← toHtmlList subtree | throwError "unexpected empty list"
          return .element "details"
            #[("class", "tree-view"), ("open", i+1 == n)]
            (<summary>{first}</summary>::rest).toArray
    else
      let mut displayLines ← tree.lines.mapM TreeLine.toHtml
      displayLines := displayLines
      if !tree.subtrees.isEmpty then
        let subtrees ← toHtmlList <| ⟨[], tree.subtrees⟩
        displayLines := displayLines ++ subtrees
      return displayLines

def toHtml (box : Box) : MetaM Html := (Tree.ofBox box).toHtml

open Jsx in
def treeViewStyle : Html := <style>{.text "
    details.tree-view{margin-bottom:0.1em; margin-left:1.25rem}
    details.tree-view>summary{cursor:pointer;display:block;position:relative;padding-top: 0.2em;outline:none;-webkit-tap-highlight-color:transparent}
    details.tree-view>summary::before{content:'';border:solid transparent;border-left:solid;border-width:.3em 0 .3em .5em;position:absolute;top:.5em;left:-1.25rem;transform:translateX(15%)}
    details.tree-view[open]>summary::before{border:solid transparent;border-top:solid;border-width:.5em .3em 0}
    details.tree-view>summary::after{content:'';width:1.25rem;height:1em;position:absolute;top:.3em;left:-1.25rem}"
}</style>

end Mirek

open Jsx in
/-- Anand's code -/
def toHtmlList : Box → MetaM (List Html)
  | .forallB decl box hidden => do
    if hidden then
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
  | .haveB decl value box hidden =>
    if hidden then
      toHtmlList box
    else
      withExistingLocalDecls [decl] do
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

open Jsx in
def renderWidget (stx : Syntax) (box : Box) : MetaM Unit := do
  let boxDisplayMirek : Html := .element "details" #[("open", true)] #[
    Mirek.treeViewStyle,
    <summary>Mirek infoview</summary>,
    ← Mirek.toHtml box,
    <br/>
  ]
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
  | .haveB decl value body _hidden => withExistingLocalDecls [decl] do
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
  | haveB (decl : LocalDecl) (value : Expr) (hidden : Bool)
  | savedBox (saved : Box)

def PathItem.toMessageData : PathItem → MessageData
  | forallB decl _hidden => m!"forallB {decl.userName} : {decl.type}"
  | metaVar _mvarId _name type => m!"metaVar {type}"
  | andL _decl _body => m!"andL"
  | andR decl _value => m!"andR {decl.type}"
  | imaginaryAnd fvarId => m!"imaginary and for {mkFVar fvarId}"
  | orL _inr => m!"orL"
  | orR _inl => m!"orR"
  | haveB decl value _hidden => m!"haveB {decl.userName} : {decl.type}, value: {value}"
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
| .forallB decl _ | andR decl _ | haveB decl _ _ => decl
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
  | .haveB decl value hidden  => some (item, { path, cursor := .haveB decl value cursor hidden })
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
  | .haveB ..        => if let .haveB decl value body hidden  := cursor then withFVar decl (.haveB decl value hidden) body else err
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

open ProofWidgets Jsx

#html <span style={json%{"white-space": "pre"}}>hello    :  world</span>
