import HumanProof.Basic
import ProofWidgets
import Lean

open Lean Meta ProofWidgets Server

namespace HumanProof

namespace Display


structure TreeLine where
  isFocused : Bool
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

def Tree.ofBox (box : Box) (focusedGoal : MVarId) : Tree :=
  aux box []
where aux (box : Box) : ReaderM (List LocalDecl) Tree := do
match box with
| .forallB decl body hidden =>
  withReader (flip List.concat decl) do
    if hidden then aux body
    else
      let line : TreeLine := {
        isFocused := false, isGoal := false, name := decl.userName, type := decl.type, ctx := ← read }
      let tree ← aux body
      if tree.isEmpty then return tree
      else return ⟨(line::tree.lines), tree.subtrees⟩
| .metaVar mvarId name type body =>
  let line : TreeLine := {
    isFocused := mvarId == focusedGoal, isGoal := true, name := name, type := type, ctx := ← read }
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
        isFocused := false, isGoal := false, name := decl.userName, type := decl.type,
        value? := value, ctx := ← read }
      let tree ← aux body
      if tree.isEmpty then return tree
      else return ⟨(line::tree.lines), tree.subtrees⟩
| .savedBox _ body => aux body

open Jsx in
def TreeLine.toHtml (tl : TreeLine) : MetaM Html := withExistingLocalDecls tl.ctx do
  let tlIsProp ← isProp tl.type
  let displayType := <InteractiveCode fmt={← Lean.Widget.ppExprTagged tl.type} />
  let nameStyle : String := if tl.isGoal then "goal-goals" else "goal-hyp"
  let nameString : String := if tl.name.isAnonymous then "_" else tl.name.toString
  let pref : String := if tl.isGoal then
    if tlIsProp then
        s!"{if tl.isFocused then "» " else ""}Goal "
    else "?"
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

def treeViewStyle : Html := .element "style" #[] #[.text "
  details.tree-view{margin-bottom:0.1em; margin-left:1.25rem}
  details.tree-view>summary{cursor:pointer;display:block;position:relative;padding-top: 0.2em;outline:none;-webkit-tap-highlight-color:transparent}
  details.tree-view>summary::before{content:'';border:solid transparent;border-left:solid;border-width:.3em 0 .3em .5em;position:absolute;top:.5em;left:-1.25rem;transform:translateX(15%)}
  details.tree-view[open]>summary::before{border:solid transparent;border-top:solid;border-width:.5em .3em 0}
  details.tree-view>summary::after{content:'';width:1.25rem;height:1em;position:absolute;top:.3em;left:-1.25rem}"]

open Jsx in
partial
def Tree.toHtml (tree : Tree) : MetaM Html := do
  let htmls ← toHtmlList tree
  let htmlInner := .element "div" #[] (treeViewStyle :: htmls).toArray
  return (
    <details «open»={true}>
      <summary>Box state display</summary>
      {htmlInner}
    </details>
  )
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

end Display

def Box.toHtml (box : Box) (focusedGoal : MVarId) : MetaM Html := (Display.Tree.ofBox box focusedGoal).toHtml

structure BoxDisplayState where
  box : Box
  addresses : Std.HashMap MVarId (List Box.PathItem)
  mctx : MetavarContext
  focusedGoal : MVarId

initialize boxStateExt : EnvExtension (Option BoxDisplayState)
  ← registerEnvExtension (pure none) (asyncMode := .local)

namespace Display

open Jsx Json in
@[server_rpc_method]
def RenderBox.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let some goal := props.goals[0]? | return <span>No goals.</span>

    goal.ctx.val.runMetaM {} do
      let some ⟨box, _, mctx, focusedGoal⟩ := boxStateExt.getState (← getEnv) |
        return <span>Box proof is not initialized.</span>
      setMCtx mctx
      let display ← box.toHtml focusedGoal
      return display

@[widget_module]
def RenderBox : Component PanelWidgetProps :=
  mk_rpc_widget% RenderBox.rpc

end Display

show_panel_widgets [scoped Display.RenderBox]
