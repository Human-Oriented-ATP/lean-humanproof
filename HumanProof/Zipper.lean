import HumanProof.Basic



structure Zipper where
  path           : List PathItem
  cursor         : Box
  lctx           : LocalContext
  localInstances : LocalInstances
  mctx           : MetavarContext

inductive Coord where
  | forallB | metaVar | andL | andR | orL | orR | haveB
  deriving Repr, BEq


def Zipper.up (zipper : Zipper) : Option Zipper := do
  let item :: path := zipper.path | failure
  let { cursor, .. } := zipper
  let zipper := { zipper with path }
  match item with
  | .forallB decl hidden =>
    return { zipper with
      cursor := .forallB decl cursor hidden
      lctx   := zipper.lctx.erase decl.fvarId  }
  | .metaVar mvarId name type => return { zipper with cursor := .metaVar mvarId name type cursor }
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
  | .metaVar, .metaVar mvarId name type body =>
    -- let { userName, lctx, type, localInstances, kind, .. } := decl
    return { zipper with
      path := .metaVar mvarId name type :: path
      cursor := body
      mctx := mctx.addExprMVarDeclExp mvarId name lctx localInstances type (kind := .syntheticOpaque) }
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
