import HumanProof.Display
import HumanProof.CustomEval

open Lean Meta Elab Tactic

namespace HumanProof

def runAndUse (finish : Expr → TacticM Unit)
    (tac : ExceptT Expr Box.BoxM Unit) : Box.BoxM Unit := do
  match ← tac with
  | .error proof =>
    finish proof
    modifyEnv (boxStateExt.setState · none)
  | .ok _ =>
    let s ← get
    let mctx ← getMCtx
    modifyEnv (boxStateExt.setState · (some { s with mctx }) )

-- **WARNING** Shady idea: modify the `SourceInfo` of the `Syntax` to extend beyond the actual range
-- This might potentially allow box states to be displayed at the end of a tactic block
def Lean.Syntax.extendSourceInfo (stx : Syntax) : MetaM Syntax := sorry

def boxStepi (finish : Expr → TacticM Unit)
    (tactic : Syntax) : TacticM Unit := do
  match boxStateExt.getState (← getEnv) with
  | none => logWarning "redundant tactic, all goals are finished"
  | some s =>
    StateRefT'.run' (s := s.toBoxState) (do
      withRef tactic do Box.withTacticInfoContext' tactic do
      -- box.renderWidget tactic
      Box.runBoxTactic (TSyntax.mk tactic)
      trace[box_proof] "after update: {← (← get).box.show}"
      runAndUse finish (Box.createTacticState))

scoped syntax (name := box_proofi) "box_proofi" ppLine colGe Box.boxTacticSeq : tactic

open Lean Elab Meta Tactic

@[tactic box_proofi, incremental]
def boxProofiElab : Tactic := fun start => do
  if (← Lean.Elab.Tactic.getGoals).length > 1 then
    logWarning "Box proofs are meant to be initialized when there is just one goal."
  let mainGoal ← Lean.Elab.Tactic.getMainGoal
  let (lctxArr, box, focus_) ← Box.createProofBox mainGoal
  let finishProof (proof : Expr) : TacticM Unit := do
    trace[box_proof]"proof term{indentExpr proof}"
    mainGoal.assign (mkAppN proof lctxArr)
  let finishBlock : TacticM Unit := do
    let state := boxStateExt.getState (← getEnv)
    match state with
    | some { box, .. } =>
      trace[box_proof]"unfinished box: {← box.show}"
      -- box.renderWidget start
      throwError "Box proof is not finished"--\n{← box.show}"
    | none => pure ()

  withLCtx {} {} do
  Box.BoxM.run box focus_ do runAndUse finishProof (withRef start (Box.createTacticState))
  Term.withNarrowedArgTacticReuse 1 (
    Term.withNarrowedArgTacticReuse 0 (
      Term.withNarrowedArgTacticReuse 0 (
        (customEvalSepTactics (boxStepi finishProof))
      )
    )
  ) start
  finishBlock
