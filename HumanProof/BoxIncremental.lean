import HumanProof.Display
import HumanProof.CustomEval

open Lean Meta Elab Tactic

namespace HumanProof

def runAndUse (finish : Expr → TacticM Unit)
    (tac : ExceptT Expr TacticM (Box × Std.HashMap MVarId (List Box.PathItem))) : TacticM Unit := do
  let state? : Option BoxState ←
    match ← tac with
    | .error proof =>
      finish proof
      pure none
    | .ok ⟨box, addresses⟩ => pure <| some ⟨box, addresses, ← getMCtx⟩
  modifyEnv (boxStateExt.setState · state?)

-- **WARNING** Shady idea: modify the `SourceInfo` of the `Syntax` to extend beyond the actual range
-- This might potentially allow box states to be displayed at the end of a tactic block
def Lean.Syntax.extendSourceInfo (stx : Syntax) : MetaM Syntax := sorry

def boxStepi (finish : Expr → TacticM Unit)
    (tactic : Syntax) : TacticM Unit := do
  match boxStateExt.getState (← getEnv) with
  | none => logWarning "redundant tactic, all goals are finished"
  | some ⟨box, addresses, _⟩ =>
    withRef tactic do withTacticInfoContext tactic do
    -- box.renderWidget tactic
    let box ← Box.runBoxTactic box (TSyntax.mk tactic) addresses
    trace[box_proof] "after update: {← box.show}"
    runAndUse finish (Box.createTacticState box)

scoped syntax (name := box_proofi) "box_proofi" ppLine colGe Box.boxTacticSeq : tactic

open Lean Elab Meta Tactic

@[tactic box_proofi, incremental]
def boxProofiElab : Tactic := fun start => do
  if (← Lean.Elab.Tactic.getGoals).length > 1 then
    logWarning "Box proofs are meant to be initialized when there is just one goal."
  let mainGoal ← Lean.Elab.Tactic.getMainGoal
  let (lctxArr, box) ← Box.createProofBox mainGoal
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

  runAndUse finishProof (withRef start (Box.createTacticState box))
  Term.withNarrowedArgTacticReuse 1 (
    Term.withNarrowedArgTacticReuse 0 (
      Term.withNarrowedArgTacticReuse 0 (
        (customEvalSepTactics (boxStepi finishProof))
      )
    )
  ) start
  finishBlock
