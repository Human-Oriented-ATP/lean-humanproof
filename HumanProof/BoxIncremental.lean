import HumanProof.Basic
import HumanProof.CustomEval

open HumanProof Lean Meta Elab Tactic

def BoxState := Box × Std.HashMap MVarId (List Box.PathItem)

initialize boxStateExt : EnvExtension (Option BoxState) ← registerEnvExtension (pure none)

def runAndUse (finish : Expr → TacticM Unit)
    (tac : ExceptT Expr TacticM BoxState) : TacticM Unit := do
  let state? : Option BoxState ←
    match ← tac with
    | .error proof =>
      finish proof
      pure none
    | .ok state => pure state
  modifyEnv (boxStateExt.setState · state?)

def boxStepi (finish : Expr → TacticM Unit)
    (tactic : Syntax) : TacticM Unit := do
  match boxStateExt.getState (← getEnv) with
  | none => logWarning "redundant tactic, all goals are finished"
  | some (box, addresses) =>
    withRef tactic do withTacticInfoContext tactic do
    let box ← Box.runBoxTactic box (TSyntax.mk tactic) addresses
    trace[box_proof] "after update: {← box.show}"
    runAndUse finish (Box.createTacticState box)

syntax (name := box_proofi) "box_proofi" ppLine Box.boxTacticSeq : tactic

open Lean Elab Meta Tactic

@[tactic box_proofi, incremental]
def boxProofiElab : Tactic := fun start => do
  if (← Lean.Elab.Tactic.getGoals).length > 1 then
    logWarning "Box proofs are meant to be initialized when there is just one goal."
  let mainGoal ← Lean.Elab.Tactic.getMainGoal
  let (lctxArr, box) ← Box.createProofBox mainGoal
  let finish (proof : Expr) : TacticM Unit := do
    trace[box_proof]"proof term{indentExpr proof}"
    mainGoal.assign (mkAppN proof lctxArr)
  withLCtx {} {} do

  runAndUse finish (withRef start (Box.createTacticState box))
  Term.withNarrowedArgTacticReuse 1 (
    Term.withNarrowedArgTacticReuse 0 (
      Term.withNarrowedArgTacticReuse 0 (
        (customEvalSepTactics (boxStepi finish))
      )
    )
  ) start
