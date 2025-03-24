import Lean
import HumanProof.CustomEval

open Lean Parser Elab Meta Tactic Language

/-
Demo to show how to call customEvalSepTactics
we extend the environment with a state represented by a natural number.
And then have a custom scope which allows setting the number to a particular value,
or printing that value.
-/
syntax "get" : tactic
syntax "set " num : tactic

syntax (name := my_scope) "my_scope" ppLine tacticSeq : tactic

-- initialize myStateRef : IO.Ref Nat ← IO.mkRef 0
initialize myStateExt : EnvExtension Nat ← registerEnvExtension (pure 0)

def myEvalTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| get) =>
    let n := myStateExt.getState (← getEnv)
    liftMetaM <| logInfoAt stx m!"The current state is {n}."
  | `(tactic| set $i) =>
    let n := i.getNat
    modifyEnv (myStateExt.setState · n)
  | `(tactic| $tac) =>
    evalTactic tac

def myFinish (stx : Syntax) : TacticM Unit := do
  let n := myStateExt.getState (← getEnv)
  liftMetaM <| logInfoAt stx m!"Finished with {n}."

@[tactic my_scope, incremental]
def myScopeElab : Tactic := fun stx => do
  modifyEnv (myStateExt.setState · 42)
  Term.withNarrowedArgTacticReuse 1 (
    Term.withNarrowedArgTacticReuse 0 (
      Term.withNarrowedArgTacticReuse 0 (
        (customEvalSepTactics myEvalTactic (myFinish stx))
      )
    )
  ) stx
  modifyEnv (myStateExt.setState · 0)
