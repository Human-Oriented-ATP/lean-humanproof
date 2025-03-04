import Mathlib.Tactic

example (a b : ℕ) : a+b = b+a := by exact Nat.add_comm a b

open Lean Meta Parser Elab Tactic Qq

namespace ModRw

def RwRoot : Type :=
  Expr → Expr → MetaM (Option (Σ _ : Expr, Expr))

/--
Typed variant of RwRoot in order to let
Qq check our proof composition
-/
def RwRootTyped (n e : Q(ℤ)): Type :=
  MetaM (Option (Σ re : Q(ℤ), Q($e ≡ $re [ZMOD $n])))

example (rwRoot : ∀ n e, RwRootTyped n e) : RwRoot := rwRoot

partial
def rwInt
    (n : Q(ℤ))
    (rwRoot : ∀ e, RwRootTyped n e)
    (e : Q(ℤ))
    : RwRootTyped n e := do
  match ← rwRoot e with
  | some x => return x
  | none =>
    match e with
    | ~q($a + $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar + $br), q(Int.ModEq.add $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar + $b), q(Int.ModEq.add_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a + $br), q(Int.ModEq.add_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a - $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar - $br), q(Int.ModEq.sub $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar - $b), q(Int.ModEq.sub_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a - $br), q(Int.ModEq.sub_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a * $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar * $br), q(Int.ModEq.mul $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar * $b), q(Int.ModEq.mul_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a * $br), q(Int.ModEq.mul_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a ^ $b) =>
      match ← rwInt n rwRoot a with
      | (some ⟨ar, apf⟩) =>
        return some ⟨q($ar ^ $b), q(Int.ModEq.pow $b $apf)⟩
      | none =>
        return none
    | ~q(-$a) =>
      match ← rwInt n rwRoot a with
      | (some ⟨ar, apf⟩) =>
        return some ⟨q(-$ar), q(Int.ModEq.neg $apf)⟩
      | none =>
        return none
    | _ => return none

def rwZModEq (n a b : Q(ℤ))
    (rwRoot : ∀ e, RwRootTyped n e) :
    MetaM (Option (Σ eq2 : Q(Prop), Q(($a ≡ $b [ZMOD $n]) = $eq2))) := do
  match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
  | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
    return some ⟨q($ar ≡ $br [ZMOD $n]), q(propext <| Eq.congr $apf $bpf)⟩
  | (some ⟨ar, apf⟩, none) =>
    return some ⟨q($ar ≡ $b [ZMOD $n]), q(propext <| Eq.congr_left $apf)⟩
  | (none, some ⟨br, bpf⟩) =>
    return some ⟨q($a ≡ $br [ZMOD $n]), q(propext <| Eq.congr_right $bpf)⟩
  | (none, none) =>
    return none

def rwRootBasic (n₀ a₀ b₀ : Q(ℤ)) (pf : Q($a₀ ≡ $b₀ [ZMOD $n₀]))
    : RwRoot :=
  fun n a => do
    if n == n₀ ∧ a == a₀ then
      return some ⟨b₀, pf⟩
    else
      return none

def rwRootAdvanced (eqn : Expr) (discharger : TSyntax ``discharger) : RwRoot := fun n e => do
  let thm ← inferType eqn -- the statement that `eqn` proves
  let (mvars, _, body) ← forallMetaTelescope thm -- the body of the statement
  let ⟨1, ~q(Prop), ~q($lhs ≡ $rhs [ZMOD $n'])⟩ ← inferTypeQ body | throwError "Expected the equation to be of the form lhs ≡ rhs [ZMOD $mod]"
  match ← isDefEqQ (u := 1) n n', ← isDefEqQ (u := 1) lhs e with
  | .defEq _, .defEq _ =>
    for mvar in mvars do
      let mvarId := mvar.mvarId!
      unless ← mvarId.isAssigned do
        let ⟨[], _⟩ ← Elab.runTactic mvarId discharger | throwError "Goal {mvarId} not closed by discharger."
    return some ⟨rhs, mkAppN eqn (← mvars.mapM instantiateMVars)⟩
  | _, _ => return none

def rwTopStep
  (rw_root : ∀ n e : Q(ℤ), MetaM (Option (Σ re : Q(ℤ), Q($e ≡ $re [ZMOD $n]))))
  : Simp.Simproc := fun e => do
  let e_whnf ← whnfR e
  if let some (n,a,b) := e_whnf.app3? `Int.ModEq then
    match ← rwZModEq n a b (rw_root n) with
    | some ⟨eq2, pf⟩ => return Simp.Step.done { expr := eq2, proof? := pf }
    | none => return Simp.Step.done { expr := e, proof? := none }
  else
    return Simp.Step.continue

def SimpConfig : Simp.Config where
  zeta := false
  proj := false

def rwTop
  (rwRoot : ∀ n e : Q(ℤ), RwRootTyped n e)
  (tgt : Expr)
  : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext SimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := { pre := rwTopStep rwRoot }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

def rwModTarget (rwRoot : ∀ n e, RwRootTyped n e) :
    TacticM Unit := do
  let mvarId ← getMainGoal
  let tgt ← instantiateMVars (← mvarId.getType)
  let mvarIdNew ← applySimpResultToTarget mvarId tgt (← rwTop rwRoot tgt)
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

def rwModLocalDecl (rwRoot : ∀ n e, RwRootTyped n e) (fvarId : FVarId) :
    TacticM Unit := do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let mvarId ← getMainGoal
  let result ← rwTop rwRoot tgt
  let some (_, mvarIdNew) ← applySimpResultToLocalDecl mvarId fvarId result False | failure
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

elab "rw_mod " d?:(discharger)? t:term loc?:(location)? : tactic =>
  withMainContext do
    let d : TSyntax ``discharger := (d?.getD (← `(discharger| (disch := assumption))))
    let loc := match loc? with
    | some loc => expandLocation loc
    | none => Location.targets #[] true
    let pf ← elabTerm t none
    let rwRoot := rwRootAdvanced pf d
    -- let rwRoot ← match t.app3? `Int.ModEq with
    -- | some (n,a,b) => pure <| (rwRootBasic n a b pf)
    -- | none => throwError "mod_rw must be provided with a proof of a statement of the form a ≡ b [ZMOD n]"
    withLocation loc
      (rwModLocalDecl rwRoot)
      (rwModTarget rwRoot)
      (fun _ ↦ logInfo "push_neg couldn't find a negation to push")

example (a b c d n : ℤ) (h : b + c * d ≡ d + b * b [ZMOD n])
(eq : a ≡ b [ZMOD n])
: a + c * d ≡ d + a * a [ZMOD n]
:= by
  rw_mod eq
  rw_mod h
  rfl

example (a b c d n : ℤ) (h : b + c * d ≡ d + b * b [ZMOD n])
(eq : a ≡ b [ZMOD n])
: a + c * d ≡ d + a * a [ZMOD n]
:= by
  rw_mod eq.symm at h
  exact h

end ModRw
