import HumanProof.BoxIncremental

elab "echo " s:str : tactic => Lean.logInfo s

example (x y : Int) : True ∧ ∀ a b c : Nat, a = b → a = c → b = c := by
  box_proofi
    backup
    admit_goal h 0
    skip
    constructor
    skip
    sleep 1000
    intro a
    skip
    intro b
    intro c
    sleep 1000
    intro h
    intro g
    rw [h] at g
    exact g
    trivial
  qed

example (p : Prop) (h : ¬ p → p) : p := by
  box_proofi
    backup
    apply h
    sleep 1000
    admit_goal h'
    echo "hi"
    rw [Classical.not_not] at h'
    exact h'
  qed
