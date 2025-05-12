import HumanProof.BoxIncremental

elab "echo " s:str : tactic => Lean.logInfo s

open HumanProof

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

theorem box_incremental_example (p : Prop) (h : ¬ p → p) : p := by
  box_proofi
    backup
    apply h
    sleep 1000
    sleep 1000
    sleep 1000
    admit_goal h'
    echo "hi"
    rw [Classical.not_not] at h'
    have : True ∧ True := by
      constructor
      · sleep 1000
        echo "hi there"
        sleep 1000
        trivial
      · sleep 1000
        echo "well, I am still here"
        trivial
    exact h'
