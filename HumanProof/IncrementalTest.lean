import HumanProof.Incremental

elab "echo " s:str : tactic => Lean.logInfo s

-- try modifying the echo's of processed lines to see the state preserved,
-- and continuing procesing below

example : True := by
  my_scope
    sleep 1000
    echo "expect 42"
    sleep 1000
    get
    sleep 1000
    sleep 1000
    let x := 5
    set 10
    have : True ∧ True := by
      constructor
      · sleep 1000
        echo "hi there"
        sleep 1000
        trivial
      · sleep 1000
        echo "I am here"
        trivial
    set 3
    get
    trivial


example : True := by
  my_scope
    sleep 1000
    echo "expect 42"
    get
    let x := 5
    sleep 1000
    set 1
    sleep 1000
    echo "expect 1"
    get
    sleep 1000
    set 2
    sleep 1000
    echo "expect 2"
    get
    sleep 1000
    set 3
    sleep 1000
    echo "expect 3"
    get
    sleep 1000
    set 4
    sleep 1000
    echo "expect 4"
    get
    sleep 1000
    set 5
    sleep 1000
    echo "expect 5"
    get
    sleep 1000
    set 6
    sleep 1000
    echo "expect 6"
    get
    sleep 1000
    set 7
    sleep 1000
    echo "expect 7"
    get
    sleep 1000
    set 8
    sleep 1000
    echo "expect 8"
    get
    trivial
