import Lean

open Lean Parser Elab Meta Tactic Language

/-
This is a copy of Lean.Elab.Tactic.evalSepTactics from the standard library
replacing the default evalTactic with a custom function.
-/
partial def customEvalSepTactics
    (evalStep : Tactic := evalTactic) : Tactic := goEven
where
  -- `stx[0]` is the next tactic step, if any
  goEven stx := do
    if stx.getNumArgs == 0 then
      return
    let tac := stx[0]
    /-
    Each `goEven` step creates three promises under incrementality and reuses their older versions
    where possible:
    * `finished` is resolved when `tac` finishes execution; if `tac` is wholly unchanged from the
      previous version, its state is reused and `tac` execution is skipped. Note that this promise
      is never turned into a `SnapshotTask` and added to the snapshot tree as incremental reporting
      is already covered by the next two promises.
    * `inner` is passed to `tac` if it is marked as supporting incrementality and can be used for
      reporting and partial reuse inside of it; if the tactic is unsupported or `finished` is wholly
      reused, it is ignored.
    * `next` is used as the context when invoking `goOdd` and thus eventually used for the next
      `goEven` step. Thus, the incremental state of a tactic script is ultimately represented as a
      chain of `next` snapshots. Its reuse is disabled if `tac` or its following separator are
      changed in any way.
    -/
    let mut oldInner? := none
    if let some snap := (← readThe Term.Context).tacSnap? then
      if let some old := snap.old? then
        let oldParsed := old.val.get
        oldInner? := oldParsed.inner? |>.map (⟨oldParsed.stx, ·⟩)
    -- compare `stx[0]` for `finished`/`next` reuse, focus on remainder of script
    Term.withNarrowedTacticReuse (stx := stx) (fun stx => (stx[0], mkNullNode stx.getArgs[1:])) fun stxs => do
      let some snap := (← readThe Term.Context).tacSnap?
        | do evalStep tac; goOdd stxs
      let mut reusableResult? := none
      let mut oldNext? := none
      if let some old := snap.old? then
        -- `tac` must be unchanged given the narrow above; let's reuse `finished`'s state!
        let oldParsed := old.val.get
        if let some state := oldParsed.finished.get.state? then
          reusableResult? := some ((), state)
          -- only allow `next` reuse in this case
          oldNext? := oldParsed.next[0]?.map (⟨old.stx, ·⟩)

      let next ← IO.Promise.new
      let finished ← IO.Promise.new
      let inner ← IO.Promise.new
      let cancelTk? := (← readThe Core.Context).cancelTk?
      snap.new.resolve {
        desc := tac.getKind.toString
        diagnostics := .empty
        stx := tac
        inner? := some { stx? := tac, task := inner.resultD default, cancelTk? }
        finished := { stx? := tac, task := finished.resultD default, cancelTk? }
        next := #[{ stx? := stxs, task := next.resultD default, cancelTk? }]
      }
      -- Run `tac` in a fresh info tree state and store resulting state in snapshot for
      -- incremental reporting, then add back saved trees. Here we rely on `evalTactic`
      -- producing at most one info tree as otherwise `getInfoTreeWithContext?` would panic.
      let trees ← getResetInfoTrees
      try
        let (_, state) ← withRestoreOrSaveFull reusableResult?
            -- set up nested reuse; `evalTactic` will check for `isIncrementalElab`
            (tacSnap? := some { old? := oldInner?, new := inner }) do
          Term.withReuseContext tac do
            evalStep tac
        finished.resolve {
          diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog
            (← Core.getAndEmptyMessageLog))
          infoTree? := (← Term.getInfoTreeWithContext?)
          state? := state
          moreSnaps := (← Core.getAndEmptySnapshotTasks)
        }
      finally
        modifyInfoState fun s => { s with trees := trees ++ s.trees }

      withTheReader Term.Context ({ · with tacSnap? := some {
        new := next
        old? := oldNext?
      } }) do
        goOdd stxs
  -- `stx[0]` is the next separator, if any
  goOdd stx := do
    if stx.getNumArgs == 0 then
      return
    saveTacticInfoForToken stx[0] -- add `TacticInfo` node for `;`
    -- disable further reuse on separator change as to not reuse wrong `TacticInfo`
    Term.withNarrowedTacticReuse (fun stx => (stx[0], mkNullNode stx.getArgs[1:])) goEven stx
