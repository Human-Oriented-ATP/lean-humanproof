import Mathlib.Tactic

lemma sq_eq_one' {m : ℕ} (a : ZMod m) (ha : a = -1 ∨ a = 1) : a ^ 2 = 1 := by
  cases ha
  · simp_all only [even_two, Even.neg_pow, one_pow]
  · simp_all only [one_pow]

lemma mul_right_cancel_mod (a : ℤ) {M : ℕ} (h_coprime : IsCoprime a M) {b c : ZMod M} : (b * a = c * a) → b = c := by
  intro h
  have h_coprime : Nat.Coprime a.natAbs ↑M := by
    apply IsCoprime.nat_coprime
    match a with
    | .ofNat a => simp_all [Int.natAbs]
    | .negSucc a =>
      rw [← IsCoprime.neg_left_iff]
      simp only [Int.natAbs, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      exact h_coprime
  have h' : b * a.natAbs = c * a.natAbs := by
    match a with
    | .ofNat a => simp_all [Int.natAbs]
    | .negSucc a =>
      simp [Int.natAbs]
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one,
                @Mathlib.Tactic.RingNF.mul_neg, neg_inj] at h
      assumption
  rw [← ZMod.isUnit_iff_coprime] at h_coprime
  calc b = b * 1 := by rw [mul_one]
       _ = b * (a.natAbs * (a.natAbs : ZMod M)⁻¹) := by rw [ZMod.mul_inv_of_unit _ h_coprime]
       _ = (b * a.natAbs) * (a.natAbs : ZMod M)⁻¹ := by rw [mul_assoc]
       _ = (c * a.natAbs) * (a.natAbs : ZMod M)⁻¹ := by rw [h']
       _ = c * (a.natAbs * (a.natAbs : ZMod M)⁻¹) := by rw [mul_assoc]
       _ = c * 1 := by rw [ZMod.mul_inv_of_unit _ h_coprime]
       _ = c := by rw [mul_one]

lemma pow_eq_self_of_exp_mod_one_totient {m n : ℕ} (a : ℤ)
    (h_coprime : IsCoprime a m) (h_exp_mod_one : @Nat.cast (ZMod (Nat.totient m)) NonAssocSemiring.toNatCast n = (1 : ZMod (Nat.totient m))) : (a : ZMod m) ^ n = (a : ZMod m) := by
  have a_is_unit : IsUnit (a : ZMod m) := by
    rw [← @isCoprime_zero_right]
    let ⟨c, d, h_sum⟩ := h_coprime
    use c; use d
    rw [← ZMod.natCast_self]
    norm_cast
    rw [h_sum]
    simp
  let u := a_is_unit.unit
  have : ↑u = (a : ZMod m) := a_is_unit.unit_spec
  rw [← this]
  by_cases hn : n = 0
  · subst hn
    simp_all
    rw [← ZMod.natCast_self] at h_exp_mod_one
    have : m = 1 ∨ m = 2 := by
      by_contra h
      sorry
    match this with
    | .inl h1 =>
      subst h1
      symm
      show _ = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_one]
      exact Int.one_dvd a
    | .inr h2 =>
      subst h2
      let ⟨c, d, hsum⟩ := h_coprime
      have hsum' := congrArg (Int.cast : ℤ → ZMod 2) hsum
      sorry
  · have : ∃ k, n = 1 + m.totient * k := by
      by_cases h : m = 0
      . subst h
        use 0
        simp_all
      · by_cases h' : m.totient = 1
        · use n.pred
          rw [h']
          simp only [Nat.pred_eq_sub_one, one_mul]
          rw [add_comm, Nat.sub_add_cancel]
          rwa [@Nat.one_le_iff_ne_zero]
        . haveI : NeZero m.totient := neZero_iff.mpr ((not_iff_not.mpr Nat.totient_eq_zero).mpr h)
          rw [ZMod.natCast_eq_iff] at h_exp_mod_one
          let ⟨k, hk⟩ := h_exp_mod_one
          use k
          rw [hk]
          congr
          rw [ZMod.val_eq_one]
          rw [@Nat.one_lt_iff_ne_zero_and_ne_one]
          constructor
          · exact (not_iff_not.mpr m.totient_eq_zero).mpr h
          · exact h'
    let ⟨k, hkn⟩ := this
    subst hkn
    rw [add_comm, pow_succ, @npow_mul]
    rw [← @Units.val_pow_eq_pow_val]
    rw [ZMod.pow_totient u]
    simp only [Units.val_one, one_pow, one_mul]

lemma pow_totient_multiple_eq_one {m n : ℕ} (a : ℤ) (h_coprime : IsCoprime a m) (h_totient_multiple : @Nat.cast (ZMod (Nat.totient m)) AddMonoidWithOne.toNatCast n = (0 : ZMod m.totient)) : (a : ZMod m) ^ n = 1 := by
  have a_is_unit : IsUnit (a : ZMod m) := by
    rw [← @isCoprime_zero_right]
    let ⟨c, d, h_sum⟩ := h_coprime
    use c; use d
    rw [← ZMod.natCast_self]
    norm_cast
    rw [h_sum]
    simp
  let u := a_is_unit.unit
  have : ↑u = (a : ZMod m) := a_is_unit.unit_spec
  rw [← this]
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h_totient_multiple
  let ⟨k, hkn⟩ := h_totient_multiple
  subst hkn
  rw [@npow_mul]
  rw [← @Units.val_pow_eq_pow_val]
  rw [ZMod.pow_totient u]
  simp only [Units.val_one, one_pow]

def exists_all_mod_large (n : ℕ) {m : ℕ} (hm : m > 0) (a : ZMod m) : ∃ N ≥ n, N = a := by
  use a.val + m * n
  constructor
  · apply le_add_of_le_right
    exact Nat.le_mul_of_pos_left n hm
  · haveI : NeZero m := neZero_iff.mpr (Nat.not_eq_zero_of_lt hm)
    rw [ZMod.natCast_eq_iff]
    use n

lemma ZMod.mod_dvd {a b : ℤ} {m n : ℕ} (h : m ∣ n) : (a : ZMod n) = (b : ZMod n) → (a : ZMod m) = (b : ZMod m) := by
  rw [intCast_eq_intCast_iff_dvd_sub, intCast_eq_intCast_iff_dvd_sub]
  intro h'
  trans
  · zify at h
    exact h
  · exact h'

lemma ZMod.mod_dvd_prod_left {a b : ℤ} {m n : ℕ} : (a : ZMod (m * n)) = (b : ZMod (m * n)) → (a : ZMod m) = (b : ZMod m) := ZMod.mod_dvd (Nat.dvd_mul_right m n)

lemma ZMod.mod_dvd_prod_right {a b : ℤ} {m n : ℕ} : (a : ZMod (m * n)) = (b : ZMod (m * n)) → (a : ZMod n) = (b : ZMod n) := ZMod.mod_dvd (Nat.dvd_mul_left n m)

open Lean Elab Meta Command Term Tactic in
elab "create_new_goal" nm:ident t:term : tactic => withMainContext do
  let stmt ← Term.elabTerm t none
  let mvar ← mkFreshExprMVar stmt .natural nm.getId
  appendGoals [mvar.mvarId!]

set_option linter.unusedTactic false in
example (a b : ℤ) (ha : a > 0) (hb : b > 0) : ∃ (M : ℕ), M > 1 ∧ ∀ n₀ : ℕ, ∃ N ≥ n₀, ↑M ∣ (a ^ N + b) ∧ ↑M ∣ (b ^ N + a) := by
  -- pre-processing
  letI _ : Ring (ZMod ?M) := @CommRing.toRing _ (ZMod.commRing ?M)
  letI _ : Semiring (ZMod ?M) := Ring.toSemiring
  refine' ⟨?M, ?gM, λ n₀ ↦ ⟨?N, ?gN, ?goal1, ?goal2⟩⟩
  -- Step 1
  -- save
  rotate_right 2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  apply add_eq_zero_iff_eq_neg'.mpr
  rotate_right
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  apply add_eq_zero_iff_eq_neg'.mpr
  -- Step 2
  -- save
  rotate_left 5
  rw [?goal1]
  -- Step 3
  save
  rw [@neg_pow, ← @pow_mul, @neg_mul_eq_neg_mul, neg_eq_neg_one_mul, ← pow_succ', ← Nat.pow_two]
  -- Step 4 (risky step)
  save
  rw [Even.neg_one_pow ?NSuccEven, one_mul]
  rotate_left 4
  refine' Odd.add_odd (a := ?N) (b := 1) ?NOdd odd_one
  apply ZMod.eq_one_iff_odd.mp
  -- Step 5, 6, 7
  save
  rotate_right 4
  symm
  apply pow_eq_self_of_exp_mod_one_totient
  rotate_left
  push_cast
  -- Step 8
  save
  apply sq_eq_one'
  -- Step 9
  save
  left
  -- Step 10
  save
  rotate_left 8
  refine' mul_right_cancel_mod a ?Coprime_a_M ?goal1'
  exact ?goal2.h_coprime
  simp [← @pow_succ]
  -- Step 11
  save
  rw [pow_totient_multiple_eq_one]
  rotate_left
  exact ?goal2.h_coprime
  rw [@Nat.cast_add]
  rw [?goal2.h_exp_mod_one.ha.h]
  push_cast
  rw [@Ring.neg_add_cancel]
  -- Step 12
  save
  rotate_right
  rw [mul_comm]
  rw [@eq_neg_iff_add_eq_zero]
  norm_cast
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd (a * b + 1) _).mpr ?goal1''
  -- Step 13
  save
  rotate_right 9
  obtain ⟨c, hc⟩ := dvd_def.mp ?goal1''
  use -b; use c
  rw [mul_comm c, ← hc, mul_comm a]
  simp only [neg_mul, neg_add_cancel_left]
  -- Step 14
  save
  rotate_left 8
  rw [← Int.toNat_of_nonneg (a := a * b + 1)]
  rotate_left
  positivity
  rotate_right
  norm_cast
  exact Nat.dvd_refl _
  -- Step 15
  save
  rotate_left 4
  simp only [gt_iff_lt, Int.lt_toNat, Nat.cast_one, lt_add_iff_pos_left]
  positivity
  -- Step 16
  save
  -- TODO: Investigate why `?M` is a type and not a `ℕ`
  create_new_goal N_mod ((?N : ℤ) : ZMod (2 * (a * b + 1).toNat.totient)) = ((-1 : ℤ) : ZMod (2 * (a * b + 1).toNat.totient))
  rotate_left 6
  have := ZMod.mod_dvd_prod_left ?N_mod
  push_cast at this
  assumption
  rotate_right 2
  have := ZMod.mod_dvd_prod_right ?N_mod
  push_cast at this
  assumption
  -- Step 17
  save
  rotate_left 5
  push_cast
  create_new_goal N_witness { N : ℕ // N ≥ n₀ ∧ N = (-1 : ZMod (2 * (a * b + 1).toNat.totient)) }
  exact (Subtype.prop ?N_witness).right
  exact (Subtype.prop ?N_witness).left
  apply Classical.indefiniteDescription
  refine exists_all_mod_large n₀ ?mod_pos (-1 : ZMod (2 * (a * b + 1).toNat.totient))
  apply Nat.mul_pos (by positivity)
  show 0 < _
  rw [Nat.totient_pos]
  zify
  rw [Int.toNat_of_nonneg (a := a * b + 1) ?mod_nonneg]
  rotate_left
  exact Int.le_of_lt ?mod_pos
  positivity
