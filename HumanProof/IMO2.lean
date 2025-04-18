import HumanProof.BoxIncremental
import Mathlib
import HumanProof.RwMod

#check Nat.totient

lemma sq_eq_one' {m : ℤ} (a : ℤ) (ha : a ≡ -1 [ZMOD m] ∨ a ≡ 1 [ZMOD m]) : a ^ 2 ≡ 1 [ZMOD m] := by
  cases ha with
  | inl h => rw_mod h; rfl
  | inr h => rw_mod h; rfl

lemma my_pow_eq_self_of_exp_mod_one_totient (m : ℤ) (n : ℕ) (a : ℤ)
    (h_coprime : IsCoprime a m)
    (h_exp_mod_one : n ≡ 1 [ZMOD Nat.totient m.natAbs])
    : a ^ n ≡ a [ZMOD m] := by
  sorry

lemma pow_totient_multiple_eq (n1 n2 : ℕ) (m a : ℤ) (h_coprime : IsCoprime a m) (h_totient_multiple : n1 ≡ n2 [ZMOD m.natAbs.totient]) : a ^ n1 ≡ a ^ n2 [ZMOD m] := by
  sorry

lemma pow_totient_multiple_eq_one (n : ℕ) (m a : ℤ) (h_coprime : IsCoprime a m) (h_totient_multiple : n ≡ 0 [ZMOD m.natAbs.totient]) : a ^ n ≡ 1 [ZMOD m] :=
  pow_totient_multiple_eq n 0 m a h_coprime h_totient_multiple

lemma mul_right_cancel_mod (a : ℤ) {M : ℤ} (h_coprime : IsCoprime a M) {b c : ℤ} : (b * a ≡ c * a [ZMOD M]) → b ≡ c [ZMOD M] := by
  sorry

lemma coprime_add (a b : ℤ) (h : IsCoprime a b) : IsCoprime a (b+a) := by
  sorry

lemma merge_mod (a b m1 m2: ℤ) (h : a ≡ b [ZMOD m1*m2])
: a ≡ b [ZMOD m1] ∧ a ≡ b [ZMOD m2] := sorry

lemma exists_all_mod_large (n m a : ℤ) (hm : m > 0) : ∃ N : ℕ, N > n ∧ N ≡ a [ZMOD m] := by
  sorry

/-
free variables a,b,n0 : Z
metavariables:
M : Z (context: a,b)
N : Z (context: a,b,n0)
Assumptions:
* a > 1
* b > 1
Constraints (goals):
* M > 1
* N > n0
* M | a^N + b
* M | b^N + a
-/
example (a b : ℤ) (ha : a > 1) (hb : b > 1) : ∃ M : ℤ, M > 1 ∧ ∀ n0 : ℤ, ∃ N : Nat, N > n0 ∧ M ∣ a^N + b ∧ M ∣ b^N + a := by
  box_proofi
  refine ⟨?m, ?_, ?_⟩
  intro n0
  refine ⟨?N, ?_, ?goal2, ?goal1⟩
  apply Int.modEq_zero_iff_dvd.mp
  apply Int.ModEq.add_left_cancel' (-b ^ ?N); ring_nf
  on_goal 2 => apply Int.modEq_zero_iff_dvd.mp
  on_goal 2 => apply Int.ModEq.add_left_cancel' (-a ^ ?N); ring_nf
  rw_mod ?goal2
  rw [@neg_pow, ← @pow_mul, @neg_mul_eq_neg_mul, neg_eq_neg_one_mul, ← pow_succ', ← Nat.pow_two]
  rw [Even.neg_one_pow ?NSuccEven, one_mul]
  case' NSuccEven =>
    refine' Odd.add_odd (a := ?N) (b := 1) ?NOdd odd_one
  case' NSuccEven =>
    apply (Int.odd_coe_nat ?N).mp
  case' NSuccEven =>
    apply Int.odd_iff.mpr
  case' NSuccEven =>
    have : (1:Int) = 1%2 := rfl
  case' NSuccEven =>
    rw [this]
  case' NSuccEven =>
    show ?N ≡ 1 [ZMOD 2]
  case' goal1 =>
    symm
    apply my_pow_eq_self_of_exp_mod_one_totient ?m (?N^2) a
    on_goal 2 => push_cast
  case' goal1.h_exp_mod_one =>
    apply sq_eq_one'
  backup -- dead branch that ends up needing (a,b) coprime
  apply Or.intro_right
  case' goal2 => rw_mod (pow_totient_multiple_eq)
  case' goal1.h_coprime => exact ?h_coprime
  case' h_totient_multiple => exact ?goal1.h_exp_mod_one.h
  case' goal2 => simp only [pow_one]
  case' goal2 => exact Int.modEq_sub _ _
  case' h_coprime =>
    simp only [sub_neg_eq_add]
  case' h_coprime =>
    apply coprime_add
  case' goal1.h_exp_mod_one.h =>
    simp only [sub_neg_eq_add]
  case' refine_1 =>
    simp only [sub_neg_eq_add]
  case' NSuccEven =>
    refine (merge_mod _ _ _ ?_ ?merged_mod).1
  case' goal1.h_exp_mod_one.h =>
    refine (merge_mod _ _ _ _ ?merged_mod).2
  case' refine_1 => omega
  have exists_N := exists_all_mod_large n0 (2 * ↑(b + a).natAbs.totient) 1 (by
    norm_cast
    apply Nat.succ_mul_pos
    apply Nat.totient_pos.mpr
    omega
  )
  obtain ⟨N, Nbig, Nmod⟩ := exists_N
    -- exact Nbig
  -- case' goal2 =>
  --   apply mul_right_cancel_mod a ?goal1.h_coprime
  --   simp [← pow_succ]
  --   rw_mod pow_totient_multiple_eq_one

  skip

example (a : ℕ) (h : a > 0) : (a.totient > 0) := by
  exact Nat.totient_pos.mpr h

example (p q : ℕ → Prop) (h : ∃ n, p n ∧ q n)
: ∃ m : ℕ, q m ∧ p m := by
  box_proof
    refine ⟨?m, ?_, ?_⟩
    obtain ⟨n, h2⟩ := h
