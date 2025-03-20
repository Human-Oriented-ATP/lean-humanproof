import HumanProof.Basic
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

lemma pow_totient_multiple_eq_one (n : ℕ) (m a : ℤ) (h_coprime : IsCoprime a m) (h_totient_multiple : n ≡ 0 [ZMOD m.natAbs.totient]) : a ^ n ≡ 1 [ZMOD m] := by
  sorry

lemma mul_right_cancel_mod (a : ℤ) {M : ℤ} (h_coprime : IsCoprime a M) {b c : ℤ} : (b * a ≡ c * a [ZMOD M]) → b ≡ c [ZMOD M] := by
  sorry

-- example (a b : ℕ) : a = b ∧ b = a := by
--   box_proof
--   refine ⟨?funny, ?brackets⟩
--   case' funny =>
--     refine nonsense
--   sorry

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
  box_proof
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
  apply Or.intro_left
  case' goal2 =>
    apply mul_right_cancel_mod a ?goal1.h_coprime
    simp [← pow_succ]
    rw_mod pow_totient_multiple_eq_one
  -- let HH : 1+1 = 2 := rfl
  skip
