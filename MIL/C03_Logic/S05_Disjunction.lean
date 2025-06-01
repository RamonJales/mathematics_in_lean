import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  next h =>
    rw [abs_of_nonneg]
    apply h
  next h =>
    rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h --ganho hipoteses pela definição de abs
  rw [abs_of_nonneg]
  linarith
  exact h
  rw [abs_of_neg]
  exact h

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h | h
  rw [abs_of_nonneg h]
  linarith [le_abs_self x, le_abs_self y]
  rw [abs_of_neg h]
  linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  rw [abs_of_nonneg h]
  constructor
  intro h1
  left
  exact h1
  intro h1
  rcases h1 with h' | h'
  exact h'
  linarith
  rw [abs_of_neg h]
  constructor
  intro h1
  right
  exact h1
  intro h1
  rcases h1 with h' | h'
  linarith
  exact h'

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h]
  constructor
  intro h1
  constructor
  linarith
  exact h1
  intro h1
  exact h1.right
  rw [abs_of_neg h]
  constructor
  intro h1
  constructor
  linarith
  linarith
  intro h1
  linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, hz⟩
  rcases hz with rfl | rfl
  · -- caso z = x^2 + y^2
    apply add_nonneg
    apply sq_nonneg
    apply sq_nonneg
  · -- caso z = x^2 + y^2 + 1
    apply add_nonneg
    apply add_nonneg
    apply sq_nonneg
    apply sq_nonneg
    norm_num

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases  h1 : P
  right
  apply h
  apply h1
  left
  apply h1
  intro h1 h2
  rcases h1 with h' | h'
  contradiction
  apply h'
