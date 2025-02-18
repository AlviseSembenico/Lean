/-
Homework 1
Please fill out the sorry's below with Lean proofs.

If you're stuck, please describe your partial progress.
You could also state some intermediate goal, "sorry" it, and move on etc.
(to obtain part of the points for the problem).
-/

/-
Name:           Alvise Sembenico
University:     University of Amsterdam
Student number: 12380288
-/

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
-- import Mathlib.Data.Nat.Parity


variable {R : Type*} [CommRing R]

theorem double(x y : R) : (x+y)*(x+ -y) = x^2 - y^2 := by
  rw [left_distrib (x+y)]
  rw [right_distrib, right_distrib]
  rw [← add_assoc]
  rw [mul_comm x (-y)]
  rw [← neg_mul_eq_neg_mul]
  rw [add_comm]
  rw [add_assoc]
  rw [add_neg_cancel (y*x)]
  rw [add_zero]
  rw [add_comm]
  rw [← pow_two]
  rw [mul_comm y (-y)]
  rw [← neg_mul_eq_neg_mul]
  rw [← pow_two]
  rw [sub_eq_add_neg]

-- (1)
-- You may NOT use the "ring" tactic in this exercise; use only basic rewrites instead.
-- theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]
example (x y a b : R) (h : a = x+y+b): (a-b)*(x-y)=x^2-y^2 := by
  rw [h]
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_neg_cancel b]
  rw [add_zero]
  rw [sub_eq_add_neg]
  apply double

theorem doublep (b c :ℝ) : 4*b*c ≤ 2*b^2+2*c^2:= by
  have h: ((Real.sqrt 2) *b - (Real.sqrt 2) *c)^2 =2*b^2+2*c^2 -4*b*c:=by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring

  apply sub_nonneg.mp
  rw [← h]
  apply pow_two_nonneg


-- (2)
-- item (a)
-- hint : use (a-b+c)^2 ≥ 0, etc.
example (a b c : ℝ) : 3*(a^2+b^2+c^2) ≥ 2*(a*b+b*c+c*a) := by
  have h1: (a-b-c)^2≥ 0 := sq_nonneg (a-b-c)

  have h4 : 2*(a*b + a*c - b*c) + 4*b*c = 2*(a*b + b*c + c*a) := by
    ring
  have h5:  (a^2 + b^2 + c^2) + 4*b*c ≤ (a^2 + b^2 + c^2) + (2*b^2+2*c^2) := by
    apply add_le_add_left
    apply doublep
  have h7: 3*(a^2+b^2+c^2) =  (a^2 + b^2 + c^2) + (2*b^2+2*c^2+2*a^2) := by
    ring
  have h6: 3*(a^2+b^2+c^2) ≥ (a^2 + b^2 + c^2) + (2*b^2+2*c^2):= by
    rw [h7]
    apply add_le_add_left
    rw [add_assoc (2*b^2)]
    apply add_le_add_left
    nth_rw 1 [← add_zero (2*c^2) ]
    apply add_le_add_left
    apply mul_nonneg_iff.mpr
    left
    norm_num
    apply pow_two_nonneg

  rw [← h4]
  linarith

theorem amgm (a b : ℝ) : a^2+b^2 ≥ 2*|a*b| := by
  have h2 : Even 2 := ⟨1, rfl⟩
  calc
    a^2+b^2 = (a^2+b^2 - 2*|a*b|) + 2*|a*b| := by
      ring
    _ = (|a|^2+|b|^2 - 2*|a*b|) + 2*|a*b| := by
      rw [Even.pow_abs h2]
      rw [Even.pow_abs h2]
    _ = (|a|^2+|b|^2 - 2*|a| * |b|) + 2*|a*b| := by
      rw [mul_assoc, ← abs_mul]
    _ = (|a| - |b|)^2 + 2*|a*b| := by
      ring
    _ ≥ 0 + 2*|a*b| := by
      apply add_le_add
      apply pow_two_nonneg
      apply le_refl
    _ =  2*|a*b| := by
      apply zero_add


theorem amgm_r (a b : ℝ) : 2*|a*b| ≤ a^2+b^2 := by
  linarith [amgm a b]

theorem add_nonneg_right (a b :ℝ )(h: 0 ≤ b): a≤ a+b := by
  nth_rw 1 [← add_zero a]
  apply add_le_add_left h

theorem sum_sq_nneg (a b c : ℝ) : 0 ≤ a^2+b^2+c^2 := by
  calc
    0 ≤ a^2 := by
      apply pow_two_nonneg
    _ ≤ a^2 + b^2 := by
      apply add_nonneg_right
      apply pow_two_nonneg
    _ ≤ a^2 + b^2 +c^2 := by
      apply add_nonneg_right
      apply pow_two_nonneg

--item (b)
example (a b c : ℝ) : (a^2+b^2+c^2) ≥ 2*(|a*b|+|b*c|+|c*a|)/3 := by
  calc
    2*(|a*b|+|b*c|+|c*a|)/3 = (2*|a*b| +2*|b*c| +2*|c*a|)/3:= by
      ring
    _ = 2*|a*b|/3 +2*|b*c|/3+ 2*|c*a|/3 := by
      ring
    _ ≤ (a^2+b^2)/3 +2*|b*c|/3+ 2*|c*a|/3 := by
      apply add_le_add_right
      apply add_le_add_right
      apply (div_le_div_right (by norm_num)).mpr
      apply amgm_r
    _ ≤ (a^2+b^2)/3+(b^2+c^2)/3+2*|c*a|/3 := by
      apply add_le_add_right
      apply add_le_add_left
      apply (div_le_div_right (by norm_num)).mpr
      apply amgm_r
    _ ≤ (a^2+b^2)/3+(b^2+c^2)/3+(c^2+a^2)/3 := by
      apply add_le_add_left
      apply (div_le_div_right (by norm_num)).mpr
      apply amgm_r
    _ = (a^2+b^2+b^2+c^2+c^2+a^2)/3 := by
      ring
    _ = (2*a^2+2*b^2+2*c^2)/3:= by
      ring
    _ = (a^2+b^2+c^2)*2/3:= by
      ring
    _ ≤ (a^2+b^2+c^2) := by
      nth_rw 2 [← mul_one (a^2+b^2+c^2)]
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?h ?a0
      rw [div_le_iff₀ (by norm_num), one_mul]
      norm_num
      apply sum_sq_nneg





-- (3)
example (m n r : ℤ) (h : m - 1∣ n) : m - 1 ∣ (n * r + m ^ 3 - 1) * r := by
  sorry
