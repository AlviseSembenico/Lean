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
  sorry


-- (2)
-- item (a)
-- hint : use (a-b+c)^2 ≥ 0, etc.
example (a b c : ℝ) : 3*(a^2+b^2+c^2) ≥ 2*(a*b+b*c+c*a) := by
  have h1: (a-b-c)^2≥ 0 := sq_nonneg (a-b-c)
  have h2 : (a - b - c)^2 = a^2 + b^2 + c^2 - 2*(a*b + a*c - b*c) := by
    ring
  have h3 : a^2 + b^2 + c^2 ≥ 2*(a*b + a*c - b*c) := by
    apply le_of_sub_nonneg
    rw [← h2]
    apply h1
  have h4 : 2*(a*b + a*c - b*c) + 4*b*c = 2*(a*b + b*c + c*a) := by
    ring
  have H : a^2 + b^2 + c^2 + 4*b*c ≥ 2*(a*b + a*c + b*c) :=by
    linarith


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



  -- refine le_of_add_le_add_right (4*b*c) _
--
--item (b)
example (a b c : ℝ) : (a^2+b^2+c^2) ≥ 2*(|a*b|+|b*c|+|c*a|)/3 := by
  sorry

-- (3)
example (m n r : ℤ) (h : m - 1∣ n) : m - 1 ∣ (n * r + m ^ 3 - 1) * r := by
  sorry
