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

-- (1)
-- You may NOT use the "ring" tactic in this exercise; use only basic rewrites instead.
example [CommRing R] (x y a : R) (h : a = x+y+b): (a-b)*(x-y)=x^2-y^2 := by
  sorry

-- (2)
-- item (a)
-- hint : use (a-b+c)^2 ≥ 0, etc.
example (a b c : ℝ) : 3*(a^2+b^2+c^2) ≥ 2*(a*b+b*c+c*a) := by
  sorry
--
--item (b)
example (a b c : ℝ) : (a^2+b^2+c^2) ≥ 2*(|a*b|+|b*c|+|c*a|)/3 := by
  sorry

-- (3)
example (m n r : ℤ) (h : m - 1∣ n) : m - 1 ∣ (n * r + m ^ 3 - 1) * r := by
  sorry
