import Mathlib

-- Lecture 2 about MiL Ch. 2

-- basic rewriting:
theorem foo (a b c : ℝ) (h : c = a + b): c * c = a * a + 2 * (a * b) + b * b := by
  rw [h ] -- rewrite in goal every occurence of c
  rw [mul_add, add_mul, add_mul] -- rewrites in goal first occurence of given pattern (3 different times)
  rw [← add_assoc] -- as above, but now from right to left
  rw [add_assoc (a * a), mul_comm b a] -- more of the pattern for rewriting is specified
  rw [← two_mul] -- finish (could also be done without ←)


#print foo -- tactic mode "by" created a proof term

-- structured with calc:
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- Note: "by calc" can also be used (so as a tactic)

-- rewriting can also be done in assumptions in the context
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp', mul_comm, ← two_mul, ← mul_assoc ] at hyp
  exact hyp -- "exact" tactic closes goal, since hyp mathches it exactly

-- Note: for rewritng only n-th occurence there is "nth_rw" (e.g. "nth_rw 2 [h]" or "nth_rw 3 [h] at hh")

-- The "ring" tactic can prove polynomial identities in commutative semirings (and deals with subtraction in commutative rings)
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example (R : Type*) [CommSemiring R] (a b : R): (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example (R : Type*) [CommSemiring R] (a b c d : R) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


namespace MyRing
variable {R : Type} [Ring R]
#check R
-- for rings we have lots of basic statements, including:
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c)) -- remember that a+b+c means (a+b)+c
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

-- Prove something in a general ring with rewriting:
theorem My_neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry

-- curly brackets mark arguments as implicit
#check add_left_cancel



-- Solutions:
-- add_neg_cancel_right
example (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

-- add_left_cancel
example {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, ← neg_add_cancel_left a c, h]

-- add_right_cancel
example {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, ← add_neg_cancel_right c b, h]


-- the "have" tactic introduces a new goal:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel this] -- also "apply" or "exact" tactics could be used

-- Prove this:
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry


-- Solution:
--zero_mul:
example (a : R) : 0 * a = 0 := by
  have : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  exact add_left_cancel this


-- subtraction in rings, and instances thereof; def. of subtraction can be type dependent:

example (a b : R) : a - b = a + -b := sub_eq_add_neg a b -- "rfl" will NOT work

example (a b : ℝ) : a - b = a + -b := rfl -- or "by rfl"
    -- "sub_eq_add_neg a b" also still works

end MyRing


-- Some more algebraic structures


--Group with multiplicative notation, tactic "group":
example (G : Type*) [Group G] (x y z : G) : (x*y)*((z*x)*z) =x*(y*1*z)*x*x⁻¹*x*z := by group

--Abelian Group with additive notation, tactic "abel"
example (A : Type*) [AddCommGroup A] (x y z : A) : (x+y)+((z+x)+2•z) =x+(y+z)+x-x+x+z+z := by abel

--Abelian Group with multiplicative notation ("group" tactic still works)
example (G : Type*) [CommGroup G] (x y z : G) : (x*y)*((z*x)*z) =x*(y*1*z)*x*x⁻¹*x*z := by group

-- Group (not necessary abelian) wiht additive notation, "simp" tactic can still be used:
example (A : Type*) [AddGroup A] (x y z : A) : (x+y)+((z+x)+2•z) =x+(y+z)+x-x+x+z+z := by simp [two_nsmul,add_assoc]


-- already saw "ring" tactic for commutatice semirings.
-- for general semirings, there is the "noncomm_ring" tactic
example (R : Type*) [Semiring R] (x y : R) : x^2+y+x*y+y=x*(x+y)+2*y := by noncomm_ring
example (R : Type*) [Ring R] (x y : R) : x^2+y+x*y-y=x*(x+y) := by noncomm_ring -- can handle subtraction


section -- Scope of variables is delimited by section ... end

-- Some inequalities
variable (a b c : ℝ) (h : a ≤ b) (h' : b ≤ c) -- or on [PartialOrder R] ...

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)


-- "apply" tactic creates new goals (which imply the original goal)
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans -- apply creates two goals + one that will be solved when dealing with the first goal
  · apply h₀ -- dot focusses on current goal
  · apply h₁


-- some more basics:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

end
-- prove this:
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry


-- solutions (some generalized to [PartialOrder R]):
example [PartialOrder R] (a b c d e : R) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  apply lt_of_le_of_lt h₂
  exact h₃ --instead of last two lines: --exact lt_of_le_of_lt h₂ h₃

example [PartialOrder R] (a b c d e : R) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := calc
  a ≤ b := h₀
  _ < c := h₁
  _ ≤ d := h₂
  _ < e := h₃

-- "linarith" tactic solves linear inequalities
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (a b d : ℝ) (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

-- "apply?" tactic searches the library
example (a : ℝ): 0 ≤ a ^ 2 := by
  apply?
  --exact sq_nonneg a

-- Note, also in MiL Ch. 2: constructor, .mpr (/.mp), repeat, norm_num (, and show)


-- Note on Type hierarchies
-- every term has a type:
#check ℕ
#check ℝ
#check Bool
#check ℝ → ℝ

#check Type 0
#check Type 32
-- #check Type 33

#check Prop

#check 1+1=2 -- true:
  example : 1+1=2 := rfl
#check 1+1=3 -- false:
  example : 1 + 1 ≠ 3 := by norm_num

-- for a proposition P, a term prf of type P (i.e. prf : P), "is" a proof of P
def easy : ∀ m n : Nat, Even n → Even (m * n) := by
  intros
  simp [*]

#print easy


section

variable (R : Type*)
#check R

universe u
#check Sort
#check Sort 1
#check Sort u
#check Sort (u+1)

end
