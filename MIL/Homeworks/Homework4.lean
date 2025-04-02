/-
Homework 4
Please complete the Lean code below.

If you're stuck, please describe your partial progress (as comments).
You could also state some intermediate goal, "sorry" it, and move on etc.
(to obtain part of the points for the problem).
-/

/-
Name:           John Doe
University:     University of Somewhere
Student number: s123456
-/

import Mathlib

-- The next line is to ensure that variables are introduced explicitly; you can just ignore it.
set_option autoImplicit false



/-
## Exercise 1.
Please fill out the sorry's below with Lean proofs.
-/
-- (a)
lemma descent (a b c k : ℕ) (h : a * b = c ^ k) : a.Coprime b → ∃ x y, a = x ^ k ∧ b = y ^ k := by
  cases c
  · intro h1
    rw [zero_pow_eq] at h
    split_ifs at h with hk
    · sorry
    -- sorry
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with (ha | hb)
    · use 0
      use 1
      apply And.intro
      · rw [ha]
        symm
        apply zero_pow_eq_zero.mpr hk
      rw [ha] at h1
      rw [Nat.coprime_zero_left] at h1
      rw [one_pow]
      exact h1

    rw [hb] at h1
    rw [Nat.coprime_zero_right] at h1
    use 1
    use 0
    apply And.intro
    · rw [one_pow]
      exact h1
    symm
    rw [hb]
    apply zero_pow_eq_zero.mpr hk
  sorry
  -- now the case for c != 0


  -- hint: distinguish between the cases c = 0 and c ≠ 0 (and consider the prime factorization in the latter case).

-- (b)
lemma cubes_differ_one (x y k : ℕ) (hk : k ≥ 2) (h : x ^ k = y ^ k + 1) : y = 0 := by
  -- hint: Write x = y + z for some z : ℕ.
  -- hint: The following fact might be useful. Induction can help here.
  have aux : ∀ m ≥ 2, y ≠ 0 → y ^ m + 1 < (y + 1) ^ m := by
    sorry
  sorry

-- (c)
theorem Diophantine (x y k : ℕ) (hk : k ≥ 2) (h : x ^ 2 + x = y ^ k) : x = 0 ∧ y = 0 := by
  sorry
  -- hint: use the previous two lemmas.


-- Namespace, to avoid name clashes with Mathlib.
namespace HW4

/-
# Graphs

Let `G` be a type. A *simple graph* on `G` is a relation `_ ~~ _ : G → G → Prop`
that is symmetric and irreflexive:
- for all `x y : G` we have `x ~~ y` implies `y ~~ x`
- for all `x : G` we have that `x ~~ x` is false
-/

/-
## Exercise 2.
Define a typeclass with a type `G` as parameter,
and with one field `rel` that encodes the graph relation `G → G → Prop`.
Also add two fields `rel_symm` and `rel_irrefl`.
Note that we can only set up the notation `x ~~ y` after the definition is complete.
So the two fields `rel_symm` and `rel_irrefl` must be expressed in terms of `rel` directly.

Uncomment the code below, and complete it.
-/

-- class SimpleGraph (G : Type*) where
--  rel : /- replace this with the type of `rel` -/
--  /- add fields here -/

/-
We set up notation for `Graph.rel`. From now on we can write `x ~~ y` for the graph relation.

Uncomment the code below to enable the notation.
-/
-- notation3 x " ~~ " y => SimpleGraph.rel x y
--
-- -- A quick check to see the notation in action.
-- variable (G : Type*) [SimpleGraph G] (x y : G) in
-- #check x ~~ y

/-
# Discrete and complete graphs

The *discrete* graph on `X` is the graph where no vertices are related.
The *complete* graph on `X` is the graph where all vertices are related to all vertices except themselves.
-/

-- We create two "type aliases" for the underlying vertices of these graph structures.
def DiscreteGraph (X : Type*) := X
def CompleteGraph (X : Type*) := X

/-
## Exercise 3.
Define the appropriate instances on `DiscreteGraph X` and `CompleteGraph X`.

Uncomment the code below, and complete it.
-/

-- instance (X : Type*) : SimpleGraph (DiscreteGraph X) where
--   rel := /- replace this with the relation -/
--   /- add more proofs here -/

-- instance (X : Type*) : SimpleGraph (CompleteGraph X) where
--   /- complete this -/

/-
## Exercise 4.
Let `G₁` and `G₂` be simple graphs.
-/

-- uncomment this line
-- variable {G₁ G₂ : Type*} [SimpleGraph G₁] [SimpleGraph G₂]

/-
A *graph homomorphism* (in this exercise) is a function `G₁ → G₂` that preserves the graph relations.
Define a structure `IsGraphHom` that takes a function `f : G₁ → G₂` as parameter,
and a field `map_rel` that expresses that `f` is a graph homomorphism.

Uncomment the code below, and complete it.
-/

-- structure IsGraphHom /- complete this -/

/-
## Exercise 5.
Show that for any type `X`, all functions `f : DiscreteGraph X → CompleteGraph X` are graph homomorphisms.

Uncomment the code below, and complete it.
-/

-- example (X : Type*) (f : DiscreteGraph X → CompleteGraph X) : IsGraphHom f where
--   /- complete this -/

end HW4
