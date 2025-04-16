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

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

lemma descent2 (a b c k : ℕ) (h : a * b = c ^ k) (h2: c ≠ 0) : a.Coprime b → ∃ x y, a = x ^ k ∧ b = y ^ k := by
  intro h3
  let p := a.primeFactorsList
  have fac_c : (c.primeFactorsList).prod = c := by
    exact Nat.prod_primeFactorsList h2
  -- split cases a,b = 0
  by_cases h_nonzero : (a ≠ 0 ∧ b ≠ 0)
  · sorry
  push_neg at h_nonzero
  by_cases ha : a = 0
  · have hb : b = 1 := by
      rw [ha] at h3
      rw [Nat.coprime_zero_left] at h3
      exact h3
    rw [ha, hb] at h
    exfalso
    by_cases hk : k = 0
    · rw [hk, pow_zero] at h
      simp at h
    sorry
      -- exact Nat.one_ne_zero h
    -- · rw [zero_pow (Nat.pos_of_ne_zero hk)] at h
      -- exact Nat.zero_ne (c ^ k) h
    -- use 0
    -- use 1

  have hb : b = 0 := h_nonzero ha
  have ha' : a = 1 := by
    rw [hb] at h3
    rw [Nat.coprime_zero_right] at h3
    assumption

  sorry






lemma descent (a b c k : ℕ) (h : a * b = c ^ k) : a.Coprime b → ∃ x y, a = x ^ k ∧ b = y ^ k := by
  rcases c with (rfl | n)
  · intro h1
    rw [zero_pow_eq] at h
    split_ifs at h with hk
    · use 0
      use 0
      rw [zero_pow_eq]
      rw [hk, if_pos (by decide)]
      apply mul_eq_one.mp h

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
  -- now the case for c != 0
  let c := n + 1
  have hc : c ≠ 0 := Nat.succ_ne_zero n
  exact descent2 a b c k h hc


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




We set up notation for `Graph.rel`. From now on we can write `x ~~ y` for the graph relation.

Uncomment the code below to enable the notation.
-/
--
-- -- A quick check to see the notation in action.
class SimpleGraph (G : Type*) where
 rel : G → G → Prop
 rel_sym : ∀ x y : G, rel x y → rel y x
 rel_irrefl : ∀ x: G, rel x x → false

notation3 x " ~~ " y => SimpleGraph.rel x y
variable (G : Type*) [SimpleGraph G] (x y : G) in
#check x ~~ y

/-
# Discrete and complete graphs

The *discrete* graph on `X` is the graph where no vertices are related.
The *complete* graph on `X` is the graph where all vertices are related to all vertices except themselves.
-/

-- We create two "type aliases" for the underlying vertices of these graph structures.
def DiscreteGraph (X : Type*) := X
def CompleteGraph (X : Type*) := X

-- ## Exercise 3.

instance (X : Type*) : SimpleGraph (DiscreteGraph X) where
  rel := sorry
  /- add more proofs here -/

instance (X : Type*) : SimpleGraph (CompleteGraph X) where
  /- complete this -/


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
