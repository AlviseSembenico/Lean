/-
Homework 2
Please fill out the sorry's below with Lean proofs.

If you're stuck, please describe your partial progress (as comments).
You could also state some intermediate goal, "sorry" it, and move on etc.
(to obtain part of the points for the problem).
-/

/-
Name:           Alvise Sembenico
University:     University of Amsterdam
Student number: 12380288
-/

import Mathlib

-- The next line is to ensure that variables are introduced explicitly; you can just ignore it.
set_option autoImplicit false

-- (1)
lemma three_dvd_sq_sub_or_sq_add (h : ∀ (a b : ℤ), b > 0 → ∃ q r, a = q * b + r ∧ 0 ≤ r ∧ r < b) :
    ∀ (m : ℤ) , 3 ∣ m ^ 2 - m ∨ 3 ∣ m ^ 2 + m := by
  intro m
  have ⟨q, r, hr⟩ := h m 3 (by norm_num)
  simp [hr]
  match r with
  | 0 => left
         rw [add_zero]
         use 3 * q * q - q
         ring
  | 1 => left
         use q*(3*q+1)
         ring
  | 2 => right
         use 3*q^2 + 5*q+2
         ring

-- (2)
-- We first introduce some notation.
section

variable {X Y : Type*}

def graph (f : X → Y) : Set (X × Y) :=
  { p | p.2 = f p.1 }

def IsGraph (S : Set (X × Y)) : Prop :=
  ∀ x, ∃! y, (x, y) ∈ S

noncomputable
def functionOfGraph (S : Set (X × Y)) (hS : IsGraph S) : X → Y :=
  fun x => (hS x).choose

-- Now do parts (a)--(e) below.

-- (a)
lemma graph_isGraph (f : X → Y) : IsGraph (graph f) := by
  dsimp [IsGraph, graph]
  intro x
  use f x
  constructor
  · rfl
  intro y fh
  exact fh


-- (b)
lemma graph_injective : Function.Injective (graph (X := X) (Y := Y)) := by
  dsimp [Function.Injective]
  intro x y
  dsimp [graph]
  have h₁ (a : X): (a, x a) ∈ {p | p.2 = x p.1} := by simp
  intro h
  rw [h] at h₁
  simp at h₁
  funext a
  apply h₁


-- (c)
lemma functionOfGraph_spec (S : Set (X × Y)) (hS : IsGraph S) (x : X) (y : Y) :
    (x, y) ∈ S ↔ y = functionOfGraph S hS x := by

    have h2: S = graph (functionOfGraph S hS):= by
      simp [graph]
      ext ⟨x, y⟩
      constructor
      · intro h
        exact (hS x).choose_spec.2 y h

      intro h
      dsimp [graph]
      dsimp [functionOfGraph] at h
      rw [h]
      exact (hS x).choose_spec.1

    constructor
    · intro h
      rw [h2] at h
      apply h

    intro h
    rw [h2]
    apply h


-- (d)
lemma functionOfGraph_graph (f : X → Y) : functionOfGraph (graph f) (graph_isGraph f) = f := by
  simp [graph]
  ext x
  exact (graph_isGraph f x).choose_spec.1



-- (e)
lemma graph_functionOfGraph (S : Set (X × Y)) (hS : IsGraph S) :
    graph (functionOfGraph S hS) = S := by
  simp [graph]
  ext ⟨x, y⟩
  constructor
  · intro h
    dsimp [graph]
    dsimp [functionOfGraph] at h
    rw [h]
    exact (hS x).choose_spec.1

  intro h
  exact (hS x).choose_spec.2 y h


end
