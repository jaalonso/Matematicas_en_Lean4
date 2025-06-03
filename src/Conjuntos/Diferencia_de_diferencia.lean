-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) \ u ⊆ s \ (t ∪ u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ (s \ t) \ u. Entonces, se tiene que
--    x ∈ s                                                      (1)
--    x ∉ t                                                      (2)
--    x ∉ u                                                      (3)
-- Tenemos que demostrar que
--    x ∈ s \ (t ∪ u)
-- pero, por (1), se reduce a
--    x ∉ t ∪ u
-- que se verifica por (2) y (3).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  rcases hx with ⟨hxst, hxnu⟩
  -- hxst : x ∈ s \ t
  -- hxnu : ¬x ∈ u
  rcases hxst with ⟨hxs, hxnt⟩
  -- hxs : x ∈ s
  -- hxnt : ¬x ∈ t
  constructor
  . -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ ¬x ∈ t ∪ u
    by_contra hxtu
    -- hxtu : x ∈ t ∪ u
    -- ⊢ False
    rcases hxtu with (hxt | hxu)
    . -- hxt : x ∈ t
      apply hxnt
      -- ⊢ x ∈ t
      exact hxt
    . -- hxu : x ∈ u
      apply hxnu
      -- ⊢ x ∈ u
      exact hxu

-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨hxs, hxnt⟩, hxnu⟩
  -- x : α
  -- hxnu : ¬x ∈ u
  -- hxs : x ∈ s
  -- hxnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  constructor
  . -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ ¬x ∈ t ∪ u
    by_contra hxtu
    -- hxtu : x ∈ t ∪ u
    -- ⊢ False
    rcases hxtu with (hxt | hxu)
    . -- hxt : x ∈ t
      exact hxnt hxt
    . -- hxu : x ∈ u
      exact hxnu hxu

-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  -- x : α
  -- xnu : ¬x ∈ u
  -- xs : x ∈ s
  -- xnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  use xs
  -- ⊢ ¬x ∈ t ∪ u
  rintro (xt | xu)
  . -- xt : x ∈ t
    -- ⊢ False
    contradiction
  . -- xu : x ∈ u
    -- ⊢ False
    contradiction

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  -- x : α
  -- xnu : ¬x ∈ u
  -- xs : x ∈ s
  -- xnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  use xs
  -- ⊢ ¬x ∈ t ∪ u
  rintro (xt | xu) <;> contradiction

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intro x xstu
  -- x : α
  -- xstu : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  simp at *
  -- ⊢ x ∈ s ∧ ¬(x ∈ t ∨ x ∈ u)
  aesop

-- 6ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intro x xstu
  -- x : α
  -- xstu : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  aesop

-- 7ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw [diff_diff]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s \ (t ∪ u) ⊆ (s \ t) \ u
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s \ (t ∪ u). Entonces,
--    x ∈ s                                                          (1)
--    x ∉ t ∪ u                                                      (2)
-- Tenemos que demostrar que x ∈ (s \ t) \ u; es decir, que se verifican
-- las relaciones
--    x ∈ s \ t                                                      (3)
--    x ∉ u                                                          (4)
-- Para demostrar (3) tenemos que demostrar las relaciones
--    x ∈ s                                                          (5)
--    x ∉ t                                                          (6)
-- La (5) se tiene por la (1). Para demostrar la (6), supongamos que
-- x ∈ t; entonces, x ∈ t ∪ u, en contracción con (2). Para demostrar la
-- (4), supongamos que x ∈ u; entonces, x ∈ t ∪ u, en contracción con
-- (2).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s \ (t ∪ u)
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact hx.1
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply hx.2
      -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    apply hx.2
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      exact xntu (Or.inl xt)
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    exact xntu (Or.inr xu)

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  fun _ ⟨xs, xntu⟩ ↦ ⟨⟨xs, fun xt ↦ xntu (Or.inl xt)⟩,
                      fun xu ↦ xntu (Or.inr xu)⟩

-- 4ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  aesop

-- 5ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by intro ; aesop

-- 6ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by rw [diff_diff]

-- Lemas usados
-- ============

variable (a b : Prop)
#check (Or.inl : a → a ∨ b)
#check (Or.inr : b → a ∨ b)
#check (diff_diff : (s \ t) \ u = s \ (t ∪ u))
