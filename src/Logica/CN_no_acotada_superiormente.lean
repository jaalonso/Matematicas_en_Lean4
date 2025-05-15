-- ---------------------------------------------------------------------
-- Ejercicio. Sea f una función de ℝ en ℝ. Demostrar que si f no tiene
-- cota superior, entonces para cada a existe un x tal que f(x) > a.
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Usaremos los siguientes lemas
--    ¬(∃x)P(x) → (∀x)¬P(x)                                          (L1)
--    ¬a > b → a ≤ b                                                 (L2)
--
-- Sea a ∈ ℝ. Tenemos que demostrar que
--    (∃x)[f(x) > a]
-- Lo haremos por reducción al absurdo. Para ello, suponemos que
--    ¬(∃x)[f(x) > a]                                                (1)
-- y tenemos que obtener una contradicción. Aplicando L1 a (1) se tiene
--    (∀x)[¬ f(x) > a]
-- y, aplicando L2, se tiene
--    (∀x)[f(x) ≤ a]
-- Lo que significa que a es una cota superior de f y, por tanto f está
-- acotada superiormente, en cotradicción con la hipótesis.

-- 2ª demostración en LN
-- =====================

-- Por la contrarecíproca, se supone que
--    ¬(∀a)(∃x)[f(x) > a]                                             (1)
-- y tenemos que demostrar que f está acotada superiormente.
--
-- Interiorizando la negación en (1) y simplificando, se tiene que
--    (∃a)(∀x)[f x ≤ a]
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Data.Real.Basic

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬FnHasUb f)
  : ∀ a, ∃ x, f x > a :=
by
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, f x > a
  by_contra h1
  -- h1 : ¬∃ x, f x > a
  -- ⊢ False
  have h2 : ∀ x, ¬ f x > a :=
    forall_not_of_not_exists h1
  have h3 : ∀ x, f x ≤ a := by
    intro x
    -- x : ℝ
    -- ⊢ f x ≤ a
    have h3a : ¬ f x > a := h2 x
    show f x ≤ a
    exact le_of_not_gt h3a
  have h4 : FnUb f a := h3
  have h5 : ∃ b, FnUb f b := ⟨a, h4⟩
  have h6 : FnHasUb f := h5
  show False
  exact h h6

-- 2ª demostración
-- ===============

example
  (h : ¬FnHasUb f)
  : ∀ a, ∃ x, f x > a :=
by
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, f x > a
  by_contra h1
  -- h1 : ¬∃ x, f x > a
  -- ⊢ False
  apply h
  -- ⊢ FnHasUb f
  use a
  -- ⊢ FnUb f a
  intro x
  -- x : ℝ
  -- ⊢ f x ≤ a
  apply le_of_not_gt
  -- ⊢ ¬f x > a
  intro h2
  -- h2 : f x > a
  -- ⊢ False
  apply h1
  -- ⊢ ∃ x, f x > a
  use x
  -- ⊢ f x > a
  exact h2

-- 3ª demostración
-- ===============

example
  (h : ¬FnHasUb f)
  : ∀ a, ∃ x, f x > a :=
by
  unfold FnHasUb at h
  -- h : ¬∃ a, FnUb f a
  unfold FnUb at h
  -- h : ¬∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- ∀ (a : ℝ), ∃ x, f x > a
  exact h

-- 4ª demostración
-- ===============

example
  (h : ¬FnHasUb f)
  : ∀ a, ∃ x, f x > a :=
by
  simp only [FnHasUb, FnUb] at h
  -- h : ¬∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- ∀ (a : ℝ), ∃ x, f x > a
  exact h

-- 5ª demostración
-- ===============

example
  (h : ¬FnHasUb f) :
  ∀ a, ∃ x, f x > a :=
by
  contrapose h
  -- h : ¬∀ (a : ℝ), ∃ x, f x > a
  -- ⊢ ¬¬FnHasUb f
  push_neg at *
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  -- ⊢ FnHasUb f
  exact h

-- 6ª demostración
-- ===============

example
  (h : ¬FnHasUb f) :
  ∀ a, ∃ x, f x > a :=
by
  contrapose! h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  -- ⊢ FnHasUb f
  exact h

-- Comentario: La táctica (contrapose! h) aplica el contrapositivo entre
-- la hipótesis h y el objetivo; es decir, si (h : P) y el objetivo es Q
-- entonces cambia la hipótesis a (h : ¬Q) el objetivo a ¬P aplicando
-- simplificaciones en ambos.

-- Lemas usados
-- ============

-- variable {α : Type _}
-- variable (P : α → Prop)
-- #check (forall_not_of_not_exists : (¬∃ x, P x) → ∀ x, ¬P x)
--
-- variable (a b : ℝ)
-- #check (le_of_not_gt : ¬a > b → a ≤ b)
