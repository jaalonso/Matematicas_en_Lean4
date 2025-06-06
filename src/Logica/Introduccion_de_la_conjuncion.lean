-- ---------------------------------------------------------------------
-- Ejercicio. Sean x e y dos números tales que
--    x ≤ y
--    ¬ y ≤ x
-- entonces
--    x ≤ y ∧ x ≠ y
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Como la conclusión es una conjunción, tenemos que desmostrar sus dos
-- partes. La primera parte (x ≤ y) coincide con la hipótesis. Para
-- demostrar la segunda parte (x ≠ y), supongamos que x = y; entonces
-- y ≤ x en contradicción con la segunda hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    have h4 : y ≤ x := h3.symm.le
    show False
    exact h2 h4

-- Comentario: La táctica constructor, cuando el objetivo es una
-- conjunción (P ∧ Q), aplica la regla de introducción de la conjunción;
-- es decir, sustituye el objetivo por dos nuevos subobjetivos (P y Q).

-- 2ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    exact h2 (h3.symm.le)

-- 3ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
⟨h1, fun h3 ↦ h2 (h3.symm.le)⟩

-- Comentario: La notación ⟨h0, h1⟩, cuando el objetivo es una conjunción
-- (P ∧ Q), aplica la regla de introducción de la conjunción donde h0 es
-- una prueba de P y h1 de Q.

-- 4ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    apply h2
    -- ⊢ y ≤ x
    rw [h3]

-- 5ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    exact h2 (by rw [h3])

-- 6ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
⟨h1, fun h ↦ h2 (by rw [h])⟩

-- 7ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  have h3 : x ≠ y
  . contrapose! h2
    -- ⊢ y ≤ x
    rw [h2]
  exact ⟨h1, h3⟩

-- 8ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by aesop
