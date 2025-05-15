-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función identidad no está acotada
-- superiormente.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usamos el lema de ejercicio anterior (que afirma que si para cada a,
-- existe un x tal que f x > a, entonces f no tiene cota superior) basta
-- demostrar que
--    (∀a ∈ ℝ)(∃x ∈ ℝ) [x > a]
-- Sea a ∈ ℝ. Entonces a + 1 > a y, por tanto, (∃x ∈ ℝ) [x > a].

-- Demostraciones con Lean4
-- ========================

import src.Logica.Funcion_no_acotada_superiormente

-- 1ª demostración
-- ===============

example : ¬ FnHasUb (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, x > a
  use a + 1
  -- ⊢ a + 1 > a
  linarith

-- 2ª demostración
-- ===============

example : ¬ FnHasUb (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, x > a
  exact ⟨a + 1, by linarith⟩

-- 3ª demostración
-- ===============

example : ¬ FnHasUb (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  exact fun a ↦ ⟨a + 1, by linarith⟩
