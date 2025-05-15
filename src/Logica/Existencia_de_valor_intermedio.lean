-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que hay algún número real entre 2 y 3.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 :=
    by norm_num
  show ∃ x : ℝ, 2 < x ∧ x < 3
  exact Exists.intro (5 / 2) h

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 :=
    by norm_num
  show ∃ x : ℝ, 2 < x ∧ x < 3
  exact ⟨5 / 2, h⟩

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  -- ⊢ 2 < 5 / 2 ∧ 5 / 2 < 3
  norm_num

-- 4ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩
