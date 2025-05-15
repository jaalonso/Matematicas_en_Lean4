import Mathlib.Data.Real.Basic                                               -- 1

-- ---------------------------------------------------------------------
-- Ejercicio 1. Declarar x como variable implícita sobre los reales.
-- ----------------------------------------------------------------------

variable {x : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ∃a, x < a
-- entonces
--    ∃b, x < b * 2
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : ∃a, x < a)
  : ∃b, x < b * 2 :=
by
  rcases h with ⟨a, hxa⟩
  -- a : ℝ
  -- hxa : x < a
  use a / 2
  -- ⊢ x < a / 2 * 2
  calc x < a         := hxa
       _ = a / 2 * 2 := (div_mul_cancel a two_ne_zero).symm

-- Comentario: Se han usado los lemas
-- + div_mul_cancel a : b ≠ 0 → a / b * b = a
-- + two_ne_zero : 2 ≠ 0

-- 2ª demostración
-- ===============

example
  (h : ∃a, x < a)
  : ∃b, x < b * 2 :=
by
  rcases h with ⟨a, hxa⟩
  -- a : ℝ
  -- hxa : x < a
  use a / 2
  -- ⊢ x < a / 2 * 2
  linarith
