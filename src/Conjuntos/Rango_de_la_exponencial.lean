-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el rango de la función exponencial es el
-- conjunto de los números positivos,
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Real

example : range exp = { y | y > 0 } := by
  ext y
  -- y : ℝ
  -- ⊢ y ∈ range rexp ↔ y ∈ {y | y > 0}
  constructor
  · -- ⊢ y ∈ range rexp → y ∈ {y | y > 0}
    rintro ⟨x, rfl⟩
    -- x : ℝ
    -- ⊢ rexp x ∈ {y | y > 0}
    apply exp_pos
  . -- ⊢ y ∈ {y | y > 0} → y ∈ range rexp
    intro hy
    -- hy : y ∈ {y | y > 0}
    -- ⊢ y ∈ range rexp
    use log y
    -- ⊢ rexp (log y) = y
    rw [exp_log hy]

-- Lemas usados
-- ============

variable (x : ℝ)
#check (exp_log : 0 < x → exp (log x) = x)
