-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que lo función logarítmica es inyectiva sobre
-- los números positivos.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Real

example : InjOn log { x | x > 0 } :=
by
  intro x hx y hy
  -- x : ℝ
  -- hx : x ∈ {x | x > 0}
  -- y : ℝ
  -- hy : y ∈ {x | x > 0}
  -- ⊢ log x = log y → x = y
  intro e
  -- e : log x = log y
  -- ⊢ x = y
  calc
    x = exp (log x) := by rw [exp_log hx]
    _ = exp (log y) := by rw [e]
    _ = y           := by rw [exp_log hy]

-- Lemas usados
-- ============

variable (x : ℝ)
#check (exp_log : 0 < x → exp (log x) = x)
