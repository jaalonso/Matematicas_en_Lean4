-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función suprayectiva de ℝ en ℝ,
-- entonces existe un x tal que (f x)^2 = 9.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Al ser f suprayectiva, existe un y tal que f(y) = 3. Por tanto,
-- f(y)² = 9.

-- Demostración con Lean4
-- ======================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Function

example
  {f : ℝ → ℝ}
  (h : Surjective f)
  : ∃ x, (f x)^2 = 9 :=
by
  rcases h 3 with ⟨y, hy⟩
  -- y : ℝ
  -- hy : f y = 3
  use y
  -- ⊢ (f y) ^ 2 = 9
  rw [hy]
  -- ⊢ 3 ^ 2 = 9
  norm_num
