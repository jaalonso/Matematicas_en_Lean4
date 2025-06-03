-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d y e son números reales tales
-- que
--    a ≤ b
--    b < c
--    c ≤ d
--    d < e
-- entonces
--    a < e
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d e : ℝ)

-- 1ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by
  apply lt_of_le_of_lt h₀
  -- ⊢ b < e
  apply lt_trans h₁
  -- ⊢ c < e
  apply lt_of_le_of_lt h₂
  -- ⊢ d < e
  exact h₃

-- 2ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
calc
  a ≤ b := h₀
  _ < c := h₁
  _ ≤ d := h₂
  _ < e := h₃

-- 3ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by linarith

-- Lemas usados
-- ============

variable (x y z : ℝ)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_trans : x < y → y < z → x < z)
