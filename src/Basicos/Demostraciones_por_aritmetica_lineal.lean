-- ---------------------------------------------------------------------
-- Ejercicio 1. Sean a, b, c, d y e números reales. Demostrar que si
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

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e)
  : a < e :=
by linarith

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    2 * a ≤ 3 * b
--    1 ≤ a
--    d = 2
-- entonces
--    d + a ≤ 5 * b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de desigualdades
--    d + a = 2 + a      [por la hipótesis 3 (d = 2)]
--          ≤ 2·a + a    [por la hipótesis 2 (1 ≤ a)]
--          = 3·a
--          ≤ 9/2·b      [por la hipótesis 1 (2·a ≤ 3·b)]
--          ≤ 5·b

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
calc
  c + a = 2 + a     := by rw [h3]
      _ ≤ 2 * a + a := by linarith only [h2]
      _ = 3 * a     := by linarith only []
      _ ≤ 9/2 * b   := by linarith only [h1]
      _ ≤ 5 * b     := by linarith

-- 2ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
by linarith
