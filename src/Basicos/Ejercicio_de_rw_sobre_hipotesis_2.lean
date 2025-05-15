-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c y d son números reales tales
-- que
--    c = b * a - d
--    d = a * b
-- entonces
--    c = 0
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    c = ba - d     [por la primera hipótesis]
--      = ab - d     [por la conmutativa]
--      = ab - ab    [por la segunda hipótesis]
--      = 0

-- Demostraciones en Lean4
-- =======================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
-- ===============

example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
calc
  c = b * a - d     := by rw [h1]
  _ = a * b - d     := by rw [mul_comm]
  _ = a * b - a * b := by rw [h2]
  _ = 0             := by rw [sub_self]

-- 2ª demostración
-- ===============

example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
by
  rw [h1]
  -- ⊢ b * a - d = 0
  rw [mul_comm]
  -- ⊢ a * b - d = 0
  rw [h2]
  -- ⊢ a * b - a * b = 0
  rw [sub_self]

-- Comentario: El último lema se puede encontrar escribiendo previamente
--    exact?
-- y afirma que
--    ∀ (a : G), a - a = 0
