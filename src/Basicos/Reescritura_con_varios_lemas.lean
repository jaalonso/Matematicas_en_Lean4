-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d, e y f son números reales
-- tales que
--    a * b = c * d
--    e = f
-- entonces
--    a * (b * e) = c * (d * f)
-- ---------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  rw [h2]
  -- ⊢ a * (b * f) = c * (d * f)
  rw [←mul_assoc]
  -- ⊢ (a * b) * f = c * (d * f)
  rw [h1]
  -- ⊢ (c * d) * f = c * (d * f)
  rw [mul_assoc]

-- 2ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  rw [h2, ←mul_assoc, h1, mul_assoc]

-- Comentario: Colocando el cursor en las comas se observa el progreso
-- en la ventana de objetivos.

-- 3ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc
  a * (b * e) = a * (b * f) := by rw [h2]
            _ = (a * b) * f := by rw [←mul_assoc]
            _ = (c * d) * f := by rw [h1]
            _ = c * (d * f) := by rw [mul_assoc]
