-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d, e y f son números reales
-- tales que
--    a * b = c * d
--    e = f
-- Entonces,
--    a * (b * e) = c * (d * f)
-- ---------------------------------------------------------------------

import Mathlib.Tactic
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
  rw [←mul_assoc]
  rw [h1]
  rw [mul_assoc]

-- Comentario: La táctica (rw h2) reescribe el objetivo con la igualdad
-- de la nipótesis h2.

-- Desarrollo de la prueba
-- -----------------------

-- inicio
--    a b c d e f : ℝ,
--    h1 : a * b = c * d,
--    h2 : e = f
--    ⊢ a * (b * e) = c * (d * f)
-- rw [h2]
--    S
--    ⊢ a * (b * f) = c * (d * f)
-- rw [←mul_assoc]
--    S
--    ⊢ (a * b) * f = c * (d * f)
-- rw [h1]
--    S
--    ⊢ (c * d) * f = c * (d * f)
-- rw [mul_assoc]
--    goals accomplished
--
-- En el desarrollo anterior, S es el conjunto de las hipótesis; es
-- decir,
--    S = {a b c d e f : ℝ,
--         h1 : a * b = c * d,
--         h2 : e = f}

-- 2ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc
  a * (b * e)
    = a * (b * f) := by rw [h2]
  _ = (a * b) * f := by rw [←mul_assoc]
  _ = (c * d) * f := by rw [h1]
  _ = c * (d * f) := by rw [mul_assoc]

-- 3ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  simp [*, ←mul_assoc]
