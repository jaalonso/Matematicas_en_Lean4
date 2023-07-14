-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los números reales tienen la siguiente
-- propiedad
--    (c * b) * a = b * (a * c)
-- ---------------------------------------------------------------------

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]

-- Desarrollo de la prueba:
-- -----------------------

--    a b c : ℝ
--    ⊢ (c * b) * a = b * (a * c)
-- rw [mul_comm c b]
--    a b c : ℝ
--    ⊢ (b * c) * a = b * (a * c)
-- rw [mul_assoc]
--    a b c : ℝ
--    ⊢ b * (c * a) = b * (a * c)
-- rw [mul_comm c a]
--    goals accomplished

-- 2ª demostración
-- ===============

example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a
    = (b * c) * a := by rw [mul_comm c b]
  _ = b * (c * a) := by rw [mul_assoc]
  _ = b * (a * c) := by rw [mul_comm c a]

-- 3ª demostración
-- ===============

example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by ring