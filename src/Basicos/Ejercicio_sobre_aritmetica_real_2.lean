-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los números reales tienen la siguiente
-- propiedad
--    a * (b * c) = b * (a * c)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    a(bc)
--    = (ab)c    [por la asociativa]
--    = (ba)c    [por la conmutativa]
--    = b(ac)    [por la asociativa]

-- Demostraciones en Lean4
-- =======================

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example
  (a b c : ℝ)
  : a * (b * c) = b * (a * c) :=
calc
  a * (b * c)
    = (a * b) * c := by rw [←mul_assoc]
  _ = (b * a) * c := by rw [mul_comm a b]
  _ = b * (a * c) := by rw [mul_assoc]

-- 2ª demostración
-- ===============

example
  (a b c : ℝ)
  : a * (b * c) = b * (a * c) :=
by
  rw [←mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- Comentario. Con la táctica (rw [←e]) se aplica reescritura sustituyendo
-- el término derecho de la igualdad e por el izquierdo.

-- Desarrollo de la prueba
-- -----------------------

--    a b c : ℝ
--    ⊢ a * (b * c) = b * (a * c)
-- rw [←mul_assoc]
--    a b c : ℝ
--    ⊢ (a * b) * c = b * (a * c)
-- rw [mul_comm a b]
--    a b c : ℝ
--    ⊢ (b * a) * c = b * (a * c)
-- rw [mul_assoc]
--    goals accomplished

-- 3ª demostración
-- ===============

example
  (a b c : ℝ)
  : a * (b * c) = b * (a * c) :=
by ring
