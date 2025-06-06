-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los números reales tienen la siguiente
-- propiedad
--    (c * b) * a = b * (a * c)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    (c * b) * a
--    = (b * c) * a    [por la conmutativa]
--    = b * (c * a)    [por la asociativa]
--    = b * (a * c)    [por la conmutativa]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

-- 1ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a
    = (b * c) * a := by rw [mul_comm c b]
  _ = b * (c * a) := by rw [mul_assoc]
  _ = b * (a * c) := by rw [mul_comm c a]

-- 2ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
by
  rw [mul_comm c b]
  -- ⊢ (b * c) * a = b * (a * c)
  rw [mul_assoc]
  -- ⊢ b * (c * a) = b * (a * c)
  rw [mul_comm c a]

-- 3ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
by ring

-- Lemas usados
-- ============

#check (mul_comm a b : a * b = b * a)
#check (mul_assoc a b c : (a * b) * c = a * (b * c))
