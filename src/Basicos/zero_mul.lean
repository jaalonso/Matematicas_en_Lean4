-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los anillos,
--    0 * a = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Basta aplicar la propiedad cancelativa a
--    0.a + 0.a = 0.a + 0
-- que se demuestra mediante la siguiente cadena de igualdades
--    0.a + 0.a = (0 + 0).a    [por la distributiva]
--              = 0.a          [por suma con cero]
--              = 0.a + 0      [por suma con cero]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace MyRing

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
-- ===============

example : a = a + 0 := (add_zero a).symm
example : a + 0 = a := add_zero a

example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by rw [add_mul]
                     _ = 0 * a       := by rw [add_zero]
                     _ = 0 * a + 0   := by rw [add_zero]
  rw [add_left_cancel h]

-- 2ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    by rw [←add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

-- 3ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by simp
                     _ = 0 * a       := by simp
                     _ = 0 * a + 0   := by simp
  simp

-- 4ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 := by simp
  simp

-- 5ª demostración
-- ===============

example : 0 * a = 0 :=
by simp

end MyRing
