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

example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by exact (add_mul 0 0 a).symm
                     _ = 0 * a       := congrArg (. * a) (add_zero 0)
                     _ = 0 * a + 0   := by exact (add_zero (0 * a)).symm
  exact add_left_cancel h

-- 2ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    by rw [←add_mul]
       -- ⊢ (0 + 0) * a = 0 * a + 0
       rw [add_zero]
       -- ⊢ 0 * a = 0 * a + 0
       rw [add_zero]
  rw [add_left_cancel h]

-- 3ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    by rw [←add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

-- 4ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by simp
                     _ = 0 * a       := by simp
                     _ = 0 * a + 0   := by simp
  simp

-- 5ª demostración
-- ===============

example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 := by simp
  simp

-- 6ª demostración
-- ===============

example : 0 * a = 0 :=
by simp

-- Lemas usados
-- ============

variable (b c : R)
variable (f : R → R)
#check (add_left_cancel : a + b = a + c → b = c)
#check (add_mul a b c : (a + b) * c = a * c + b * c)
#check (add_zero a : a + 0 = a)
#check (congrArg f : a = b → f a = f b)

end MyRing
