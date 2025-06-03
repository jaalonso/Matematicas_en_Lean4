-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a como variable sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs -- 1
namespace MyRing                 -- 2
variable {R : Type _} [Ring R]   -- 3
variable (a : R)                 -- 4

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--     a - a = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    a - a = a + -a    [por definición de resta]
--          = 0         [por suma con opuesto]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : a - a = 0 :=
calc
  a - a = a + -a := by exact (sub_eq_add_neg a a)
      _ = 0      := add_neg_cancel a

-- 2ª demostración
-- ===============

theorem self_sub : a - a = 0 :=
calc
  a - a = a + -a := by rw [sub_eq_add_neg a a]
      _ = 0      := by rw [add_neg_cancel]

-- Lemas usados
-- ============

variable (b : R)
#check (add_neg_cancel a : a + -a = 0)
#check (sub_eq_add_neg a b : a - b = a + -b)

end MyRing
