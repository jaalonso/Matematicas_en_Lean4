-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a como variable sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs -- 1
import Mathlib.Tactic
namespace MyRing                 -- 2
variable {R : Type _} [Ring R]   -- 3
variable (a : R)                 -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    1 + 1 = 2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por cálculo.

-- Demostración con Lean4
-- ======================

theorem one_add_one_eq_two : 1 + 1 = (2 : R) :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    2 * a = a + a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    2·a = (1 + 1)·a    [por la definición de 2]
--        = 1·a + 1·a    [por la distributiva]
--        = a + a        [por producto con uno]

-- Demostración con Lean4
-- ======================

theorem two_mul : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   := by rw [one_add_one_eq_two]
      _ = 1 * a + 1 * a := by rw [add_mul]
      _ = a + a         := by rw [one_mul]

end MyRing
