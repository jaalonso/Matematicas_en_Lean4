-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a y b como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs -- 1
namespace MyRing                 -- 2
variable {R : Type _} [Ring R]   -- 3
variable (a b : R)               -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a - b = a + -b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la definición de la resta.

-- Demostración en Lean4
-- =====================

-- 1ª demostración
theorem sub_eq_add_neg' : a - b = a + -b :=
-- by exact?
sub_eq_add_neg a b

end MyRing
