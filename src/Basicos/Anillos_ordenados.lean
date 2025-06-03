-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de los anillos ordenados.
--    2. Declarar R como un tipo sobre los anillos ordenados.
--    3. Declarar a y b como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Order.Ring.Defs                                  -- 1
variable {R : Type _} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] -- 2
variable (a b c : R)                                                    -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    @add_le_add_left R _ a b
--    @mul_pos R _ a b
--    zero_ne_one
--    @mul_nonneg R _ a b
-- ----------------------------------------------------------------------

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check (zero_ne_one : 0 ≠ 1)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
