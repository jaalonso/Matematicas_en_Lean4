-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de órdenes
--    2. Declarar α como un tipo sobre los órdenes parciales
--    3. x, y y z como variables sobre α.
-- ----------------------------------------------------------------------

import Mathlib.Order.Basic                -- 1
variable {α : Type _} [PartialOrder α]    -- 2
variable (x y z : α)                      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    x < y
--    lt_irrefl x
--    lt_trans
--    lt_of_le_of_lt
--    lt_of_lt_of_le
--    lt_iff_le_and_ne
-- ----------------------------------------------------------------------

#check (x < y : Prop)
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)
#check (lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y)
