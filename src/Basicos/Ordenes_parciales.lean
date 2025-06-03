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
-- Ejercicio 2. Calcular los tipos de las siguientes expresiones
--    x ≤ y
--    le_refl x
--    @le_trans α _ x y z
-- ----------------------------------------------------------------------

-- #check x ≤ y
-- #check le_refl x
-- #check @le_trans α _ x y z
-- #check @le_antisymm α _ x y

-- Comentario: Al colocar el cursor sobre check se obtiene
#check (x ≤ y : Prop)
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- Nota: Las letras griegas se escriben con \a, \b, ...
