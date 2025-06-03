-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de retículos
--    2. Declarar α como un tipo sobre los retículos.
--    3. x, y y z como variables sobre α.
-- ----------------------------------------------------------------------

import Mathlib.Order.Lattice               -- 1
variable {α : Type _} [DistribLattice α]   -- 2
variable (x y z : α)                       -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    @inf_sup_left α _ x y z
--    @inf_sup_right α _ x y z
--    @sup_inf_left α _ x y z
--    @sup_inf_right α _ x y z
-- ----------------------------------------------------------------------

--- #check @inf_sup_left α _ x y z
--- #check @inf_sup_right α _ x y z
--- #check @sup_inf_left α _ x y z
--- #check @sup_inf_right α _ x y z

-- Comentario: Al situar el cursor sobre check se obtiene
#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left x y z : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
