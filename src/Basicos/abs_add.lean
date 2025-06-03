-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--     abs_add
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

#check abs_add

-- Comentario: Colocando el cursor sobre check se obtiene
--    abs_add.{u_1} {G : Type u_1} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
--      (a b : G) : |a + b| ≤ |a| + |b|
