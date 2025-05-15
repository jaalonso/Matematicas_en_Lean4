-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--     abs_add
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

#check abs_add

-- Comentario: Colocando el cursor sobre check se obtiene
--    abs_add.{u_1} {α : Type u_1} [inst : LinearOrderedAddCommGroup α]
--      (a b : α) : |a + b| ≤ |a| + |b|
