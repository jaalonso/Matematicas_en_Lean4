-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de grupos
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Group.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar G como un tipo sobre grupos.
-- ----------------------------------------------------------------------

variable {G : Type _} [Group G]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Comprobar que G verifica los axiomas de los grupos
-- ----------------------------------------------------------------------

variable (a b c : G)
#check (mul_assoc a b c : a * b * c = a * (b * c))
#check (one_mul a : 1 * a = a)
#check (inv_mul_cancel a : a⁻¹ * a = 1)
