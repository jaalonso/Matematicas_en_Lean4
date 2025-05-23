-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de grupos
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Group.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar A como un tipo sobre grupos aditivos.
-- ----------------------------------------------------------------------

variable (A : Type _) [AddGroup A]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Comprobar que A verifica los axiomas de los grupos
-- ----------------------------------------------------------------------

#check (add_assoc :    ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add :     ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
