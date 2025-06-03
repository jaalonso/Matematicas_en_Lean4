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

variable (a b c : A)

#check (add_assoc a b c : a + b + c = a + (b + c))
#check (zero_add a : 0 + a = a)
#check (neg_add_cancel a : -a + a = 0)
