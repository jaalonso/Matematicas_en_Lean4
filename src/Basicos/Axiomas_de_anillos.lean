-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de anillos.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar R como un tipo sobre los anillos.
-- ----------------------------------------------------------------------

variable (R : Type _) [Ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Comprobar que R verifica los axiomas de los anillos.
-- ----------------------------------------------------------------------

variable (a b c : R)
#check (add_assoc a b c : a + b + c = a + (b + c))
#check (add_comm a b : a + b = b + a)
#check (zero_add a :  0 + a = a)
#check (neg_add_cancel a : -a + a = 0)
#check (mul_assoc a b c : a * b * c = a * (b * c))
#check (mul_one a : a * 1 = a)
#check (one_mul a : 1 * a = a)
#check (mul_add a b c : a * (b + c) = a * b + a * c)
#check (add_mul a b c : (a + b) * c = a * c + b * c)
