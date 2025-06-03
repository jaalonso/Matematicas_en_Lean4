-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre MyRing.
-- ----------------------------------------------------------------------

namespace MyRing

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declara R una variable sobre anillos.
-- ----------------------------------------------------------------------

variable {R : Type _} [Ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Declarar a y b como variables sobre R.
-- ----------------------------------------------------------------------

variable (a b : R)

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    (a + b) + -b = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    (a + b) + -b = a + (b + -b)    [por la asociativa]
--               _ = a + 0           [por suma con opuesto]
--               _ = a               [por suma con cero]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

theorem neg_add_cancel_right : (a + b) + -b = a :=
calc
  (a + b) + -b = a + (b + -b) := by exact add_assoc a b (-b)
             _ = a + 0        := congrArg (a + .) (add_neg_cancel b)
             _ = a            := add_zero a

-- 2ª demostración
-- ===============

example : (a + b) + -b = a :=
by
  rw [add_assoc]
  -- ⊢ a + (b + -b) = a
  rw [add_neg_cancel]
  -- ⊢ a + 0 = a
  rw [add_zero]

-- 3ª demostración
-- ===============

example : (a + b) + -b = a :=
by rw [add_assoc, add_neg_cancel, add_zero]

-- Lemas usados
-- ============

variable (c : R)
variable (f : R → R)
#check (add_assoc a b c : a + b + c = a + (b + c))
#check (add_zero a : a + 0 = a)
#check (add_neg_cancel a : a + -a = 0)
#check (congrArg f : a = b → f a = f b)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Cerrar la teoría MyRing
-- ----------------------------------------------------------------------

end MyRing
