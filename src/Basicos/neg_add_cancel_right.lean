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
  (a + b) + -b = a + (b + -b) := by rw [add_assoc]
             _ = a + 0        := by rw [add_right_neg]
             _ = a            := by rw [add_zero]

-- 2ª demostración
-- ===============

example : (a + b) + -b = a :=
by
  rw [add_assoc]
  -- ⊢ a + (b + -b) = a
  rw [add_right_neg]
  -- ⊢ a + 0 = a
  rw [add_zero]

-- 3ª demostración
-- ===============

example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Cerrar la teoría MyRing
-- ----------------------------------------------------------------------

end MyRing
