-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre MyRing
-- ----------------------------------------------------------------------

namespace MyRing

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar R como una variable sobre anillos.
-- ----------------------------------------------------------------------

variable {R : Type _} [Ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que para todo a, b ∈ R,
--    -a + (a + b) = b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    -a + (a + b) = (-a + a) + b [por la asociativa]
--                 = 0 + b        [por inverso por la izquierda]
--                 = b            [por cero por la izquierda]

-- 1ª demostración
-- ===============

example
  (a b : R)
  : -a + (a + b) = b :=
calc -a + (a + b) = (-a + a) + b := by rw [← add_assoc]
                _ = 0 + b        := by rw [add_left_neg]
                _ = b            := by rw [zero_add]

-- 2ª demostración
-- ===============

theorem neg_add_cancel_left
  (a b : R)
  : -a + (a + b) = b :=
by
  rw [←add_assoc]
  -- ⊢ (-a + a) + b = b
  rw [add_left_neg]
  -- ⊢ 0 + b = b
  rw [zero_add]

-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre MyRing.
-- ----------------------------------------------------------------------

end MyRing
