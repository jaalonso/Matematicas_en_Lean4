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
variable (a b : R)

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

example : -a + (a + b) = b :=
calc -a + (a + b) = (-a + a) + b := by exact (add_assoc (-a) a b).symm
                _ = 0 + b        := congrArg (. + b) (neg_add_cancel a)
                _ = b            := zero_add b

-- 2ª demostración
-- ===============

example
  : -a + (a + b) = b :=
by
  rw [←add_assoc]
  -- ⊢ (-a + a) + b = b
  rw [neg_add_cancel]
  -- ⊢ 0 + b = b
  rw [zero_add]

-- 3ª demostración
-- ===============

theorem neg_add_cancel_left
  : -a + (a + b) = b :=
by
  rw [←add_assoc, neg_add_cancel, zero_add]

-- Lemas usados
-- ============

variable (c : R)
#check (add_assoc a b c : a + b + c = a + (b + c))
#check (neg_add_cancel a : -a + a = 0)
#check (zero_add a :  0 + a = a)

-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre MyRing.
-- ----------------------------------------------------------------------

end MyRing
