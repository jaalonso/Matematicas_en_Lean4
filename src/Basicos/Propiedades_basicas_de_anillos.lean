-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombres myRing (para evitar
-- conflictos con los nombres).
-- ----------------------------------------------------------------------

namespace myRing

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar R como una variable implícita sobre los anillos.
-- ----------------------------------------------------------------------

variable {R : Type _} [Ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar a como una variable sobre R.
-- ----------------------------------------------------------------------

variable (a : R)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    a + 0 = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a + 0 = 0 + a    [por la conmutativa de la suma]
--          = a        [por el axioma del cero por la izquierda]

-- 1ª demostración
-- ===============

example : a + 0 = a :=
calc a + 0
     = 0 + a := add_comm a 0
   _ = a     := zero_add a

-- 2ª demostración
-- ===============

example : a + 0 = a :=
by
  rw [add_comm]
  -- ⊢ 0 + a = a
  rw [zero_add]

-- 3ª demostración
-- ===============

theorem add_zero : a + 0 = a :=
by rw [add_comm, zero_add]

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    a + -a = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a + -a = -a + a    [por la conmutativa de la suma]
--           = 0         [por el axioma de inverso por la izquierda]

-- 1ª demostración
-- ===============

example : a + -a = 0 :=
calc a + -a
     = -a + a := add_comm a (-a)
   _ = 0      := neg_add_cancel a

-- 2ª demostración
-- ===============

example : a + -a = 0 :=
by
  rw [add_comm]
  -- ⊢ -a + a = 0
  rw [neg_add_cancel]

-- 3ª demostración
-- ===============

theorem add_right_neg : a + -a = 0 :=
by rw [add_comm, neg_add_cancel]

-- Lemas usados
-- ============

variable (a b : R)
#check (add_comm a b : a + b = b + a)
#check (neg_add_cancel a : -a + a = 0)
#check (zero_add a : 0 + a = a)

-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre myRing.
-- ----------------------------------------------------------------------

end myRing

-- ---------------------------------------------------------------------
-- Ejercicio 7. Calcular el tipo de @myRing.add_zero.
-- ----------------------------------------------------------------------

#check @myRing.add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    myRing.add_zero : ∀ {R : Type u_1} [inst : Ring R] (a : R),
--                      a + 0 = a

-- ---------------------------------------------------------------------
-- Ejercicio 8. Calcular el tipo de @add_zero.
-- ----------------------------------------------------------------------

#check @add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    @add_zero : ∀ {M : Type u_1} [inst : AddZeroClass M] (a : M), a + 0 = a
