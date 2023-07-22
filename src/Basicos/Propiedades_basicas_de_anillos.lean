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
     = 0 + a := by rw [add_comm]
   _ = a     := by rw [zero_add]

-- 2ª demostración
-- ===============

example : a + 0 = a :=
by
  rw [add_comm]
  rw [zero_add]

-- El desarrollo de la prueba es
--
--    R : Type ?u.599
--    inst : Ring R
--    a : R
--    ⊢ a + 0 = a
-- rw [add_comm]
--    ⊢ 0 + a = a
-- rw [zero_add]
--    goals accomplished

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
     = -a + a := by rw [add_comm]
   _ = 0      := by rw [add_left_neg]

-- 2ª demostración
-- ===============

example : a + -a = 0 :=
by
  rw [add_comm]
  rw [add_left_neg]

-- El desarrollo de la prueba es
--
--    R : Type ?u.1925
--    inst : Ring R
--    a : R
--    ⊢ a + -a = 0
-- rw [add_comm]
--    ⊢ -a + a = 0
-- rw [add_left_neg]
--    no goals

-- 3ª demostración
-- ===============

theorem add_right_neg : a + -a = 0 :=
by rw [add_comm, add_left_neg]

-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre myRing.
-- ----------------------------------------------------------------------

end myRing

-- ---------------------------------------------------------------------
-- Ejercicio 7. Calcular el tipo de @myRing.add_zero.
-- ----------------------------------------------------------------------

#check @myRing.add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    myRing.add_zero : ∀ {R : Type u_1} [_inst_1 : Ring R] (a : R),
--                      a + 0 = a

-- ---------------------------------------------------------------------
-- Ejercicio 8. Calcular el tipo de @add_zero.
-- ----------------------------------------------------------------------

#check @add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    @add_zero : ∀ {M : Type u_1} [inst : AddZeroClass M] (a : M),
--                a + 0 = a
