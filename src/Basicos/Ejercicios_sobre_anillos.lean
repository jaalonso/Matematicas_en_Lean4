-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a y b como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace MyRing

variable {R : Type _} [Ring R]
variable {a b : R}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    a + b = 0
-- entonces
--    -a = b
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- ---------------------

-- Por la siguiente cadena de igualdades
--    -a = -a + 0          [por suma cero]
--       = -a + (a + b)    [por hipótesis]
--       = b               [por cancelativa]

-- 2ª demostración en LN
-- ---------------------

-- Sumando -a a ambos lados de la hipótesis, se tiene
--    -a + (a + b) = -a + 0
-- El término de la izquierda se reduce a b (por la cancelativa) y el de
-- la derecha a -a (por la suma con cero). Por tanto, se tiene
--     b = -a
-- Por la simetría de la igualdad, se tiene
--     -a = b

-- Demostraciones con Lean 4
-- =========================

-- 1ª demostración
-- ---------------

theorem neg_eq_of_add_eq_zero
  (h : a + b = 0)
  : -a = b :=
calc
  -a = -a + 0       := by rw [add_zero]
   _ = -a + (a + b) := by rw [h]
   _ = b            := by rw [neg_add_cancel_left]

-- 2ª demostración
-- ---------------

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a = -a + 0       := by simp
   _ = -a + (a + b) := by rw [h]
   _ = b            := by simp

-- 3ª demostración
-- ---------------

example
  (h : a + b = 0)
  : -a = b :=
by
  have h1 : -a + (a + b) = -a + 0 := congrArg (HAdd.hAdd (-a)) h
  have h2 : -a + (a + b) = b := neg_add_cancel_left a b
  have h3 : -a + 0 = -a := add_zero (-a)
  rw [h2, h3] at h1
  exact h1.symm

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--     (a + b) + -b = a
-- -------------------------------------------------------------------------

theorem neg_add_cancel_right : (a + b) + -b = a :=
calc
  (a + b) + -b = a + (b + -b) := by rw [add_assoc]
             _ = a + 0        := by rw [add_right_neg]
             _ = a            := by rw [add_zero]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    a + b = 0
-- entonces
--    a = -b
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- ---------------------

-- Por la siguiente cadena de igualdades
--    a = (a + b) + -b    [por la concelativa]
--      = 0 + -b          [por la hipótesis]
--      = -b              [por la suma con cero]

-- 2ª demostración en LN
-- ---------------------

-- Sumando -a a ambos lados de la hipótesis, se tiene
--    (a + b) + -b = 0 + -b
-- El término de la izquierda se reduce a a (por la cancelativa) y el de
-- la derecha a -b (por la suma con cero). Por tanto, se tiene
--     a = -b

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ---------------

theorem eq_neg_of_add_eq_zero
  (h : a + b = 0)
  : a = -b :=
calc
  a = (a + b) + -b := by rw [neg_add_cancel_right]
  _ = 0 + -b       := by rw [h]
  _ = -b           := by rw [zero_add]

-- 2ª demostración
-- ---------------

example
  (h : a + b = 0)
  : a = -b :=
calc
  a = (a + b) + -b := by simp
  _ = 0 + -b       := by rw [h]
  _ = -b           := by simp

-- 3ª demostración
-- ---------------

example
  (h : a + b = 0)
  : a = -b :=
by
  have h1 : (a + b) + -b = 0 + -b := by rw [h]
  have h2 : (a + b) + -b = a := neg_add_cancel_right
  have h3 : 0 + -b = -b := zero_add (-b)
  rwa [h2, h3] at h1

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    -0 = 0
-- ----------------------------------------------------------------------

theorem neg_zero : (-0 : R) = 0 :=
by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

-- El desarrollo de la prueba es
--
--    R : Type u_1
--    inst : Ring R
--    ⊢ -0 = 0
-- apply neg_eq_of_add_eq_zero
--    ⊢ 0 + 0 = 0
-- rw [add_zero]
--    goals accomplished

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--     -(-a) = a
-- ----------------------------------------------------------------------

theorem neg_neg : -(-a) = a :=
by
  apply neg_eq_of_add_eq_zero
  rw [add_left_neg]

-- El desarrollo de la prueba es
--
--    R : Type u_1
--    inst : Ring R
--    a : R
--    ⊢ - -a = a
-- apply neg_eq_of_add_eq_zero
--    ⊢ -a + a = 0
-- rw [add_left_neg]
--    goals accomplished

end MyRing
