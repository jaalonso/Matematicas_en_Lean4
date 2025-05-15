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
  have h1 : -a + (a + b) = -a + 0 := congrArg (-a + .) h
  have h2 : -a + (a + b) = b := neg_add_cancel_left a b
  have h3 : -a + 0 = -a := add_zero (-a)
  rw [h2, h3] at h1
  -- h1 : b = -a
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

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Por la suma con cero se tiene
--    0 + 0 = 0
-- Aplicándole la propiedad
--    ∀ a b ∈ R, a + b = 0 → -a = b
-- se obtiene
--    -0 = 0

-- 2ª demostración en LN
-- =====================

-- Puesto que
--    ∀ a b ∈ R, a + b = 0 → -a = b
-- basta demostrar que
--    0 + 0 = 0
-- que es cierta por la suma con cero.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración (basada en la 1ª en LN)
example : (-0 : R) = 0 :=
by
  have h1 : (0 : R) + 0 = 0 := add_zero 0
  show (-0 : R) = 0
  exact neg_eq_of_add_eq_zero h1

-- 2ª demostración (basada en la 2ª en LN)
theorem neg_zero : (-0 : R) = 0 :=
by
  apply neg_eq_of_add_eq_zero
  -- ⊢ 0 + 0 = 0
  rw [add_zero]

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--     -(-a) = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia de las siguiente propiedades demostradas en
-- ejercicios anteriores:
--    ∀ a b ∈ R, a + b = 0 → -a = b
--    ∀ a ∈ R, -a + a = 0

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example : -(-a) = a :=
by
  have h1 : -a + a = 0 := add_left_neg a
  show -(-a) = a
  exact neg_eq_of_add_eq_zero h1

-- 2ª demostración
theorem neg_neg : -(-a) = a :=
by
  apply neg_eq_of_add_eq_zero
  -- ⊢ -a + a = 0
  rw [add_left_neg]

end MyRing
