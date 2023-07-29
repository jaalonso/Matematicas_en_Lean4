-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre MyRing.
-- ----------------------------------------------------------------------

namespace MyRing

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declara R una variable sobre anillos.
-- ----------------------------------------------------------------------

variable {R : Type _} [Ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

variable {a b c : R}

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    a + b = a + c
-- entonces
--    b = c
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- ======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    b = 0 + b           [por suma con cero]
--      = (-a + a) + b    [por suma con opuesto]
--      = -a + (a + b)    [por asociativa]
--      = -a + (a + c)    [por hipótesis]
--      = (-a + a) + c    [por asociativa]
--      = 0 + c           [por suma con opuesto]
--      = c               [por suma con cero]

-- 2ª demostración en LN
-- =====================

-- Por la siguiente cadena de implicaciones
--    a + b = a + c
--    ==> -a + (a + b) = -a + (a + c)     [sumando -a]
--    ==>  (-a + a) + b = (-a + a) + c    [por la asociativa]
--    ==>  0 + b = 0 + b                  [suma con opuesto]
--    ==>  b = c                          [suma con cero]

-- 3ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    b = -a + (a + b)
--      = -a + (a + c)   [por la hipótesis]
--      = c

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

theorem add_left_cancel
  (h : a + b = a + c)
  : b = c :=
calc
  b = 0 + b        := by rw [zero_add]
  _ = (-a + a) + b := by rw [add_left_neg]
  _ = -a + (a + b) := by rw [add_assoc]
  _ = -a + (a + c) := by rw [h]
  _ = (-a + a) + c := by rw [←add_assoc]
  _ = 0 + c        := by rw [add_left_neg]
  _ = c            := by rw [zero_add]

-- 2ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
by
  have h1 : -a + (a + b) = -a + (a + c) :=
    congrArg (HAdd.hAdd (-a)) h
  clear h
  rw [← add_assoc] at h1
  rw [add_left_neg] at h1
  rw [zero_add] at h1
  rw [← add_assoc] at h1
  rw [add_left_neg] at h1
  rw [zero_add] at h1
  exact h1

-- El desarrollo de la prueba es
--
--    R : Type ?u.3961
--    inst : Ring R
--    a b c : R,
--    h : a + b = a + c
--    ⊢ b = c
-- have h1 : -a + (a + b) = -a + (a + c)
--    |    ⊢ -a + (a + b) = -a + (a + c) :=
--    |          congrArg (HAdd.hAdd (-a)) h
--    h : a + b = a + c,
--    h1 : -a + (a + b) = -a + (a + c)
--    ⊢ b = c
-- clear h
--    h1 : -a + (a + b) = -a + (a + c)
--    ⊢ b = c
-- rw [← add_assoc at h1]
--    h1 : -a + a + b = -a + (a + c)
--    ⊢ b = c
-- rw [add_left_neg at h1]
--    h1 : 0 + b = -a + (a + c)
--    ⊢ b = c
-- rw [zero_add at h1]
--    h1 : b = -a + (a + c)
--    ⊢ b = c
-- rw [← add_assoc at h1]
--    h1 : b = -a + a + c
--    ⊢ b = c
-- rw [add_left_neg at h1]
--    h1 : b = 0 + c
--    ⊢ b = c
-- rw [zero_add at h1]
--    h1 : b = c
--    ⊢ b = c
-- exact h1
--    goals accomplished

-- 3ª demostración
-- ===============

lemma neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
by simp

example
  (h : a + b = a + c)
  : b = c :=
calc
  b = -a + (a + b) := by rw [neg_add_cancel_left a b]
  _ = -a + (a + c) := by rw [h]
  _ = c            := by rw [neg_add_cancel_left]

-- 4ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b]
  rw [h]
  rw [neg_add_cancel_left]

-- 5ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que si
--    a + b = c + b
-- entonces
--    a = c
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    a = a + 0           [por suma con cero]
--      = a + (b + -b)    [por suma con opuesto]
--      = (a + b) + -b    [por asociativa]
--      = (c + b) + -b    [por hipótesis]
--      = c + (b + -b)    [por asociativa]
--      = c + 0           [por suma con opuesto]
--      = c               [por suma con cero]

-- 2ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    a = (a + b) + -b
--      = (c + b) + -b    [por hipótesis]
--      = c

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración con Lean4
-- =========================

theorem add_right_cancel
  (h : a + b = c + b)
  : a = c :=
calc
  a = a + 0        := by rw [add_zero]
  _ = a + (b + -b) := by rw [add_right_neg]
  _ = (a + b) + -b := by rw [add_assoc]
  _ = (c + b) + -b := by rw [h]
  _ = c + (b + -b) := by rw [← add_assoc]
  _ = c + 0        := by rw [← add_right_neg]
  _ = c            := by rw [add_zero]

-- 2ª demostración con Lean4
-- =========================

lemma neg_add_cancel_right (a b : R) : (a + b) + -b = a :=
by simp

example
  (h : a + b = c + b)
  : a = c :=
calc
  a = (a + b) + -b := by rw [neg_add_cancel_right a b]
  _ = (c + b) + -b := by rw [h]
  _ = c            := by rw [neg_add_cancel_right]

-- 3ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← neg_add_cancel_right a b]
  rw [h]
  rw [neg_add_cancel_right]

-- 4ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← neg_add_cancel_right a b, h, neg_add_cancel_right]

-- ---------------------------------------------------------------------
-- Ejercicio 7. Cerrar el espacio de nombre MyRing.
-- ----------------------------------------------------------------------

end MyRing
