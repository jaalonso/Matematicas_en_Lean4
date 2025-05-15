-- ---------------------------------------------------------------------
-- Ejercicio. Importar las teorías:
-- + algebra.group_power de potencias en grupos
-- + tactic de tácticas
-- ----------------------------------------------------------------------

import Mathlib

-- ---------------------------------------------------------------------
-- Ejercicio. Declara R como una variable sobre dominios de integridad.
-- ----------------------------------------------------------------------

variable {R : Type _}  [CommRing R] [IsDomain R]

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar x e y como variables sobre R.
-- ----------------------------------------------------------------------

variable (x y : R)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
--    x^2 = 1
-- entonces
--    x = 1 ∨ x = -1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas
--    (∀ x ∈ ℝ)[x - x = 0]                                           (L1)
--    (∀ x, y ∈ ℝ)[xy = 0 → x = 0 ∨ y = 0]                           (L2)
--    (∀ x, y ∈ ℝ)[x - y = 0 ↔ x = y]                                (L3)
--    (∀ x, y ∈ ℝ)[x + y = 0 → x = -y]                               (L4)
--
-- Se tiene que
--    (x - 1)(x + 1) = x² - 1
--                   = 1 - 1      [por la hipótesis]
--                   = 0          [por L1]
-- y, por el lema L2, se tiene que
--    x - 1 = 0 ∨ x + 1 = 0
-- Acabaremos la demostración por casos.
--
-- Primer caso:
--   x - 1 = 0 ⟹ x = 1             [por L3]
--             ⟹ x = 1 ∨ x = -1
--
-- Segundo caso:
--   x + 1 = 0 ⟹ x = -1            [por L4]
--             ⟹ x = 1 ∨ x = -1

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by
  have h1 : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x^2 - 1 := by ring
                         _ = 1 - 1   := by rw [h]
                         _ = 0       := sub_self 1
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  . -- h3 : x - 1 = 0
    left
    -- ⊢ x = 1
    exact sub_eq_zero.mp h3
  . -- h4 : x + 1 = 0
    right
    -- ⊢ x = -1
    exact eq_neg_of_add_eq_zero_left h4

-- 2ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
sq_eq_one_iff.mp h

-- 3ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by aesop

-- Lemas usados
-- ============

-- #check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
-- #check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
-- #check (sq_eq_one_iff : x ^ 2 = 1 ↔ x = 1 ∨ x = -1)
-- #check (sub_eq_zero : x - y = 0 ↔ x = y)
-- #check (sub_self x : x - x = 0)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
--    x^2 = y^2
-- entonces
--    x = y ∨ x = -y
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas
--    (∀ x ∈ ℝ)[x - x = 0]                                           (L1)
--    (∀ x, y ∈ ℝ)[xy = 0 → x = 0 ∨ y = 0]                           (L2)
--    (∀ x, y ∈ ℝ)[x - y = 0 ↔ x = y]                                (L3)
--    (∀ x, y ∈ ℝ)[x + y = 0 → x = -y]                               (L4)
--
-- Se tiene que
--    (x - y)(x + y) = x² - y²
--                   = y² - y²    [por la hipótesis]
--                   = 0          [por L1]
-- y, por el lema L2, se tiene que
--    x - y = 0 ∨ x + y = 0
--
-- Acabaremos la demostración por casos.
--
-- Primer caso:
--   x - y = 0 ⟹ x = y             [por L3]
--             ⟹ x = y ∨ x = -y
--
-- Segundo caso:
--   x + y = 0 ⟹ x = -y            [por L4]
--             ⟹ x = y ∨ x = -y

-- Demostraciones en Lean4
-- =======================

-- 1ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by
  have h1 : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x^2 - y^2 := by ring
                         _ = y^2 - y^2 := by rw [h]
                         _ = 0         := sub_self (y ^ 2)
  have h2 : x - y = 0 ∨ x + y = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  . -- h3 : x - y = 0
    left
    -- ⊢ x = y
    exact sub_eq_zero.mp h3
  . -- h4 : x + y = 0
    right
    -- ⊢ x = -y
    exact eq_neg_of_add_eq_zero_left h4

-- 2ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
sq_eq_sq_iff_eq_or_eq_neg.mp h

-- Lemas usados
-- ============

-- #check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
-- #check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
-- #check (sq_eq_sq_iff_eq_or_eq_neg : x ^ 2 = y ^ 2 ↔ x = y ∨ x = -y)
-- #check (sub_eq_zero : x - y = 0 ↔ x = y)
-- #check (sub_self x : x - x = 0)
