-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números naturales.
-- 2. Declarar x e y como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    y > x^2
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que
--    (∀ x ∈ ℝ)[x² ≥ 0]
-- se tiene que
--    y > x²
--      ≥ 0
-- Por tanto, y > 0 y, al verificar la primera parte de la diyunción, se
-- verifica la disyunción.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  have h1 : y > 0 := by
    calc y > x^2 := h
         _ ≥ 0   := pow_two_nonneg x
  show y > 0 ∨ y < -1
  exact Or.inl h1

-- 2ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  calc y > x^2 := h
       _ ≥ 0   := pow_two_nonneg x

-- 3ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  linarith [pow_two_nonneg x]

-- 4ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by { left ; linarith [pow_two_nonneg x] }

-- Comentario: La táctica left, si el objetivo es una disjunción
-- (P ∨ Q), aplica la regla de introducción de la disyunción; es decir,
-- cambia el objetivo por P.

-- Lema usado
-- ==========

-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    -y > x^2 + 1
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas
--    (∀ b, c ∈ ℝ)[b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)]               (L1)
--    (∀ a ∈ ℝ)[0 ≤ a^2]                                             (L2)
--    (∀ a  ∈ ℝ)[0 + a = a]                                          (L3)
--    (∀ a, b ∈ ℝ)[a < -b ↔ b < -a]                                  (L4)

-- Se tiene
--    -y > x^2 + 1    [por la hipótesis]
--       ≥ 0 + 1      [por L1 y L2]
--       = 1          [por L3]
-- Por tanto,
--    -y > 1
-- y, aplicando el lema L4, se tiene
--    y < -1
-- Como se verifica la segunda parte de la diyunción, se verifica la
-- disyunción.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by
    calc -y > x^2 + 1 := by exact h
          _ ≥ 0 + 1   := add_le_add_right (pow_two_nonneg x) 1
          _ = 1       := zero_add 1
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 2ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by linarith [pow_two_nonneg x]
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 3ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1: y < -1 := by linarith [pow_two_nonneg x]
  show y > 0 ∨ y < -1
  exact Or.inr h1

-- 4ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  right
  -- ⊢ y < -1
  linarith [pow_two_nonneg x]

-- 5ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by { right ; linarith [pow_two_nonneg x] }

-- Comentario: La táctica right, si el objetivo es una disjunción
-- (P ∨ Q), aplica la regla de introducción de la disyunción; es decir,
-- cambia el objetivo por Q.

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (pow_two_nonneg a : 0 ≤ a ^ 2)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (zero_add a : 0 + a = a)
-- #check (lt_neg : a < -b ↔ b < -a)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--      y > 0
-- entonces
--      y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : y > 0)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  exact h

-- 2ª demostración
-- ===============

example
  (h : y > 0)
  : y > 0 ∨ y < -1 :=
Or.inl h

-- 3ª demostración
-- ===============

example
  (h : y > 0)
  : y > 0 ∨ y < -1 :=
by tauto

-- Lema usado
-- ==========

-- variable (a b : Prop)
-- #check (Or.inl : a → a ∨ b)

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    y < -1
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : y < -1)
  : y > 0 ∨ y < -1 :=
by
  right
  -- y < -1
  exact h

-- 2ª demostración
-- ===============

example
  (h : y < -1)
  : y > 0 ∨ y < -1 :=
Or.inr h

-- 3ª demostración
-- ===============

example
  (h : y < -1)
  : y > 0 ∨ y < -1 :=
by tauto

-- Lema usado
-- ==========

-- variable (a b : Prop)
-- #check (Or.inr : b → a ∨ b)
