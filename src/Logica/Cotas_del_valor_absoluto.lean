-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar x e y como variables sobre los reales.
-- 3. Iniciar el espacio de nombre my_abs.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y z : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x < |y| ↔ x < y ∨ x < -y
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · -- h : 0 ≤ y
    rw [abs_of_nonneg h]
    -- ⊢ x < y ↔ x < y ∨ x < -y
    constructor
    · -- ⊢ x < y → x < y ∨ x < -y
      intro h'
      -- h' : x < y
      -- ⊢ x < y ∨ x < -y
      left
      -- ⊢ x < y
      exact h'
    . -- ⊢ x < y ∨ x < -y → x < y
      intro h'
      -- h' : x < y ∨ x < -y
      -- ⊢ x < y
      rcases h' with h' | h'
      · -- h' : x < y
        exact h'
      . -- h' : x < -y
        linarith
  . -- h : 0 > y
    rw [abs_of_neg h]
    -- ⊢ x < -y ↔ x < y ∨ x < -y
    constructor
    · -- ⊢ x < -y → x < y ∨ x < -y
      intro h'
      -- h' : x < -y
      -- ⊢ x < y ∨ x < -y
      right
      -- ⊢ x < -y
      exact h'
    . -- ⊢ x < y ∨ x < -y → x < -y
      intro h'
      -- h' : x < y ∨ x < -y
      -- ⊢ x < -y
      rcases h' with h' | h'
      · -- h' : x < y
        linarith
      . -- h' : x < -y
        exact h'

-- 2ª demostración
-- ===============

example : x < |y| ↔ x < y ∨ x < -y :=
by
  rw [abs_eq_max_neg]
  -- ⊢ x < max y (-y) ↔ x < y ∨ x < -y
  exact lt_max_iff

-- 3ª demostración
-- ===============

example : x < |y| ↔ x < y ∨ x < -y :=
  lt_max_iff

-- 4ª demostración
-- ===============

example : x < |y| ↔ x < y ∨ x < -y :=
  lt_abs

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    |x| < y ↔ - y < x ∧ x < y
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · -- h : 0 ≤ x
    rw [abs_of_nonneg h]
    -- ⊢ x < y ↔ -y < x ∧ x < y
    constructor
    · -- ⊢ x < y → -y < x ∧ x < y
      intro h'
      -- h' : x < y
      -- ⊢ -y < x ∧ x < y
      constructor
      · -- ⊢ -y < x
        linarith
      . -- ⊢ x < y
        exact h'
    . -- ⊢ -y < x ∧ x < y → x < y
      intro h'
      -- h' : -y < x ∧ x < y
      -- ⊢ x < y
      rcases h' with ⟨-, h2⟩
      -- h2 : x < y
      exact h2
  . -- h : 0 > x
    rw [abs_of_neg h]
    -- ⊢ -x < y ↔ -y < x ∧ x < y
    constructor
    · -- ⊢ -x < y → -y < x ∧ x < y
      intro h'
      -- h' : -x < y
      -- ⊢ -y < x ∧ x < y
      constructor
      · -- ⊢ -y < x
        linarith
      . -- ⊢ x < y
        linarith
    . -- ⊢ -y < x ∧ x < y → -x < y
      intro h'
      -- h' : -y < x ∧ x < y
      -- ⊢ -x < y
      linarith

-- 2ª demostración
-- ===============

example : |x| < y ↔ -y < x ∧ x < y :=
by
  rw [abs_eq_max_neg]
  -- ⊢ max x (-x) < y ↔ -y < x ∧ x < y
  constructor
  . -- ⊢ max x (-x) < y → -y < x ∧ x < y
    intro h1
    -- h1 : max x (-x) < y
    -- ⊢ -y < x ∧ x < y
    rw [max_lt_iff] at h1
    -- h1 : x < y ∧ -x < y
    rcases h1 with ⟨h2, h3⟩
    -- h2 : x < y
    -- h3 : -x < y
    constructor
    . -- ⊢ -y < x
      exact neg_lt.mp h3
    . -- ⊢ x < y
      exact h2
  . -- ⊢ -y < x ∧ x < y → max x (-x) < y
    intro h4
    -- h4 : -y < x ∧ x < y
    -- ⊢ max x (-x) < y
    apply max_lt_iff.mpr
    -- ⊢ x < y ∧ -x < y
    rcases h4 with ⟨h5, h6⟩
    -- h5 : -y < x
    -- h6 : x < y
    constructor
    . -- ⊢ x < y
      exact h6
    . -- ⊢ -x < y
      exact neg_lt.mp h5

-- 2ª demostración
-- ===============

example : |x| < y ↔ -y < x ∧ x < y :=
  abs_lt

-- Lemas usados
-- ============

#check (abs_eq_max_neg : |x| = max x (-x))
#check (abs_lt : |x| < y ↔ -y < x ∧ x < y)
#check (abs_of_neg : x < 0 → |x| = -x)
#check (abs_of_nonneg : 0 ≤ x → abs x = x)
#check (le_or_gt x y : x ≤ y ∨ x > y)
#check (lt_abs : x < |y| ↔ x < y ∨ x < -y)
#check (lt_max_iff : x < max y z ↔ x < y ∨ x < z)
#check (max_lt_iff : max x y < z ↔ x < z ∧ y < z)
#check (neg_lt : -x < y ↔ -y < x)
