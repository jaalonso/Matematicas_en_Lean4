-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números reales.
-- 2. Declarar x, y, a y b como variables sobre los reales.
-- 3. Crear el espacio de nombres my_abs.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
variable {x y a b : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x ≤ |x|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    (∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     (L1)
--    (∀ x, y ∈ ℝ)[x < y → x ≤ y]                                    (L2)
--    (∀ x ∈ ℝ)[x ≤ 0 → x ≤ -x]                                      (L3)
--    (∀ x ∈ ℝ)[x < 0 → |x| = -x]                                    (L4)
--
-- Se demostrará por casos según x ≥ 0:
--
-- Primer caso: Supongamos que x ≥ 0. Entonces,
--    x ≤ x
--      = |x|    [por L1]
--
-- Segundo caso: Supongamos que x < 0. Entonces, por el L2, se tiene
--    x ≤ 0                                                          (1)
-- Por tanto,
--    x ≤ -x     [por L3 y (1)]
--      = |x|    [por L4]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : x ≤ |x| :=
by
  rcases le_or_gt 0 x with h1 | h2
  . -- h1 : 0 ≤ x
    show x ≤ |x|
    calc x ≤ x   := le_refl x
         _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    have h3 : x ≤ 0 := le_of_lt h2
    show x ≤ |x|
    calc x ≤ -x  := le_neg_self_iff.mpr h3
         _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : x ≤ |x| :=
by
  rcases le_or_gt 0 x with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h2 : 0 > x
    rw [abs_of_neg h2]
    -- ⊢ x ≤ -x
    apply Left.self_le_neg
    -- ⊢ x ≤ 0
    exact le_of_lt h2

-- 3ª demostración
-- ===============

example : x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h1 : 0 ≤ x
    rw [abs_of_neg h2]
    linarith

-- 4ª demostración
-- ===============

example : x ≤ |x| :=
  le_abs_self x

-- Lemas usados
-- ============

-- #check (Left.self_le_neg : x ≤ 0 → x ≤ -x)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_abs_self x : x ≤ |x|)
-- #check (le_neg_self_iff : x ≤ -x ↔ x ≤ 0)
-- #check (le_of_lt : x < y → x ≤ y)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    -x ≤ |x|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    (∀ x ∈ ℝ)[0 ≤ x → -x ≤ x]                                      (L1)
--    (∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     (L2)
--    (∀ x ∈ ℝ)[x ≤ x]                                               (L3)
--    (∀ x ∈ ℝ)[x < 0) → |x| = -x]                                   (L4)
--
-- Se demostrará por casos según x ≥ 0:
--
-- Primer caso: Supongamos que x ≥ 0. Entonces,
--    -x ≤ x      [por L1]
--       = |x|    [por L2]
--
-- Segundo caso: Supongamos que x < 0. Entonces,
--    -x ≤ -x     [por L3]
--     _ = |x|    [por L4]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : -x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    show -x ≤ |x|
    calc -x ≤ x   := by exact neg_le_self h1
          _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    show -x ≤ |x|
    calc -x ≤ -x  := by exact le_refl (-x)
          _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : -x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    exact neg_le_self h1
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 3ª demostración
-- ===============

example : -x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    linarith
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 4ª demostración
-- ===============

example : -x ≤ |x| :=
  neg_le_abs_self x

-- Lemas usados
-- ============

-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (le_refl x : x ≤ x)
-- #check (neg_le_abs_self x : -x ≤ |x|)
-- #check (neg_le_self : 0 ≤ x → -x ≤ x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    |x + y| ≤ |x| + |y|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--     (∀ x ∈ ℝ)[0 ≤ x → |x| = x)                          (L1)
--     (∀ a, b, c, d ∈ ℝ)[a ≤ b ∧ c ≤ d → a + c ≤ b + d    (L2)
--     (∀ x ∈ ℝ)[x ≤ |x|]                                  (L3)
--     (∀ x ∈ ℝ)[x < 0 → |x| = -x]                         (L4)
--     (∀ x, y ∈ ℝ)[-(x + y) = -x + -y]                    (L5)
--     (∀ x ∈ ℝ)[-x ≤ |x|]                                 (L6)
--
-- Se demostrará por casos según x + y ≥ 0:
--
-- Primer caso: Supongamos que x + y ≥ 0. Entonces,
--    |x + y| = x + y        [por L1]
--          _ ≤ |x| + |y|    [por L2 y L3]
--
-- Segundo caso: Supongamos que x + y < 0. Entonces,
--    |x + y| = -(x + y)     [por L4]
--            = -x + -y      [por L5]
--            ≤ |x| + |y|    [por L2 y L6]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = x + y     := by exact abs_of_nonneg h1
               _ ≤ |x| + |y| := add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = -(x + y)  := by exact abs_of_neg h2
               _ = -x + -y   := by exact neg_add x y
               _ ≤ |x| + |y| := add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    exact add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    calc -(x + y) = -x + -y    := by exact neg_add x y
                _ ≤ |x| + |y|  := add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    linarith [le_abs_self x, le_abs_self y]
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    linarith [neg_le_abs_self x, neg_le_abs_self y]

-- 3ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| :=
  abs_add x y

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (abs_add x y : |x + y| ≤ |x| + |y|)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (neg_add x y : -(x + y) = -x + -y)
-- #check (neg_le_abs_self x : -x ≤ |x|)
