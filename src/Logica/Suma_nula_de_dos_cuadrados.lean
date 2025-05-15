-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar x e y como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x^2 + y^2 = 0
-- entonces
--   x = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Demostraciones con Lean 4
-- =========================

-- Se usarán los siguientes lemas
--    (∀ x ∈ ℝ)(∀ n ∈ ℕ)[x^n = 0 → x = 0]                            (L1)
--    (∀ x, y ∈ ℝ)[x ≤ y → y ≤ x → x = y]                            (L2)
--    (∀ x, y ∈ ℝ)[0 ≤ y → x ≤ x + y]                                (L3)
--    (∀ x ∈ ℝ)[0 ≤ x²]                                              (L4)
--
-- Por el lema L1, basta demostrar
--    x² = 0                                                         (1)
-- y, por el lema L2, basta demostrar las siguientes desigualdades
--     x² ≤ 0                                                        (2)
--     0 ≤ x²                                                        (3)
--
-- La prueba de la (2) es
--    x² ≤ x² + y²   [por L3 y L4]
--       = 0         [por la hipótesis]
--
-- La (3) se tiene por el lema L4.

-- 1ª demostración
-- ===============

example
  (h : x^2 + y^2 = 0)
  : x = 0 :=
by
  have h' : x^2 = 0 := by
    apply le_antisymm
    . -- ⊢ x ^ 2 ≤ 0
      calc x ^ 2 ≤ x^2 + y^2 := by simp [le_add_of_nonneg_right,
                                         pow_two_nonneg]
               _ = 0         := by exact h
    . -- ⊢ 0 ≤ x ^ 2
      apply pow_two_nonneg
  show x = 0
  exact pow_eq_zero h'

-- 2ª demostración
-- ===============

lemma aux
  (h : x^2 + y^2 = 0)
  : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

-- Lemas usados
-- ============

-- #check (le_add_of_nonneg_right : 0 ≤ y → x ≤ x + y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (pow_eq_zero : ∀ {n : ℕ}, x ^ n = 0 → x = 0)
-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Demostraciones con Lean4
-- ========================

-- Para la primera implicación, supongamos que
--    x² + y² = 0                                                    (1)
-- Entonces, por el lema anterior,
--    x = 0                                                          (2)
-- Además, aplicando la conmutativa a (1), se tiene
--    y² + x² = 0
-- y, por el lema anterior,
--    y = 0                                                          (3)
-- De (2) y (3) se tiene
--    x = 0 ∧ y = 0
--
-- Para la segunda implicación, supongamos que
--    x = 0 ∧ y = 0
-- Por tanto,
--    x² + y² = 0² + 0²
--            = 0

-- 1ª demostración
-- ===============

example : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
by
  constructor
  . -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    . -- ⊢ x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : x ^ 2 + y ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    intro h1
    -- h1 : x = 0 ∧ y = 0
    -- ⊢ x ^ 2 + y ^ 2 = 0
    rcases h1 with ⟨h2, h3⟩
    -- h2 : x = 0
    -- h3 : y = 0
    rw [h2, h3]
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- 2ª demostración
-- ===============

example : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
by
  constructor
  . -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    . -- ⊢ x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : x ^ 2 + y ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    rintro ⟨h1, h2⟩
    -- h1 : x = 0
    -- h2 : y = 0
    -- ⊢ x ^ 2 + y ^ 2 = 0
    rw [h1, h2]
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- 3ª demostración
-- ===============

example : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    · -- x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : y ^ 2 + x ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    rintro ⟨rfl, rfl⟩
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- Comentario: La táctica constructor, si el objetivo es un bicondicional
-- (P ↔ Q), aplica la introducción del bicondicional; es decir, lo
-- sustituye por dos nuevos objetivos: P → Q y Q → P.

-- Lemas usados
-- ============

-- #check (add_comm x y : x + y = y + x)
