-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar α como una variables sobre preórdenes.
-- 3. Declarar a, b y c como variables sobre elementos de α.
-- ----------------------------------------------------------------------

import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a b c : α)

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que que la relación menor es irreflexiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará la siguiente propiedad de lo preórdenes
--    (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a]
-- Con dicha propiedad, lo que tenemos que demostrar se transforma en
--    ¬(a ≤ a ∧ a ≰ a)
-- Para demostrarla, supongamos que
--    a ≤ a ∧ a ≰ a
-- lo que es una contradicción.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : ¬a < a :=
by
  rw [lt_iff_le_not_le]
  -- ⊢ ¬(a ≤ a ∧ ¬a ≤ a)
  rintro ⟨h1, h2⟩
  -- h1 : a ≤ a
  -- h2 : ¬a ≤ a
  -- ⊢ False
  exact h2 h1

-- 2ª demostración
-- ===============

example : ¬a < a :=
  irrefl a

-- Lemas usados
-- ============

-- #check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (irrefl a : ¬a < a)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que que la relación menor es transitiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará la siguiente propiedad de los preórdenes
--    (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a]
-- Con dicha propiedad, lo que tenemos que demostrar se transforma en
--    a ≤ b ∧ b ≰ a → b ≤ c ∧ c ≰ b → a ≤ c ∧ c ≰ a
-- Para demostrarla, supongamos que
--    a ≤ b                                                          (1)
--    b ≰ a                                                          (2)
--    b ≤ c                                                          (3)
--    c ≰ b                                                          (4)
-- y tenemos que demostrar las siguientes relaciones
--    a ≤ c                                                          (5)
--    c ≰ a                                                          (6)
--
-- La (5) se tiene aplicando la propiedad transitiva a (1) y (3).
--
-- Para demostrar la (6), supongamos que
--    c ≤ a                                                          (7)
-- entonces, junto a la (1), por la propieda transitiva se tiene
--    c ≤ b
-- que es una contradicción con la (4).

-- 1ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    contrapose! h4
    -- h4 : c ≤ a
    -- ⊢ c ≤ b
    exact le_trans h4 h1

-- 2ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    rintro (h5 : c ≤ a)
    -- ⊢ False
    have h6 : c ≤ b := le_trans h5 h1
    show False
    exact h4 h6

-- 3ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    exact fun h5 ↦ h4 (le_trans h5 h1)

-- 4ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  exact ⟨le_trans h1 h3, fun h5 ↦ h4 (le_trans h5 h1)⟩

-- 5ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  exact fun ⟨h1, _h2⟩ ⟨h3, h4⟩ ↦ ⟨le_trans h1 h3,
                                  fun h5 ↦ h4 (le_trans h5 h1)⟩

-- 6ª demostración
-- ===============

example : a < b → b < c → a < c :=
  lt_trans

-- Lemas usados
-- ============

-- #check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- #check (lt_trans : a < b → b < c → a < c)
