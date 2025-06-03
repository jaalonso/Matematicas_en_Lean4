-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.nat.prime data.nat.parity
-- 2. Abrir el espacio de nombres nat
-- 3. Declarar s y t como variables sobre conjuntos de números naturales.
-- 4. Declarar el hecho (ssubt : s ⊆ t)
-- 5, Añadir ssubt como hipótesis de la teoría.
-- ----------------------------------------------------------------------

import Mathlib.Data.Nat.Prime.Basic

open Nat                              -- 2

variable (s t : Set ℕ)                -- 3
variable (ssubt : s ⊆ t)              -- 4

include ssubt                         -- 5

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∀ x ∈ t, ¬ Even x
--    ∀ x ∈ t, Nat.Prime x
-- entonces
--    ∀ x ∈ s, ¬ Even x ∧ Nat.Prime x
-- ----------------------------------------------------------------------

example
  (h₀ : ∀ x ∈ t, ¬Even x)
  (h₁ : ∀ x ∈ t, Nat.Prime x)
  : ∀ x ∈ s, ¬Even x ∧ Nat.Prime x :=
by
  intro x xs
  -- x : ℕ
  -- xs : x ∈ s
  -- ⊢ ¬Even x ∧ Nat.Prime x
  constructor
  · -- ⊢ ¬Even x
    apply h₀ x (ssubt xs)
  . -- ⊢ Nat.Prime x
    apply h₁ x (ssubt xs)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∃ x ∈ s, ¬ Even x ∧ Nat.Prime x
-- entonces
--    ∃ x ∈ t, Nat.Prime x
-- ----------------------------------------------------------------------

example (h : ∃ x ∈ s, ¬Even x ∧ Nat.Prime x) : ∃ x ∈ t, Nat.Prime x :=
by
  rcases h with ⟨x, xs, -, px⟩
  -- x : ℕ
  -- xs : x ∈ s
  -- px : Nat.Prime x
  -- ⊢ ∃ x ∈ t, Nat.Prime x
  use x, ssubt xs
