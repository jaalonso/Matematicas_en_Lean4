-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.nat.prime data.nat.parity
-- 2. Abrir el espacio de nombres nat.
-- 3. Declarar s como variable sobre conjuntos de números naturales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Nat.Prime.Basic     -- 1
open Nat                                -- 2
variable (s : Set ℕ)                    -- 3

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si los elementos de s no son pares y si los
-- elementos de s son primos, entonces los elementos de s no son pares
-- pero sí son primpos.
-- ----------------------------------------------------------------------

example
  (h₀ : ∀ x ∈ s, ¬ Even x)
  (h₁ : ∀ x ∈ s, Nat.Prime x)
  : ∀ x ∈ s, ¬ Even x ∧ Nat.Prime x :=
by
  intros x xs
  -- x : ℕ
  -- xs : x ∈ s
  -- ⊢ ¬Even x ∧ Nat.Prime x
  constructor
  . -- ⊢ ¬Even x
    apply h₀ x xs
  . -- ⊢ Nat.Prime x
    apply h₁ x xs

-- Comentario: La táctica (intros x xs) si la conclusión es (∀ y ∈ s, P y)
-- y una hipótesis es (s : Set α), entonces añade las hipótesis (x : α)
-- y (xs : x ∈ s) y cambia la conclusión a (P x).

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si s tiene algún elemento primo impar,
-- entonces tiene algún elemento primo.
-- ----------------------------------------------------------------------

example
  (h : ∃ x ∈ s, ¬ Even x ∧ Nat.Prime x)
  : ∃ x ∈ s, Nat.Prime x :=
by
  rcases h with ⟨x, xs, -, Nat.Prime_x⟩
  -- x : ℕ
  -- xs : x ∈ s
  -- Nat.Prime_x : Nat.Prime x
  -- ⊢ ∃ x, x ∈ s ∧ Nat.Prime x
  use x, xs

-- Comentarios:
-- 1. La táctica (cases h with ⟨x, xs, h1, h2⟩) si la
--    hipótesis es (∃ y ∈ s, P y ∧ Q y) y una hipótesis es (s : Set α),
--    entonces quita h y añade las hipótesis (x : s), (h1 : P x) y
--    (h2 : Q x).
-- 2. La táctica (use x, xs) resuelve la conclusión
--    (∃ x ∈ s, P x) si xs es una prueba de (x ∈ s) y h lo es de (P x).
