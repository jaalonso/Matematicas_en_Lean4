-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría data.set.lattice
-- 2. Importar la teoría data.nat.prime
-- 3. Abrir los espacios de nombre set y nat.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite

open Set Nat

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números primos.
-- ----------------------------------------------------------------------

def primes : Set ℕ := {x | Nat.Prime x}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x}
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) =
          { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=
by
  ext
  -- ⊢ x ∈ ⋃ p ∈ primes, {x | p ^ 2 ∣ x} ↔ x ∈ {x | ∃ p ∈ primes, p ^ 2 ∣ x}
  rw [mem_iUnion₂]
  -- ⊢ (∃ i, ∃ (_ : i ∈ primes), x ∈ {x | i ^ 2 ∣ x}) ↔ x ∈ {x | ∃ p ∈ primes, p ^ 2 ∣ x}
  simp

-- 2ª demostración
-- ===============

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=
by
  ext
  -- ⊢ x ∈ ⋃ p ∈ primes, {x | p ^ 2 ∣ x} ↔ x ∈ {x | ∃ p ∈ primes, p ^ 2 ∣ x}
  simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1}
-- ----------------------------------------------------------------------

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } :=
by
  intro x
  -- x : ℕ
  -- ⊢ x ∈ ⋂ p ∈ primes, {x | ¬p ∣ x} → x ∈ {x | x = 1}
  contrapose!
  -- ⊢ x ∉ {x | x = 1} → x ∉ ⋂ p ∈ primes, {x | ¬p ∣ x}
  simp
  -- ⊢ ¬x = 1 → ∃ x_1 ∈ primes, x_1 ∣ x
  apply Nat.exists_prime_and_dvd

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋃ p ∈ primes, {x | x ≤ p}) = univ
-- ----------------------------------------------------------------------

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
by
  apply eq_univ_of_forall
  -- ⊢ ∀ (x : ℕ), x ∈ ⋃ p ∈ primes, {x | x ≤ p}
  intro x
  -- x : ℕ
  -- ⊢ x ∈ ⋃ p ∈ primes, {x | x ≤ p}
  simp
  -- ⊢ ∃ i ∈ primes, x ≤ i
  dsimp [primes]
  -- ⊢ ∃ i, Nat.Prime i ∧ x ≤ i
  obtain ⟨p, pge, primep⟩ := exists_infinite_primes x
  -- p : ℕ
  -- pge : x ≤ p
  -- primep : Nat.Prime p
  use p

-- Lemas usados
-- ============

variable (α : Type u)
variable (I : Type v)
variable (J : Type w)
variable (A : I → J → Set α)
variable (x : α)
variable (n : ℕ)
variable (s : Set α)
#check (Nat.exists_prime_and_dvd : n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n)
#check (eq_univ_of_forall : (∀ x, x ∈ s) → s = univ)
#check (exists_infinite_primes n : ∃ p, n ≤ p ∧ Nat.Prime p)
#check (mem_iUnion₂ : x ∈ ⋃ i, ⋃ j, A i j ↔ ∃ i j, x ∈ A i j)
