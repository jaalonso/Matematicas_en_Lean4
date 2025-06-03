-- ---------------------------------------------------------------------
-- Ejercicio. Ejercutar las siguientes acciones
-- 1. Importar la librería data.set.basic data.nat.parity
-- 2. Abrir los espacios de nombres set y nat.
-- ----------------------------------------------------------------------

import Mathlib.Tactic
import Mathlib.Algebra.Ring.Parity

open Set Nat

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números naturales.
-- ----------------------------------------------------------------------

def Naturales : Set ℕ := {_n | True}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números pares.
-- ----------------------------------------------------------------------

def Pares     : Set ℕ := {n | Even n}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números impares.
-- ----------------------------------------------------------------------

def Impares   : Set ℕ := {n | ¬Even n}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    Pares ∪ Impares = Naturales
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    {n | Even n} ∪ {n | ¬Even n} = {n | True}
-- es decir,
--    n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
-- que se reduce a
--    ⊢ Even n ∨ ¬Even n
-- que es una tautología.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- n : ℕ
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  simp only [Set.mem_setOf_eq, iff_true]
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n}
  exact em (Even n)

-- 2ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- n : ℕ
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  tauto

-- Lemas usados
-- ============

variable (x : ℕ)
variable (a : Prop)
variable (p : ℕ → Prop)
#check (Set.mem_setOf_eq : (x ∈ {y : ℕ | p y}) = p x)
#check (em a : a ∨ ¬ a)
#check (iff_true a : (a ↔ True) = a)
