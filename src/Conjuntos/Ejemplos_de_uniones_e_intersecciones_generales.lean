-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones
-- 1. Importar las librerías Tactic, Set.Basic y Set.Lattice
-- 2. Abrir el espacio de nombres Set
-- 3. Declarar u y v como variables de universos.
-- 4. Declarar α como una variable de tipos en u.
-- 5. Declarar I como una variable de tipos en v.
-- 6. Declarar A y B como variables sobre funciones de I en α.
-- 7. Declarar s como variable sobre conjuntos de elementos de α.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Basic    -- 1
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

open Set                         -- 2

universe u v                     -- 3
variable (α : Type u)            -- 4
variable (I : Type v)            -- 5
variable (A B : I → Set α)       -- 6
variable (s : Set α)             -- 7

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada x, se verifica que
--    x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
-- Lo demostramos mediante la siguiente cadena de equivalencias
--    x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ s ∧ x ∈ ⋃ (i : ℕ), A i
--                           ↔ x ∈ s ∧ (∃ i : ℕ, x ∈ A i)
--                           ↔ ∃ i : ℕ, x ∈ s ∧ x ∈ A i
--                           ↔ ∃ i : ℕ, x ∈ A i ∧ x ∈ s
--                           ↔ ∃ i : ℕ, x ∈ A i ∩ s
--                           ↔ x ∈ ⋃ (i : ℕ), A i ∩ s

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : I), A i ↔ x ∈ ⋃ (i : I), A i ∩ s
  calc x ∈ s ∩ ⋃ (i : I), A i
     ↔ x ∈ s ∧ x ∈ ⋃ (i : I), A i :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ s ∧ (∃ i : I, x ∈ A i) :=
         by simp only [mem_iUnion]
   _ ↔ ∃ i : I, x ∈ s ∧ x ∈ A i :=
         by simp only [exists_and_left]
   _ ↔ ∃ i : I, x ∈ A i ∧ x ∈ s :=
         by simp only [and_comm]
   _ ↔ ∃ i : I, x ∈ A i ∩ s :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ ⋃ (i : I), A i ∩ s :=
         by simp only [mem_iUnion]

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : I), A i ↔ x ∈ ⋃ (i : I), A i ∩ s
  constructor
  . -- ⊢ x ∈ s ∩ ⋃ (i : I), A i → x ∈ ⋃ (i : I), A i ∩ s
    intro h
    -- h : x ∈ s ∩ ⋃ (i : I), A i
    -- ⊢ x ∈ ⋃ (i : I), A i ∩ s
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ A i ∩ s
    rcases h with ⟨xs, xUAi⟩
    -- xs : x ∈ s
    -- xUAi : x ∈ ⋃ (i : I), A i
    rw [mem_iUnion] at xUAi
    -- xUAi : ∃ i, x ∈ A i
    rcases xUAi with ⟨i, xAi⟩
    -- i : I
    -- xAi : x ∈ A i
    use i
    -- ⊢ x ∈ A i ∩ s
    constructor
    . -- ⊢ x ∈ A i
      exact xAi
    . -- ⊢ x ∈ s
      exact xs
  . -- ⊢ x ∈ ⋃ (i : I), A i ∩ s → x ∈ s ∩ ⋃ (i : I), A i
    intro h
    -- h : x ∈ ⋃ (i : I), A i ∩ s
    -- ⊢ x ∈ s ∩ ⋃ (i : I), A i
    rw [mem_iUnion] at h
    -- h : ∃ i, x ∈ A i ∩ s
    rcases h with ⟨i, hi⟩
    -- i : I
    -- hi : x ∈ A i ∩ s
    rcases hi with ⟨xAi, xs⟩
    -- xAi : x ∈ A i
    -- xs : x ∈ s
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ ⋃ (i : I), A i
      rw [mem_iUnion]
      -- ⊢ ∃ i, x ∈ A i
      use i
      -- ⊢ x ∈ A i

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : I), A i ↔ x ∈ ⋃ (i : I), A i ∩ s
  simp
  -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) ↔ (∃ i, x ∈ A i) ∧ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) → (∃ i, x ∈ A i) ∧ x ∈ s
    rintro ⟨xs, ⟨i, xAi⟩⟩
    -- xs : x ∈ s
    -- i : I
    -- xAi : x ∈ A i
    -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s
    exact ⟨⟨i, xAi⟩, xs⟩
  . -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s → x ∈ s ∧ ∃ i, x ∈ A i
    rintro ⟨⟨i, xAi⟩, xs⟩
    -- xs : x ∈ s
    -- i : I
    -- xAi : x ∈ A i
    -- ⊢ x ∈ s ∧ ∃ i, x ∈ A i
    exact ⟨xs, ⟨i, xAi⟩⟩

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : I), A i ↔ x ∈ ⋃ (i : I), A i ∩ s
  aesop

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by ext; aesop

-- Lemas usados
-- ============

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para x se verifica
--    x ∈ ⋂ i, (A i ∩ B i) ↔ x ∈ (⋂ i, A i) ∩ (⋂ i, B i)
-- Lo demostramos mediante la siguiente cadena de equivalencias
--    x ∈ ⋂ i, (A i ∩ B i) ↔ (∀ i)[x ∈ A i ∩ B i]
--                         ↔ (∀ i)[x ∈ A i ∧ x ∈ B i]
--                         ↔ (∀ i)[x ∈ A i] ∧ (∀ i)[x ∈ B i]
--                         ↔ x ∈ (⋂ i, A i) ∧ x ∈ (⋂ i, B i)
--                         ↔ x ∈ (⋂ i, A i) ∩ (⋂ i, B i)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  calc x ∈ ⋂ i, A i ∩ B i
     ↔ ∀ i, x ∈ A i ∩ B i :=
         by exact mem_iInter
   _ ↔ ∀ i, x ∈ A i ∧ x ∈ B i :=
         by simp only [mem_inter_iff]
   _ ↔ (∀ i, x ∈ A i) ∧ (∀ i, x ∈ B i) :=
         by exact forall_and
   _ ↔ x ∈ (⋂ i, A i) ∧ x ∈ (⋂ i, B i) :=
         by simp only [mem_iInter]
   _ ↔ x ∈ (⋂ i, A i) ∩ ⋂ i, B i :=
         by simp only [mem_inter_iff]

-- 2ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  constructor
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) → (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    -- ⊢ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      exact (h i).1
    . -- ⊢ ∀ (i : ℕ), x ∈ B i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ B i
      exact (h i).2
  . -- ⊢ ((∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i) → ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    intros h i
    -- h : (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    -- i : ℕ
    -- ⊢ x ∈ A i ∧ x ∈ B i
    rcases h with ⟨h1, h2⟩
    -- h1 : ∀ (i : ℕ), x ∈ A i
    -- h2 : ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ x ∈ A i
      exact h1 i
    . -- ⊢ x ∈ B i
      exact h2 i

-- 3ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  exact ⟨fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩,
         fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2 i⟩⟩

-- 4ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  aesop

-- Lemas usados
-- ============

variable (x : α)
variable (a b : Set α)
variable (ι : Sort v)
variable (s : ι → Set α)
variable (p q : α → Prop)
variable (P Q : Prop)
#check (and_comm : P ∧ Q ↔ Q ∧ P)
#check (exists_and_left : (∃ (x : α), Q ∧ p x) ↔ Q ∧ ∃ (x : α), p x)
#check (forall_and : (∀ (x : α), p x ∧ q x) ↔ (∀ (x : α), p x) ∧ ∀ (x : α), q x)
#check (mem_iInter : x ∈ ⋂ (i : ι), s i ↔ ∀ (i : ι), x ∈ s i)
#check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
#check (mem_inter_iff x a b : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b)
