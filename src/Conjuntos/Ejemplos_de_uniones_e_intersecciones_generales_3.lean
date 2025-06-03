-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.set.lattice
-- 2. Abrir el espacio de nombres set.
-- 3. Declarar α una variable de tipos.
-- 4. Declarar s una vabiable sobre conjuntos de conjuntos de elementos
--    de α.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Lattice -- 1
open Set                        -- 2
variable {α : Type*}            -- 3
variable (s : Set (Set α))      -- 4

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ⋃₀ s = ⋃ t ∈ s, t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ⋃₀ s = ⋃ t ∈ s, t :=
by
  ext x
  -- ⊢ x ∈ ⋃₀ s ↔ x ∈ ⋃ t ∈ s, t
  rw [mem_iUnion₂]
  -- ⊢ x ∈ ⋃₀ s ↔ ∃ i, ∃ (_ : i ∈ s), x ∈ i
  simp

-- 2ª demostración
-- ===============

example : ⋃₀ s = ⋃ t ∈ s, t :=
sUnion_eq_biUnion

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ⋂₀ s = ⋂ t ∈ s, t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

-- 2ª demostración
-- ===============

example : ⋂₀ s = ⋂ t ∈ s, t :=
sInter_eq_biInter

-- Lemas usados
-- ============

variable (α : Type u)
variable (x : α)
variable (A : I → J → Set α)
variable (s : Set (Set α))
#check (mem_iInter₂ : x ∈ ⋂ i, ⋂ j, A i j ↔ ∀ i j, x ∈ A i j)
#check (mem_iUnion₂ : x ∈ ⋃ i, ⋃ j, A i j ↔ ∃ i j, x ∈ A i j)
#check (sInter_eq_biInter : ⋂₀ s = ⋂ i ∈ s, i)
#check (sUnion_eq_biUnion : ⋃₀ s = ⋃ i ∈ s, i)
