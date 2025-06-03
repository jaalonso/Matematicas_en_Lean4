import Mathlib.Data.Set.Function

open Set

universe u v
variable {α : Type u}
variable {β : Type v}
variable (f : α → β)
variable (s : Set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f es inyectiva sobre s syss
--    ∀ x1 ∈ s, ∀ x2 ∈ s, f x1 = f x2 → x1 = x2
-- ----------------------------------------------------------------------

example :
  InjOn f s ↔ ∀ x1 ∈ s, ∀ x2 ∈ s, f x1 = f x2 → x1 = x2 :=
Iff.refl _

-- Lemas usados
-- ============

variable (a : Prop)
#check (Iff.refl a : a ↔ a)
