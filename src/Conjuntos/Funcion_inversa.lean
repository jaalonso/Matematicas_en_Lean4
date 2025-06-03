-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría data.set.function
-- 2. Declarar u y v como universos.
-- 3. Declarar α como variable sobre tipo de u habitados.
-- 4. Declarar β como variable sobre tipo de v.
-- 5. Declarar la teoría como no computable.
-- 6. Usar la lógica clásica.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

universe u v                          -- 2
variable {α : Type u} [Inhabited α]   -- 3
variable {β : Type v}                 -- 4
noncomputable section                 -- 5
open Classical

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la inversa de una función
-- ----------------------------------------------------------------------

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y
  then Classical.choose h
  else default

-- ---------------------------------------------------------------------
-- Ejercicio. Sea d una función de α en β e y un elemento de
-- β. Demostrar que si
--    ∃ x, f x = y
-- entonces
--    f (inverse f y) = y
-- ----------------------------------------------------------------------

theorem inverse_spec
  {f : α → β}
  (y : β)
  (h : ∃ x, f x = y)
  : f (inverse f y) = y :=
by
  rw [inverse, dif_pos h]
  -- ⊢ f (choose h) = y
  exact Classical.choose_spec h

-- Comentarios:
-- 1. La identidad (dif_pos h), cuando (h : e), reescribe la expresión
--    (if h : e then x else y) a x.

-- Lemas usados
-- ============

variable (P : α -> Prop)
variable (c : Prop)
variable {t : c → α}
variable {e : ¬c → α}
variable (hc : c)
variable (h : ∃ x, P x)
#check (Classical.choose : (∃ x, P x) → α)
#check (Classical.choose_spec : (∃ x, P x) → P (Classical.choose h))
#check (dif_pos hc : dite c t e = t hc)
#check (inverse : (α → β) → β → α)
