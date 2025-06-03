-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la composición de funciones inyectivas es
-- inyectiva.
-- ----------------------------------------------------------------------

import Mathlib.Tactic

open Function

variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

-- 1ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro x y h1
  -- x y : α
  -- h1 : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  have h2: g (f x) = g (f y) := h1
  have h3: f x = f y := hg h2
  show x = y
  exact hf h3

-- 2ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intros x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  apply hf
  -- ⊢ f x = f y
  apply hg
  -- ⊢ g (f x) = g (f y)
  apply h

-- 3ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
fun _ _ h ↦ hf (hg h)

-- 4ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
-- by exact?
Injective.comp hg hf

-- 5ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by tauto

-- Lemas usados
-- ============

#check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
