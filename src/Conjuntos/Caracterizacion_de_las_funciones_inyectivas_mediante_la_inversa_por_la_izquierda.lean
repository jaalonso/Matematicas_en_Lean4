import src.Conjuntos.Funcion_inversa
import Mathlib.Data.Set.Function

universe u v
variable {α : Type u} [Inhabited α]
variable {β : Type v}
variable (f : α → β)
variable (g : β → α)
variable (x : α)

open Set Function

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que g es la inversa por la izquierda de f syss
--    ∀ x, g (f x) = x
-- ----------------------------------------------------------------------

example : LeftInverse g f ↔ ∀ x, g (f x) = x :=
by rw [LeftInverse]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las siguientes condiciones son equivalentes:
-- 1. f es inyectiva
-- 2. left_inverse (inverse f) f
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · -- ⊢ Injective f → LeftInverse (inverse f) f
    intro h y
    -- h : Injective f
    -- y : α
    -- ⊢ inverse f (f y) = y
    apply h
    -- ⊢ f (inverse f (f y)) = f y
    apply inverse_spec
    -- ⊢ ∃ x, f x = f y
    use y
  . -- ⊢ LeftInverse (inverse f) f → Injective f
    intro h x1 x2 e
    -- x1 x2 : α
    -- e : f x1 = f x2
    -- ⊢ x1 = x2
    rw [← h x1, ← h x2, e]

-- 2ª demostración
-- ===============

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

-- Lemas usados
-- ============

variable (y : β)
#check (LeftInverse : (β → α) → (α → β) → Prop)
#check (inverse_spec y : (∃ x, f x = y) → f (inverse f y) = y)
