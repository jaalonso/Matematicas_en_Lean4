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
-- Ejercicio. Demostrar que g es la inversa por la derecha de f syss
--    ∀ x, f (g x) = x
-- ----------------------------------------------------------------------

example : RightInverse g f ↔ ∀ x, f (g x) = x :=
by
  rw [RightInverse]
  -- ⊢ LeftInverse f g ↔ ∀ (x : β), f (g x) = x
  rw [LeftInverse]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las siguientes condiciones son equivalentes:
-- 1. f es suprayectiva
-- 2. right_inverse (inverse f) f
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · -- ⊢ Surjective f → RightInverse (inverse f) f
    intro h y
    -- h : Surjective f
    -- y : β
    -- ⊢ f (inverse f y) = y
    apply inverse_spec
    -- ⊢ ∃ x, f x = y
    apply h
  . -- ⊢ RightInverse (inverse f) f → Surjective f
    intro h y
    -- h : RightInverse (inverse f) f
    -- y : β
    -- ⊢ ∃ a, f a = y
    use inverse f y
    -- ⊢ f (inverse f y) = y
    apply h

-- 2ª demostración
-- ===============

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h _ ↦ inverse_spec _ (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f es suprayectiva syss tiene una inversa por
-- la izquierda.
-- ----------------------------------------------------------------------

example : Surjective f ↔ ∃ g, RightInverse g f :=
by
  constructor
  . -- ⊢ Surjective f → ∃ g, RightInverse g f
    intro h
    -- h : Surjective f
    -- ⊢ ∃ g, RightInverse g f
    dsimp [Surjective] at h
    -- ⊢ ∃ g, RightInverse g f
    choose g hg using h
    -- g : β → α
    -- hg : ∀ (b : β), f (g b) = b
    use g
    -- ⊢ RightInverse g f
    exact hg
  . -- ⊢ (∃ g, RightInverse g f) → Surjective f
    rintro ⟨g, hg⟩
    -- g : β → α
    -- hg : RightInverse g f
    -- ⊢ Surjective f
    intros b
    -- b : β
    -- ⊢ ∃ a, f a = b
    use g b
    -- ⊢ f (g b) = b
    exact hg b

-- Comentarios:
-- 1. La táctica (dsimp [e] at h) simplifica la hipótesis h con la
--    definición de e.
-- 2. La táctica (choose g hg using h) si h es de la forma
--    (∀ (b : β), ∃ (a : α), f a = b) quita la hipótesis h y añade las
--     hipótesis (g : β → α) y (hg : ∀ (b : β), f (g b) = b).

-- Lemas usados
-- ============

variable (y : β)
#check (LeftInverse : (β → α) → (α → β) → Prop)
#check (RightInverse : (β → α) → (α → β) → Prop)
#check (Surjective : (α → β) → Prop)
#check (inverse_spec y : (∃ x, f x = y) → f (inverse f y) = y)
