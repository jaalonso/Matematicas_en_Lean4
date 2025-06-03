import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s ∩ (t ∪ u). Entonces se tiene que
--    x ∈ s                                                          (1)
--    x ∈ t ∪ u                                                      (2)
-- La relación (2) da lugar a dos casos.
--
-- Caso 1: Supongamos que x ∈ t. Entonces, por (1), x ∈ s ∩ t y, por
-- tanto, x ∈ (s ∩ t) ∪ (s ∩ u).
--
-- Caso 2: Supongamos que x ∈ u. Entonces, por (1), x ∈ s ∩ u y, por
-- tanto, x ∈ (s ∩ t) ∪ (s ∩ u).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  rcases hx with ⟨hxs, hxtu⟩
  -- hxs : x ∈ s
  -- hxtu : x ∈ t ∪ u
  rcases hxtu with (hxt | hxu)
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- hxt : x ∈ t
      exact hxt
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- ⊢ x ∈ u
      exact hxu

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    exact ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    exact ⟨hxs, hxu⟩

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    exact Or.inl ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    exact Or.inr ⟨hxs, hxu⟩

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intro x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  aesop

-- 5ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw [inter_union_distrib_left]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ (s ∩ t) ∪ (s ∩ u). Entonces son posibles dos casos.
--
-- 1º caso: Supongamos que x ∈ s ∩ t. Entonces, x ∈ s y x ∈ t (y, por
-- tanto, x ∈ t ∪ u). Luego, x ∈ s ∩ (t ∪ u).
--
-- 2º caso: Supongamos que x ∈ s ∩ u. Entonces, x ∈ s y x ∈ u (y, por
-- tanto, x ∈ t ∪ u). Luego, x ∈ s ∩ (t ∪ u).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ (s ∩ t) ∪ (s ∩ u)
  -- ⊢ x ∈ s ∩ (t ∪ u)
  rcases hx with (xst | xsu)
  . -- xst : x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xst.2
  . -- xsu : x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact xsu.1
    . -- ⊢ x ∈ t ∪ u
      right
      -- ⊢ x ∈ u
      exact xsu.2

-- 2ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . -- x : α
    -- xs : x ∈ s
    -- xt : x ∈ t
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    left
    -- ⊢ x ∈ t
    exact xt
  . -- x : α
    -- xs : x ∈ s
    -- xu : x ∈ u
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 3ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by rw [inter_union_distrib_left s t u]

-- 4ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ t ∪ s ∩ u
  -- ⊢ x ∈ s ∩ (t ∪ u)
  aesop

-- Lemas usados
-- ============

variable (a b : Prop)
variable (u : Set α)
#check (Or.inl : a → a ∨ b)
#check (Or.inr : b → a ∨ b)
#check (inter_union_distrib_left s t u : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u))
