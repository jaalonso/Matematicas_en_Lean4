-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces
--    f ⁻¹' (f '' s) ⊆ s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x tal que
--    x ∈ f⁻¹[f[s]]
-- Entonces,
--    f(x) ∈ f[s]
-- y, por tanto, existe un
--    y ∈ s                                                          (1)
-- tal que
--    f(y) = f(x)                                                    (2)
-- De (2), puesto que f es inyectiva, se tiene que
--    y = x                                                          (3)
-- Finalmente, de (3) y (1), se tiene que
--    x ∈ s
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set Function

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

-- 1ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  have h1 : f x ∈ f '' s := mem_preimage.mp hx
  have h2 : ∃ y, y ∈ s ∧ f y = f x := (mem_image f s (f x)).mp h1
  obtain ⟨y, hy : y ∈ s ∧ f y = f x⟩ := h2
  obtain ⟨ys : y ∈ s, fyx : f y = f x⟩ := hy
  have h3 : y = x := h fyx
  show x ∈ s
  exact h3 ▸ ys

-- 2ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rw [mem_image] at hx
  -- hx : ∃ x_1, x_1 ∈ s ∧ f x_1 = f x
  rcases hx with ⟨y, hy⟩
  -- y : α
  -- hy : y ∈ s ∧ f y = f x
  rcases hy with ⟨ys, fyx⟩
  -- ys : y ∈ s
  -- fyx : f y = f x
  unfold Injective at h
  -- h : ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
  have h1 : y = x := h fyx
  rw [←h1]
  -- ⊢ y ∈ s
  exact ys

-- 3ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rcases hx with ⟨y, ys, fyx⟩
  -- y : α
  -- ys : y ∈ s
  -- fyx : f y = f x
  rw [←h fyx]
  -- ⊢ y ∈ s
  exact ys

-- 4ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  rintro x ⟨y, ys, hy⟩
  -- x y : α
  -- ys : y ∈ s
  -- hy : f y = f x
  -- ⊢ x ∈ s
  rw [←h hy]
  -- ⊢ y ∈ s
  exact ys

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[f⁻¹[u]]. Entonces existe un x tal que
--    x ∈ f⁻¹[u]                                                     (1)
--    f(x) = y                                                       (2)
-- Por (1),
--    f(x) ∈ u
-- y, por (2),
--    y ∈ u

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  obtain ⟨x : α, h1 : x ∈ f ⁻¹' u ∧ f x = y⟩ := h
  obtain ⟨hx : x ∈ f ⁻¹' u, fxy : f x = y⟩ := h1
  have h2 : f x ∈ u := mem_preimage.mp hx
  show y ∈ u
  exact fxy ▸ h2

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, h2⟩
  -- x : α
  -- h2 : x ∈ f ⁻¹' u ∧ f x = y
  rcases h2 with ⟨hx, fxy⟩
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, hx, fxy⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, fxy⟩
  -- y : β
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  -- ⊢ y ∈ u
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, rfl⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ f x ∈ u
  exact hx

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ u. Por ser f suprayectiva, exite un x tal que
--    f(x) = y                                                       (1)
-- Por tanto, x ∈ f⁻¹[u] y
--    f(x) ∈ f[f⁻¹[u]]                                               (2)
-- Finalmente, por (1) y (2),
--    y ∈ f[f⁻¹[u]]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  . -- ⊢ x ∈ f ⁻¹' u
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu
  . -- ⊢ f x = y
    exact fxy

-- 2ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  . show f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu
  . show f x = y
    exact fxy

-- 3ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  aesop

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    s ⊆ t
-- entonces
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s]. Entonces, existe un x tal que
--    x ∈ s                                                          (1)
--    f(x) = y                                                       (2)
-- Por (1) y la hipótesis,
--    x ∈ t                                                          (3)
-- Por (3),
--    f(x) ∈ f[t]                                                    (4)
-- y, por (2) y (4),
--    y ∈ f[t]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rw [mem_image] at hy
  -- hy : ∃ x, x ∈ s ∧ f x = y
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ t
    exact h xs
  . -- ⊢ f x = y
    exact fxy

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rcases hy with ⟨x, xs, fxy⟩
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  exact ⟨h xs, fxy⟩

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    u ⊆ v
-- entonces
--    f ⁻¹' u ⊆ f ⁻¹' v
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de implicaciones:
--    x ∈ f⁻¹[u] ⟹ f(x) ∈ u
--               ⟹ f(x) ∈ v      [porque u ⊆ v]
--               ⟹ x ∈ f⁻¹[v]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  have h1 : f x ∈ u := mem_preimage.mp hx
  have h2 : f x ∈ v := h h1
  show x ∈ f ⁻¹' v
  exact mem_preimage.mpr h2

-- 2ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply mem_preimage.mpr
  -- ⊢ f x ∈ v
  apply h
  -- ⊢ f x ∈ u
  apply mem_preimage.mp
  -- ⊢ x ∈ f ⁻¹' u
  exact hx

-- 3ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply h
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  exact h hx

-- 5ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
fun _ hx ↦ h hx

-- 6ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- 7ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
preimage_mono h

-- 8ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by tauto

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (u ∪ v) = (f ⁻¹' u) ∪ (f ⁻¹' v)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ f⁻¹[u ∪ v] ↔ x ∈ f⁻¹[u] ∪ f⁻¹[v]
-- Lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que x ∈ f⁻¹[u ∪ v]. Entonces, f(x) ∈ u ∪ v.
-- Distinguimos dos casos:
--
-- Caso 1: Supongamos que f(x) ∈ u. Entonces, x ∈ f⁻¹[u] y, por tanto,
-- x ∈ f⁻¹[u] ∪ f⁻¹[v].
--
-- Caso 2: Supongamos que f(x) ∈ v. Entonces, x ∈ f⁻¹[v] y, por tanto,
-- x ∈ f⁻¹[u] ∪ f⁻¹[v].
--
-- (⟸) Supongamos que x ∈ f⁻¹[u] ∪ f⁻¹[v]. Distinguimos dos casos.
--
-- Caso 1: Supongamos que x ∈ f⁻¹[u]. Entonces, f(x) ∈ u y, por tanto,
-- f(x) ∈ u ∪ v. Luego, x ∈ f⁻¹[u ∪ v].
--
-- Caso 2: Supongamos que x ∈ f⁻¹[v]. Entonces, f(x) ∈ v y, por tanto,
-- f(x) ∈ u ∪ v. Luego, x ∈ f⁻¹[u ∪ v].

-- Demostraciones con Lean4
-- ========================


-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
    intro h
    -- h : x ∈ f ⁻¹' (u ∪ v)
    -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
    rw [mem_preimage] at h
    -- h : f x ∈ u ∪ v
    rcases h with fxu | fxv
    . -- fxu : f x ∈ u
      left
      -- ⊢ x ∈ f ⁻¹' u
      apply mem_preimage.mpr
      -- ⊢ f x ∈ u
      exact fxu
    . -- fxv : f x ∈ v
      right
      -- ⊢ x ∈ f ⁻¹' v
      apply mem_preimage.mpr
      -- ⊢ f x ∈ v
      exact fxv
  . -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∪ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∪ v)
    rw [mem_preimage]
    -- ⊢ f x ∈ u ∪ v
    rcases h with xfu | xfv
    . -- xfu : x ∈ f ⁻¹' u
      rw [mem_preimage] at xfu
      -- xfu : f x ∈ u
      left
      -- ⊢ f x ∈ u
      exact xfu
    . -- xfv : x ∈ f ⁻¹' v
      rw [mem_preimage] at xfv
      -- xfv : f x ∈ v
      right
      -- ⊢ f x ∈ v
      exact xfv

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
    intros h
    -- h : x ∈ f ⁻¹' (u ∪ v)
    -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
    rcases h with fxu | fxv
    . -- fxu : f x ∈ u
      left
      -- ⊢ x ∈ f ⁻¹' u
      exact fxu
    . -- fxv : f x ∈ v
      right
      -- ⊢ x ∈ f ⁻¹' v
      exact fxv
  . -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∪ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∪ v)
    rcases h with xfu | xfv
    . -- xfu : x ∈ f ⁻¹' u
      left
      -- ⊢ f x ∈ u
      exact xfu
    . -- xfv : x ∈ f ⁻¹' v
      right
      -- ⊢ f x ∈ v
      exact xfv

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
    rintro (fxu | fxv)
    . -- fxu : f x ∈ u
      -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
      exact Or.inl fxu
    . -- fxv : f x ∈ v
      -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
      exact Or.inr fxv
  . -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
    rintro (xfu | xfv)
    . -- xfu : x ∈ f ⁻¹' u
      -- ⊢ x ∈ f ⁻¹' (u ∪ v)
      exact Or.inl xfu
    . -- xfv : x ∈ f ⁻¹' v
      -- ⊢ x ∈ f ⁻¹' (u ∪ v)
      exact Or.inr xfv

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
    aesop
  . -- ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
    aesop

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  aesop

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext ; aesop

-- 7ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext ; rfl

-- 8ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
rfl

-- 9ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
preimage_union

-- 10ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (s ∩ t) ⊆ (f '' s) ∩ (f '' t)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea tal que
--    y ∈ f[s ∩ t]
-- Por tanto, existe un x tal que
--   x ∈ s ∩ t                                                       (1)
--   f(x) = y                                                        (2)
-- Por (1), se tiene que
--   x ∈ s                                                           (3)
--   x ∈ t                                                           (4)
-- Por (2) y (3), se tiene
--   y ∈ f[s]                                                        (5)
-- Por (2) y (4), se tiene
--   y ∈ f[t]                                                        (6)
-- Por (5) y (6), se tiene
--   y ∈ f[s] ∩ f[t]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∩ t ∧ f x = y
  rcases hx with ⟨xst, fxy⟩
  -- xst : x ∈ s ∩ t
  -- fxy : f x = y
  constructor
  . -- ⊢ y ∈ f '' s
    use x
    -- ⊢ x ∈ s ∧ f x = y
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' t
    use x
    -- ⊢ x ∈ t ∧ f x = y
    constructor
    . -- ⊢ x ∈ t
      exact xst.2
    . -- ⊢ f x = y
      exact fxy

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- xs : x ∈ s
  -- xt : x ∈ t
  constructor
  . -- ⊢ y ∈ f '' s
    use x
  . -- ⊢ y ∈ f '' t
    use x

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; aesop

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces
--    (f '' s) ∩ (f '' t) ⊆ f '' (s ∩ t)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s] ∩ f[t]. Entonces, existen x₁ y x₂ tales que
--    x₁ ∈ s                                                         (1)
--    f(x₁) = y                                                      (2)
--    x₂ ∈ t                                                         (3)
--    f(x₂) = y                                                      (4)
-- De (2) y (4) se tiene que
--    f(x₁) = f(x₂)
-- y, por ser f inyectiva, se tiene que
--    x₁ = x₂
-- y, por (1), se tiene que
--    x₂ ∈ t
-- y, por (3), se tiene que
--    x₂ ∈ s ∩ t
-- Por tanto,
--    f(x₂) ∈ f[s ∩ t]
-- y, por (4),
--    y ∈ f[s ∩ t]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s ∩ f '' t
  -- ⊢ y ∈ f '' (s ∩ t)
  rcases hy with ⟨hy1, hy2⟩
  -- hy1 : y ∈ f '' s
  -- hy2 : y ∈ f '' t
  rcases hy1 with ⟨x1, hx1⟩
  -- x1 : α
  -- hx1 : x1 ∈ s ∧ f x1 = y
  rcases hx1 with ⟨x1s, fx1y⟩
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  rcases hy2 with ⟨x2, hx2⟩
  -- x2 : α
  -- hx2 : x2 ∈ t ∧ f x2 = y
  rcases hx2 with ⟨x2t, fx2y⟩
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  have h1 : f x1 = f x2 := Eq.trans fx1y fx2y.symm
  have h2 : x1 = x2 := h (congrArg f (h h1))
  have h3 : x2 ∈ s := by rwa [h2] at x1s
  have h4 : x2 ∈ s ∩ t := by exact ⟨h3, x2t⟩
  have h5 : f x2 ∈ f '' (s ∩ t) := mem_image_of_mem f h4
  show y ∈ f '' (s ∩ t)
  rwa [fx2y] at h5

-- 2ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s ∩ f '' t
  -- ⊢ y ∈ f '' (s ∩ t)
  rcases hy  with ⟨hy1, hy2⟩
  -- hy1 : y ∈ f '' s
  -- hy2 : y ∈ f '' t
  rcases hy1 with ⟨x1, hx1⟩
  -- x1 : α
  -- hx1 : x1 ∈ s ∧ f x1 = y
  rcases hx1 with ⟨x1s, fx1y⟩
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  rcases hy2 with ⟨x2, hx2⟩
  -- x2 : α
  -- hx2 : x2 ∈ t ∧ f x2 = y
  rcases hx2 with ⟨x2t, fx2y⟩
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  use x1
  -- ⊢ x1 ∈ s ∩ t ∧ f x1 = y
  constructor
  . -- ⊢ x1 ∈ s ∩ t
    constructor
    . -- ⊢ x1 ∈ s
      exact x1s
    . -- ⊢ x1 ∈ t
      convert x2t
      -- ⊢ x1 = x2
      apply h
      -- ⊢ f x1 = f x2
      rw [← fx2y] at fx1y
      -- fx1y : f x1 = f x2
      exact fx1y
  . -- ⊢ f x1 = y
    exact fx1y

-- 3ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  rintro y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩
  -- y : β
  -- x1 : α
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  -- x2 : α
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  -- ⊢ y ∈ f '' (s ∩ t)
  use x1
  -- ⊢ x1 ∈ s ∩ t ∧ f x1 = y
  constructor
  . -- ⊢ x1 ∈ s ∩ t
    constructor
    . -- ⊢ x1 ∈ s
      exact x1s
    . -- ⊢ x1 ∈ t
      convert x2t
      -- ⊢ x1 = x2
      apply h
      -- ⊢ f x1 = f x2
      rw [← fx2y] at fx1y
      -- fx1y : f x1 = f x2
      exact fx1y
  . -- ⊢ f x1 = y
    exact fx1y

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f '' s) \ (f '' t) ⊆ f '' (s \ t)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s] \ f[t]. Entonces,
--    y ∈ f[s]                                                       (1)
--    y ∉ f[t]                                                       (2)
-- Por (1), existe un x tal que
--    x ∈ s                                                          (3)
--    f(x) = y                                                       (4)
-- Por tanto, para demostrar que y ∈ f[s \ t], basta probar que
-- x ∉ t. Para ello, supongamos que x ∈ t. Entonces, por (4),
-- y ∈ f[t] en contradicción con (2).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  have h1 : x ∉ t := by
    intro xt
    -- xt : x ∈ t
    -- ⊢ False
    have h2 : f x ∈ f '' t := mem_image_of_mem f xt
    have h3 : y ∈ f '' t := by rwa [fxy] at h2
    show False
    exact ynft h3
  have h4 : x ∈ s \ t := mem_diff_of_mem xs h1
  have h5 : f x ∈ f '' (s \ t) := mem_image_of_mem f h4
  show y ∈ f '' (s \ t)
  rwa [fxy] at h5

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply ynft
      -- ⊢ y ∈ f '' t
      rw [←fxy]
      -- ⊢ f x ∈ f '' t
      apply mem_image_of_mem
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  rintro y ⟨⟨x, xs, fxy⟩, ynft⟩
  -- y : β
  -- ynft : ¬y ∈ f '' t
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (s \ t)
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  aesop

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
fun y ⟨⟨x, xs, fxy⟩, ynft⟩ ↦ ⟨x, by aesop⟩

-- 5ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f ⁻¹' u) \ (f ⁻¹' v) ⊆ f ⁻¹' (u \ v)
-- ----------------------------------------------------------------------

example : (f ⁻¹' u) \ (f ⁻¹' v) ⊆ f ⁻¹' (u \ v) :=
by
  rintro x ⟨hxu,hxv⟩
  -- x : α
  -- hxu : x ∈ f ⁻¹' u
  -- hxv : x ∉ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (u \ v)
  simp
  -- ⊢ f x ∈ u ∧ f x ∉ v
  constructor
  . -- ⊢ f x ∈ u
    exact hxu
  . -- ⊢ f x ∉ v
    intro h
    -- h : f x ∈ v
    -- ⊢ False
    apply hxv
    -- ⊢ x ∈ f ⁻¹' v
    exact h

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f '' s) ∩ v = f '' (s ∩ (f ⁻¹' v))
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para toda y,
--    y ∈ f[s] ∩ v ↔ y ∈ f[s ∩ f⁻¹[v]]
-- Lo haremos probando las dos implicaciones.
--
-- (⟹) Supongamos que y ∈ f[s] ∩ v. Entonces, se tiene que
--    y ∈ f[s]                                                       (1)
--    y ∈ v                                                          (2)
-- Por (1), existe un x tal que
--    x ∈ s                                                          (3)
--    f(x) = y                                                       (4)
-- Por (2) y (4),
--    f(x) ∈ v
-- y, por tanto,
--    x ∈ f⁻¹[v]
-- que, junto con (3), da
--    x ∈ s ∩ f⁻¹[v]
-- y, por tanto,
--    f(x) ∈ f[s ∩ f⁻¹[v]]
-- que, junto con (4), da
--    y ∈ f[s ∩ f⁻¹[v]]
--
-- (⟸) Supongamos que y ∈ f[s ∩ f⁻¹[v]]. Entonces, existe un x tal que
--    x ∈ s ∩ f⁻¹[v]                                                 (5)
--    f(x) = y                                                       (6)
-- Por (1), se tiene que
--    x ∈ s                                                          (7)
--    x ∈ f⁻¹[v]                                                     (8)
-- Por (7) se tiene que
--    f(x) ∈ f[s]
-- y, junto con (6), se tiene que
--    y ∈ f[s]                                                       (9)
-- Por (8), se tiene que
--    f(x) ∈ v
-- y, junto con (6), se tiene que
--    y ∈ v                                                         (10)
-- Por (9) y (19), se tiene que
--    y ∈ f[s] ∩ v

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  have h1 : y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v) := by
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    have h1a : y ∈ f '' s := hy.1
    obtain ⟨x : α, hx: x ∈ s ∧ f x = y⟩ := h1a
    have h1b : x ∈ s := hx.1
    have h1c : f x = y := hx.2
    have h1d : y ∈ v := hy.2
    have h1e : f x ∈ v := by rwa [←h1c] at h1d
    have h1f : x ∈ s ∩ f ⁻¹' v := mem_inter h1b h1e
    have h1g : f x ∈ f '' (s ∩ f ⁻¹' v) := mem_image_of_mem f h1f
    show y ∈ f '' (s ∩ f ⁻¹' v)
    rwa [h1c] at h1g
  have h2 : y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v :=  by
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    obtain ⟨x : α, hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y⟩ := hy
    have h2a : x ∈ s := hx.1.1
    have h2b : f x ∈ f '' s := mem_image_of_mem f h2a
    have h2c : y ∈ f '' s := by rwa [hx.2] at h2b
    have h2d : x ∈ f ⁻¹' v := hx.1.2
    have h2e : f x ∈ v := mem_preimage.mp h2d
    have h2f : y ∈ v := by rwa [hx.2] at h2e
    show y ∈ f '' s ∩ v
    exact mem_inter h2c h2f
  show y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  exact ⟨h1, h2⟩

-- 2ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    cases' hy with hyfs yv
    -- hyfs : y ∈ f '' s
    -- yv : y ∈ v
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ y ∈ f '' s
      use x
      -- ⊢ x ∈ s ∧ f x = y
      constructor
      . -- ⊢ x ∈ s
        exact hx.1.1
      . -- ⊢ f x = y
        exact hx.2
    . -- ⊢ y ∈ v
      cases' hx with hx1 fxy
      -- hx1 : x ∈ s ∩ f ⁻¹' v
      -- fxy : f x = y
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact hx1.2

-- 3ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    constructor
    . -- ⊢ y ∈ f '' s
      use x, xs
    . -- ⊢ y ∈ v
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact xv

-- 4ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    aesop
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    aesop

-- 5ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by ext ; constructor <;> aesop

-- 6ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
(image_inter_preimage f s v).symm

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (s ∩ f ⁻¹' u) ⊆ (f '' s) ∪ u
-- ----------------------------------------------------------------------

example : f '' (s ∩ f ⁻¹' u) ⊆ (f '' s) ∪ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (s ∩ f ⁻¹' u)
  -- ⊢ y ∈ f '' s ∪ u
  rcases h with ⟨x,⟨xs,xu⟩,fxy⟩
  -- x : α
  -- fxy : f x = y
  -- xs : x ∈ s
  -- xu : x ∈ f ⁻¹' u
  right
  -- ⊢ y ∈ u
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact xu

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∩ u) :=
-- ----------------------------------------------------------------------

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∩ u) :=
by
  rintro x ⟨xs,xu⟩
  -- x : α
  -- xs : x ∈ s
  -- xu : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' (f '' s ∩ u)
  simp at xu
  -- xu : f x ∈ u
  constructor
  . -- ⊢ f x ∈ f '' s
    exact mem_image_of_mem f xs
  . -- ⊢ f x ∈ u
    exact xu

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∪ f ⁻¹' v ⊆ f ⁻¹' ((f '' s) ∪ v)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s ∪ f⁻¹[v]. Entonces, se puede dar dos casos.
--
-- Caso 1: Supongamos que x ∈ s. Entonces, se tiene
--    f(x) ∈ f[s]
--    f(x) ∈ f[s] ∪ v
--    x ∈ f⁻¹[f[s] ∪ v]
--
-- Caso 2: Supongamos que x ∈ f⁻¹[v]. Entonces, se tiene
--    f(x) ∈ v
--    f(x) ∈ f[s] ∪ v
--    x ∈ f⁻¹[f[s] ∪ v]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  rcases hx with xs | xv
  . -- xs : x ∈ s
    have h1 : f x ∈ f '' s := mem_image_of_mem f xs
    have h2 : f x ∈ f '' s ∪ v := mem_union_left v h1
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h2
  . -- xv : x ∈ f ⁻¹' v
    have h3 : f x ∈ v := mem_preimage.mp xv
    have h4 : f x ∈ f '' s ∪ v := mem_union_right (f '' s) h3
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h4

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  rw [mem_preimage]
  -- ⊢ f x ∈ f '' s ∪ v
  rcases hx with xs | xv
  . -- xs : x ∈ s
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- xv : x ∈ f ⁻¹' v
    apply mem_union_right
    -- ⊢ f x ∈ v
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' v
    exact xv

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  rcases hx with xs | xv
  . -- xs : x ∈ s
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_right
    -- ⊢ f x ∈ v
    exact xv

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    left
    -- ⊢ f x ∈ f '' s
    exact mem_image_of_mem f xs
  . -- xv : x ∈ f ⁻¹' v
    right
    -- ⊢ f x ∈ v
    exact xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    exact Or.inl (mem_image_of_mem f xs)
  . -- xv : x ∈ f ⁻¹' v
    exact Or.inr xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x h
  -- x : α
  -- h : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  exact Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
fun _ h ↦ Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
union_preimage_subset s v f

-- Lemas usados
-- ============

variable (x : α)
variable (z : β)
variable (t : Set α)
variable (a b c : Prop)
#check (Eq.trans : a = b → b = c → a = c)
#check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
#check (Or.inl : a → a ∨ b)
#check (Or.inr : b → a ∨ b)
#check (image_inter_preimage f s v : f '' (s ∩ f ⁻¹' v) = f '' s ∩ v)
#check (image_inter_subset f s t : f '' (s ∩ t) ⊆ f '' s ∩ f '' t)
#check (image_preimage_subset f u : f '' (f⁻¹' u) ⊆ u)
#check (image_subset f : s ⊆ t → f '' s ⊆ f '' t)
#check (mem_diff_of_mem : x ∈ s → x ∉ t → x ∈ s \ t)
#check (mem_image f s z : (z ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = z))
#check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
#check (mem_inter : x ∈ s → x ∈ t → x ∈ s ∩ t)
#check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
#check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
#check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
#check (preimage_mono : u ⊆ v → f ⁻¹' u ⊆ f ⁻¹' v)
#check (preimage_union : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v)
#check (subset_image_diff f s t : f '' s \ f '' t ⊆ f '' (s \ t))
#check (union_preimage_subset s v f : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v))
