-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si c es no negativo y f es monótona,
-- entonces c * f es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el Lema
--    mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c
--
-- Tenemos que demostrar que
--    (∀ a, b ∈ ℝ) [a ≤ b → (cf)(a) ≤ (cf)(b)]
-- Sean a, b ∈ ℝ tales que a ≤ b. Puesto que f es monótona, se tiene
--    f(a) ≤ f(b).
-- y, junto con la hipótesis de que c es no negativo, usando el lema
-- mul_le_mul_of_nonneg_left, se tiene que
--    cf(a) ≤ cf(b)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (f : ℝ → ℝ)
variable {c : ℝ}

-- 1ª demostración
-- ===============

example
  (mf : Monotone f)
  (nnc : 0 ≤ c)
  : Monotone (fun x ↦ c * f x) :=
by
  have h1 : ∀ a b, a ≤ b → (fun x ↦ c * f x) a ≤ (fun x ↦ c * f x) b := by
    intros a b hab
    -- a b : ℝ
    -- hab : a ≤ b
    -- ⊢ (fun x => c * f x) a ≤ (fun x => c * f x) b
    have h2 : f a ≤ f b := mf hab
    show (fun x ↦ c * f x) a ≤ (fun x ↦ c * f x) b
    exact mul_le_mul_of_nonneg_left h2 nnc
  show Monotone (fun x ↦ c * f x)
  exact h1

-- 2ª demostración
-- ===============

example
  (mf : Monotone f)
  (nnc : 0 ≤ c)
  : Monotone (fun x ↦ c * f x) :=
by
  intros a b hab
    -- a b : ℝ
    -- hab : a ≤ b
    -- ⊢ (fun x => c * f x) a ≤ (fun x => c * f x) b
  apply mul_le_mul_of_nonneg_left
  . -- ⊢ f a ≤ f b
    apply mf hab
  . -- ⊢ 0 ≤ c
    apply nnc

-- 3ª demostración
-- ===============

example (mf : Monotone f) (nnc : 0 ≤ c) :
  Monotone (fun x ↦ c * f x) :=
λ _ _ hab ↦ mul_le_mul_of_nonneg_left (mf hab) nnc

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c)
