-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
-- 1. Importar la librería de los reales.
-- 2. Declarar f como variable de las funciones de ℝ en ℝ.
-- 3. Declarar a y b como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que no para toda f : ℝ → ℝ monótona,
--    (∀ a b)[f(a) ≤ f(b) → a ≤ b]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que
--    (∀f)[f es monótona → (∀a, b)[f(a) ≤ f(b) → a ≤ b]]             (1)
-- Sea f : ℝ → ℝ la función constante igual a cero (es decir,
--    (∀x ∈ ℝ)[f(x) = 0]
-- Entonces, f es monótona y f(1) ≤ f(0) (ya que
-- f(1) = 0 ≤ 0 = f(0)). Luego, por (1), 1 ≤ 0 que es una
-- contradicción.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example :
  ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
by
  intro h1
  -- h1 : ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b : ℝ}, f a ≤ f b → a ≤ b
  -- ⊢ False
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have h2 : Monotone f := monotone_const
  have h3 : f 1 ≤ f 0 := le_refl 0
  have h4 : (1 : ℝ) ≤ 0 := h1 h2 h3
  linarith

-- Lemas usados
-- ============

variable (a c : ℝ)
#check (le_refl a : a ≤ a)
#check (monotone_const : Monotone fun _ : ℝ ↦ c)
