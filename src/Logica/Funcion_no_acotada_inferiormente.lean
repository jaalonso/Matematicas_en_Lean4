-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función de ℝ en ℝ tal que
-- para cada a, existe un x tal que f x < a, entonces f no tiene cota
-- inferior.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f tiene cota inferior. Sea b una de dichas cotas
-- inferiores. Por la hipótesis, existe un x tal que f(x) < b. Además,
-- como b es una cota inferior de f, b ≤ f(x) que contradice la
-- desigualdad anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasLb (f : ℝ → ℝ) : Prop :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ FnHasLb f :=
by
  intros hf
  -- hf : FnHasLb f
  -- ⊢ False
  obtain ⟨b, hb⟩ := hf
  -- b : ℝ
  -- hb : FnLb f b
  obtain ⟨x, hx⟩ := h b
  -- x : ℝ
  -- hx : f x < b
  have : b ≤ f x := hb x
  linarith

-- 2ª demostración
-- ===============

example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ FnHasLb f :=
by
  intros hf
  -- hf : FnHasLb f
  -- ⊢ False
  rcases hf with ⟨b, hb⟩
  -- b : ℝ
  -- hb : FnLb f b
  rcases h b with ⟨x, hx⟩
  -- x : ℝ
  -- hx : f x < b
  have : b ≤ f x := hb x
  linarith
