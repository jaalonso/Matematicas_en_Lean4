-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función de ℝ en ℝ tal que
-- para cada a, existe un x tal que f x > a, entonces f no tiene cota
-- superior.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f tiene cota superior. Sea b una de dichas cotas
-- superiores. Por la hipótesis, existe un x tal que f(x) > b. Además,
-- como b es una cota superior de f, f(x) ≤ b que contradice la
-- desigualdad anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

theorem sinCotaSup
  (h : ∀ a, ∃ x, f x > a)
  : ¬ FnHasUb f :=
by
  intros hf
  -- hf : FnHasUb f
  -- ⊢ False
  rcases hf with ⟨b, hb⟩
  -- b : ℝ
  -- hb : FnUb f b
  rcases h b with ⟨x, hx⟩
  -- x : ℝ
  -- hx : f x > b
  have : f x ≤ b := hb x
  linarith
