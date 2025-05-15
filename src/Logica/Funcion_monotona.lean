-- ---------------------------------------------------------------------
-- Ejercicio. Explicitar la definición de función monótona poniendo el
-- nombre en la hipótesis y su definición en la conclusión.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

example
  (f : ℝ → ℝ)
  (h : Monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b :=
@h
