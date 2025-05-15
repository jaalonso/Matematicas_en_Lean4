-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de los números reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    FnUb (ℝ → ℝ) → ℝ → Prop
-- tal que (FnUb f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    FnLb (ℝ → ℝ) → ℝ → Prop
-- tal que (FnLb f a) afirma que a es una cota inferior de f.
-- ----------------------------------------------------------------------

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
