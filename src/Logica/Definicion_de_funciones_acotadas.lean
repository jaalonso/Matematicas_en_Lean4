import Mathlib.Data.Real.Basic

-- ---------------------------------------------------------------------
-- Ejercicio 1. Definir la función
--    FnUb (ℝ → ℝ) → ℝ → Prop
-- tal que (FnUb f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    FnLb (ℝ → ℝ) → ℝ → Prop
-- tal que (FnLb f a) afirma que a es una cota inferior de f.
-- ----------------------------------------------------------------------

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    FnHasUb (ℝ → ℝ) → Prop
-- tal que (FnHasUb f) afirma que f tiene cota superior.
-- ----------------------------------------------------------------------

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

-- ---------------------------------------------------------------------
-- Ejercicio 4. Definir la función
--    FnHasLb (ℝ → ℝ) → Prop
-- tal que (FnHasLb f) afirma que f tiene cota inferior.
-- ----------------------------------------------------------------------

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
