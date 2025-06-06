-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de los números reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar a, b y c como variables sobre los reales.
-- ----------------------------------------------------------------------

variable (a b c : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar que
-- + h  es una variable de tipo a ≤ b
-- + h' es una variable de tipo b ≤ c
-- ----------------------------------------------------------------------

variable (h : a ≤ b) (h' : b ≤ c)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Calcular el tipo de las siguientes expresiones:
--    + le_refl
--    + le_refl a
--    + le_trans
--    + le_trans h
--    + le_trans h h'
-- ----------------------------------------------------------------------

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
