-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
-- 1. Importar la librería de los reales.
-- 2. Declarar a y b como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de los siguientes lemas
--    not_le_of_gt
--    not_lt_of_ge
--    lt_of_not_ge
--    le_of_not_gt
-- ----------------------------------------------------------------------

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)
