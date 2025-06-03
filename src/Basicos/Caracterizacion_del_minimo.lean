-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Calcular los tipos de
--    min_le_left a b
--    min_le_right a b
--    @le_min ℝ _ a b c
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
