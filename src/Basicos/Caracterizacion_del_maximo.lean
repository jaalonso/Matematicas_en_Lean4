-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Calcular los tipos de
--    le_max_left a b
--    le_max_right a b
--    @max_le ℝ _ a b c
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)
