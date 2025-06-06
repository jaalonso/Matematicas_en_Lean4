-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de los siguientes lemas
--    gcd_zero_right
--    gcd_zero_left
--    lcm_zero_right
--    lcm_zero_left
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

open Nat

variable (n : ℕ)

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n : lcm 0 n = 0)
