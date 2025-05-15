-- ---------------------------------------------------------------------
-- Ejercicio . Demostrar que, para todo númeo real a,
--    0 ≤ a^2
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a : ℝ) : 0 ≤ a^2 :=
by
  -- apply?
  exact sq_nonneg a

-- Notas:
-- + Nota 1: Al colocar el cursor sobre apply? (después de descomentar
--   la línea) escribe el mensaje
--      Try this: exact sq_nonneg a
-- + Nota 2: Para usar apply? hay que importar Mathlib.Tactic.
