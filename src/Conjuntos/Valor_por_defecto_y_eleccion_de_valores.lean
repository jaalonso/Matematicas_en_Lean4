-- ---------------------------------------------------------------------
-- Ejercicio. Declarar α como una variables de tipos habitados.
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Lattice

variable {α : Type u} [Inhabited α]

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--     default α
-- ----------------------------------------------------------------------

#check (default : α)

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar P como un predicado sobre α tal que existe algún
-- elemento que verifica P.
-- ----------------------------------------------------------------------

variable (P : α → Prop) (h : ∃ x, P x)

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    classical.some h
-- ----------------------------------------------------------------------

#check (Classical.choose h : α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    P (classical.some h)
-- ----------------------------------------------------------------------

example : P (Classical.choose h) :=
  Classical.choose_spec h

-- Lemas usados
-- ============

#check (Classical.choose_spec : (∃ x, P x) → P (Classical.choose h))
