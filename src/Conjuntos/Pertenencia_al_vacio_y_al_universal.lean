-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacion de nombres set.
-- ----------------------------------------------------------------------

import Mathlib.Tactic

open Set

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar ningún elemento pertenece al vacío.
-- ----------------------------------------------------------------------

example (x : ℕ) : x ∉ (∅ : Set ℕ) :=
not_false

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : false :=
False.elim h

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar tofos los elementos pertenecen al universal.
-- ----------------------------------------------------------------------

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
trivial

-- Lemas usados
-- ============

variable (a : Prop)
#check (False.elim : False → a)
#check (not_false : ¬False)
#check (trivial : True)
