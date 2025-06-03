import Mathlib.Algebra.Prime.Defs
import Mathlib.Data.Nat.Prime.Defs
variable (p : ℕ)

-- ---------------------------------------------------------------------
-- Ejercicio. En Mathlib hay dos definiciones de primo:
-- + (Nat.Prime p) indica que el número natural p es primo.
-- + (Prime p) indica que el número p (de un monoide conmutativo con
--    cero) es primo.
--
-- Demostrar que en los números naturales ambos conceptos coinciden.
-- ---------------------------------------------------------------------

example : Nat.Prime p ↔ Prime p :=
  Nat.prime_iff

example
  (h : Prime p)
  : Nat.Prime p :=
by
  rw [Nat.prime_iff]
  -- ⊢ Prime p
  exact h

example
  (h : Prime p)
  : Nat.Prime p :=
by
  rwa [Nat.prime_iff]

-- Lemas usados
-- ============

#check (Nat.prime_iff : Nat.Prime p ↔ Prime p)
