-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--     ConvergesTo (ℕ → ℝ) → ℝ → Prop
-- tal que (ConvergesTo s a) afirma que a es el límite de s.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- #print ConvergesTo

-- Comentario: Al colocar el cursor sobre print se obtiene
--    def ConvergesTo : (ℕ → ℝ) → ℝ → Prop :=
--    fun s a => ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |s n - a| < ε
