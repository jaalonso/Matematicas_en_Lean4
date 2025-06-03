-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--     limite (ℕ → ℝ) → ℝ → Prop
-- tal que (limite s a) afirma que a es el límite de s.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

#print limite

-- Comentario: Al colocar el cursor sobre print se obtiene
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--    fun s a => ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
