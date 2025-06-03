-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la unicidad de los límites de las sucesiones
-- convergentes.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_convergencia
import Mathlib.Tactic

theorem unicidad_limite
  {s : ℕ → ℝ}
  {a b : ℝ}
  (sa : limite s a)
  (sb : limite s b)
  : a = b :=
by
  by_contra abne
  -- abne : ¬a = b
  -- ⊢ False
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    -- ⊢ a - b ≠ 0
    exact sub_ne_zero_of_ne abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    -- ⊢ |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |s n - a| < ε
  rcases sb ε εpos with ⟨Nb, hNb⟩
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |s n - b| < ε
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    specialize hNa N
    -- hNa : N ≥ Na → |s N - a| < ε
    apply hNa
    -- ⊢ N ≥ Na
    exact le_max_left Na Nb
  have absb : |s N - b| < ε := by
    specialize hNb N
    -- hNb : N ≥ Nb → |s N - b| < ε
    apply hNb
    -- ⊢ N ≥ Nb
    exact le_max_right Na Nb
  have : |a - b| < |a - b| :=
    calc |a - b|
         = |(a - s N) + (s N - b)|  := by {congr; ring_nf}
       _ ≤ |a - s N| + |s N - b|    := abs_add (a - s N) (s N - b)
       _ = |s N - a| + |s N - b|    := by rw [abs_sub_comm]
       _ < ε + ε                    := by exact add_lt_add absa absb
       _ = |a - b|                  := by exact add_halves (abs (a - b))
  exact lt_irrefl _ this

-- Lemas usados
-- ============

variable (a b c d : ℝ)
#check (abs_add a b : |a + b| ≤ |a| + |b|)
#check (abs_pos : 0 < |a| ↔ a ≠ 0)
#check (abs_sub_comm a b : |a - b| = |b - a|)
#check (add_halves a : a / 2 + a / 2 = a)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (sub_ne_zero_of_ne : a ≠ b → a - b ≠ 0)
