-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, para todo a ∈ ℝ, la sucesión constante
--    s(n) = a
-- converge a a.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_convergencia
variable (a : ℝ)

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada ε ∈ ℝ tal que ε > 0, existe un
-- N ∈ ℕ, tal que (∀n ∈ ℕ)[n ≥ N → |s(n) - a| < ε]. Basta tomar N como
-- 0, ya que para todo n ≥ N se tiene
--    |s(n) - a| = |a - a|
--               = |0|
--               = 0
--               < ε

-- 1ª demostración
-- ===============

example : ConvergesTo (fun _ : ℕ ↦ a) a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun x => a) n - a| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun x => a) n - a| < ε
  intros n _hn
  -- n : ℕ
  -- nge : n ≥ 0
  -- ⊢ |(fun x => a) n - a| < ε
  show |(fun _ => a) n - a| < ε
  calc |(fun _ => a) n - a| = |a - a| := by dsimp
                          _ = |0|     := by {congr ; exact sub_self a}
                          _ = 0       := abs_zero
                          _ < ε       := hε

-- 2ª demostración
-- ===============

example : ConvergesTo (fun _ : ℕ ↦ a) a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun x => a) n - a| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun x => a) n - a| < ε
  intros n _hn
  -- n : ℕ
  -- nge : n ≥ 0
  -- ⊢ |(fun x => a) n - a| < ε
  dsimp
  -- ⊢ |a - a| < ε
  rw [sub_self]
  -- ⊢ |0| < ε
  rw [abs_zero]
  -- ⊢ 0 < ε
  exact hε

-- Lemas usados
-- ============

-- #check (sub_self a : a - a = 0)
