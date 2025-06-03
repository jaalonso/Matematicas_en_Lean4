-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los reales, si
--    x ≤ y ∧ x ≠ y
-- entonces
--    ¬ y ≤ x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que y ≤ x. Entonces, por la antisimetría y la primera
-- parte de la hipótesis, se tiene que x = y que contradice la segunda
-- parte de la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  rcases h with ⟨h2, h3⟩
  -- h2 : x ≤ y
  -- h3 : x ≠ y
  have h4 : x = y := le_antisymm h2 h1
  show False
  exact h3 h4

-- 2ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  -- h1 : y ≤ x
  -- ⊢ False
  have h4 : x = y := le_antisymm h.1 h1
  show False
  exact h.2 h4

-- 3ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  -- h1 : y ≤ x
  -- ⊢ False
  show False
  exact h.2 (le_antisymm h.1 h1)

-- 4ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
fun h1 ↦ h.2 (le_antisymm h.1 h1)

-- 5ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h'
  -- h' : y ≤ x
  -- ⊢ False
  apply h.right
  -- ⊢ x = y
  exact le_antisymm h.left h'

-- Comentario: Si h es una conjunción (P ∧ Q), entonces h.left es P y
-- h.right es Q.

-- 6ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  cases' h with h1 h2
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  contrapose! h2
  -- h2 : y ≤ x
  -- ⊢ x = y
  exact le_antisymm h1 h2

-- Comentario: La táctica (cases' h with h1 h2) si la hipótesis h es una
-- conjunción (P ∧ Q), aplica la regla de eliminación de la conjunción;
-- es decir, sustituye h por las hipótesis (h1 : P) y (h2 : Q).

-- 7ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩ h'
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  -- h' : y ≤ x
  -- ⊢ False
  exact h2 (le_antisymm h1 h')

-- Comentario: La táctica (rintro ⟨h1, h2⟩ h')
-- + si el objetivo es de la forma (P ∧ Q → (R → S)) añade las hipótesis
--   (h1 : P), (h2 : Q), (h' : R) y sustituye el objetivo por S.
-- + si el objetivo es de la forma (P ∧ Q → ¬R) añade las hipótesis
--   (h1 : P), (h2 : Q), (h' : R) y sustituye el objetivo por false.

-- 8ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
fun ⟨h1, h2⟩ h' ↦ h2 (le_antisymm h1 h')

-- Lemas usados
-- ============

#check (le_antisymm : x ≤ y → y ≤ x → x = y)
