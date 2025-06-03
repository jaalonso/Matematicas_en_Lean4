import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

variable (x y : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que (∃x ∈ ℝ)[2 < x < 3]
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Podemos usar el número 5/2 y comprobar que 2 < 5/2 < 3.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  show 2 < 5 / 2 ∧ 5 / 2 < 3
  constructor
  . show 2 < 5 / 2
    norm_num
  . show 5 / 2 < 3
    norm_num

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  constructor
  . norm_num
  . norm_num

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  constructor <;> norm_num

-- 4ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5/2, by norm_num⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si (∃z ∈ ℝ)[x < z < y], entonces x < y.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea z tal que verifica las siguientes relaciones:
--    x < z                                                          (1)
--    z < y                                                          (2)
-- Aplicando la propiedad transitiva a (1) y (2) se tiene que
--    x < y.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1 : x < z, h2 : z < y⟩
  show x < y
  exact lt_trans h1 h2

-- 2ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1, h2⟩
  exact lt_trans h1 h2

-- 3ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
fun ⟨_, h1, h2⟩ ↦ lt_trans h1 h2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que existen números primos m y n tales que
-- 4 < m < n < 10.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Basta considerar los números 5 y 7, ya que son primos y
-- 4 < 5 < 7 < 10.

-- Demostración con Lean4
-- ======================

example :
  ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n :=
by
  use 5, 7
  -- ⊢ 4 < 5 ∧ 5 < 7 ∧ 7 < 10 ∧ Nat.Prime 5 ∧ Nat.Prime 7
  norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que
--    x ≤ y                                                          (1)
--    x ≠ y                                                          (2)
-- Entonces, se tiene x ≤ y (por (1)) y, para probar y ≰ x, supongamos
-- que y ≤ x. Por (1), se tiene que x = y, en contradicción con (2).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    have h4 : x = y := le_antisymm h1 h3
    show False
    exact h2 h4

-- 2ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    show False
    exact h2 (le_antisymm h1 h3)

-- 3ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 4ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 5ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
  fun ⟨h1, h2⟩ ↦ ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 6ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  use h1
  exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 7ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  use h1
  -- ¬y ≤ x
  contrapose! h2
  -- h2 : y ≤ x
  -- ⊢ x = y
  apply le_antisymm h1 h2

-- Lemas usados
-- ============

variable (z : ℝ)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)
#check (lt_trans : x < y → y < z → x < z)
