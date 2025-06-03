import Mathlib.Data.Set.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Set Real

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    sqrt '' { x | x ≥ 0 } = {y | y ≥ 0}
-- ----------------------------------------------------------------------

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
by
  ext y
  -- ⊢ y ∈ sqrt '' {x | x ≥ 0} ↔ y ∈ {y | y ≥ 0}
  constructor
  · -- ⊢ y ∈ sqrt '' {x | x ≥ 0} → y ∈ {y | y ≥ 0}
    rintro ⟨x, ⟨hx, rfl⟩⟩
    -- x : ℝ
    -- hx : x ∈ {x | x ≥ 0}
    -- ⊢ √x ∈ {y | y ≥ 0}
    apply sqrt_nonneg
  . -- ⊢ y ∈ {y | y ≥ 0} → y ∈ sqrt '' {x | x ≥ 0}
    intro hy
    -- hy : y ∈ {y | y ≥ 0}
    -- ⊢ y ∈ sqrt '' {x | x ≥ 0}
    dsimp at hy
    -- hy : y ≥ 0
    simp
    -- ⊢ ∃ x, 0 ≤ x ∧ √x = y
    use y ^ 2
    -- ⊢ 0 ≤ y ^ 2 ∧ √(y ^ 2) = y
    constructor
    . -- ⊢ 0 ≤ y ^ 2
      apply pow_nonneg hy
    . -- ⊢ √(y ^ 2) = y
      apply sqrt_sq
      -- ⊢ 0 ≤ y
      assumption

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (range fun x ↦ x ^ 2) = {y | y ≥ 0}
-- ----------------------------------------------------------------------

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } :=
by
  ext y
  -- ⊢ (y ∈ range fun x => x ^ 2) ↔ y ∈ {y | y ≥ 0}
  constructor
  · -- ⊢ (y ∈ range fun x => x ^ 2) → y ∈ {y | y ≥ 0}
    rintro ⟨x, rfl⟩
    -- x : ℝ
    -- ⊢ (fun x => x ^ 2) x ∈ {y | y ≥ 0}
    dsimp at *
    -- ⊢ x ^ 2 ≥ 0
    apply pow_two_nonneg
  . -- ⊢ y ∈ {y | y ≥ 0} → y ∈ range fun x => x ^ 2
    intro hy
    -- hy : y ∈ {y | y ≥ 0}
    -- ⊢ y ∈ range fun x => x ^ 2
    simp
    -- ⊢ ∃ y_1, y_1 ^ 2 = y
    use sqrt y
    -- ⊢ √y ^ 2 = y
    exact sq_sqrt hy

-- Lemas usados
-- ============

variable (x : ℝ)
#check (pow_nonneg : 0 ≤ x → ∀ n, 0 ≤ x ^ n)
#check (pow_two_nonneg x : 0 ≤ x ^ 2)
#check (sq_sqrt : 0 ≤ x → √x ^ 2 = x)
#check (sqrt_nonneg x : 0 ≤ √x)
#check (sqrt_sq : 0 ≤ x → √(x ^ 2) = x)
