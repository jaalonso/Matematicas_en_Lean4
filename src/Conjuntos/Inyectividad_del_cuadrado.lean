import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Set Real

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función raíz cuadrada es inyectiva sobre
-- los números no negativos.
-- ----------------------------------------------------------------------

example : InjOn sqrt { x | x ≥ 0 } :=
by
  intro x hx y hy
  -- x : ℝ
  -- hx : x ∈ {x | x ≥ 0}
  -- y : ℝ
  -- hy : y ∈ {x | x ≥ 0}
  intro e
  -- e : √x = √y
  -- ⊢ x = y
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt hx]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt hy]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función cuadrado es inyectiva sobre
-- los números no negativos.
-- ----------------------------------------------------------------------

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } :=
by
  intro x hx y hy
  -- x : ℝ
  -- hx : x ∈ {x | x ≥ 0}
  -- y : ℝ
  -- hy : y ∈ {x | x ≥ 0}
  -- ⊢ (fun x => x ^ 2) x = (fun x => x ^ 2) y → x = y
  intro e
  -- e : (fun x => x ^ 2) x = (fun x => x ^ 2) y
  -- ⊢ x = y
  dsimp at *
  -- hx : x ≥ 0
  -- hy : y ≥ 0
  -- e : x ^ 2 = y ^ 2
  -- ⊢ x = y
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq hx]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq hy]

-- Lemas usados
-- ============

variable (x : ℝ)
#check (sq_sqrt : 0 ≤ x → √x ^ 2 = x)
#check (sqrt_sq : 0 ≤ x → √(x ^ 2) = x)
