-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de números reales.
-- 2. Abrir el espacio de nombre de las funciones.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic -- 1
open Function                  -- 2

variable {c : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que, para todo c la función
--    f(x) = x + c
-- es inyectiva
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el lema
--    (∀ a, b, c) [a + b = c + b → a = c]                            (L1)
-- Hay que demostrar que
--    (∀ x₁ x₂) [f(x₁) = f(x₂) → x₁ = x₂]
-- Sean x₁, x₂ tales que f(x₁) = f(x₂). Entonces,
--    x₁ + c = x₂ + c
-- y, por L1, x₁ = x₂.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : Injective ((. + c)) :=
by
  intro x1 x2 h1
  -- x1 x2 : ℝ
  -- h1 : (fun x => x + c) x1 = (fun x => x + c) x2
  -- ⊢ x1 = x2
  exact add_right_cancel h1

-- 2ª demostración
-- ===============

example : Injective ((. + c)) :=
  fun _ _ h ↦ add_right_cancel h

-- Lemas usados
-- ============

-- variable {a b : ℝ}
-- #check (add_right_cancel : a + b = c + b → a = c)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que para todo c distinto de cero la función
--    f(x) = c * x
-- es inyectiva
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el lema
--    (∀ a, b, c) [a ≠ 0 → (a * b = a * c ↔ b = c))]             (L1)
-- Hay que demostrar que
--    (∀ x₁, x₂) [f(x₁) = f(x₂) → x₁ = x₂]
-- Sean x₁, x₂ tales que f(x₁) = f(x₂). Entonces,
--    c * x₁ = c * x₂
-- y, por L1 y puesto que c ≠ 0, se tiene que
--    x₁ = x₂.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
by
  intro x1 x2 h1
  -- x1 x2 : ℝ
  -- h1 : (fun x => c * x) x1 = (fun x => c * x) x2
  -- ⊢ x1 = x2
  exact (mul_right_inj' h).mp h1

-- 2ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
fun _ _ h1 ↦ mul_left_cancel₀ h h1

-- Lemas usados
-- ============

variable (a b : ℝ)
#check (mul_right_inj' : a ≠ 0 → (a * b = a * c ↔ b = c))
#check (mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c)
#check (add_right_cancel : a + b = c + b → a = c)
