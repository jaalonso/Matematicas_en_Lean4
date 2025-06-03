-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar la siguientes acciones:
--    1. Importar la teoría de mcd sobre los naturales.
--    2. Declarar x, y y z como variables sobre los naturales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
variable (x y z : ℕ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x ∣ y
--    y ∣ z
-- entonces
--    x ∣ z
-- ----------------------------------------------------------------------

example
  (h₀ : x ∣ y)
  (h₁ : y ∣ z)
  : x ∣ z :=
dvd_trans h₀ h₁

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    x ∣ y * x * z
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la transitividad de la divisibilidad aplicada a las relaciones
--    x ∣ yx
--    yx ∣ yxz


-- 1ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  have h1 : x ∣ y * x :=
    dvd_mul_left x y
  have h2 : (y * x) ∣ (y * x * z) :=
    dvd_mul_right (y * x) z
  show x ∣ y * x * z
  exact dvd_trans h1 h2

-- 2ª demostración
-- ===============

example : x ∣ y * x * z :=
dvd_trans (dvd_mul_left x y) (dvd_mul_right (y * x) z)

-- 3ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  apply dvd_mul_of_dvd_left
  -- ⊢ x ∣ y * x
  apply dvd_mul_left

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si x ∈ ℕ, entonces
--    x ∣ x^2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se tiene que
--    x ∣ xx
-- y, por la definición del cuadrado,
--    x ∣ x²

-- 1ª demostración
-- ===============

example : x ∣ x^2 :=
by
  have : x ∣ x * x := dvd_mul_left x x
  show x ∣ x^2
  rwa [pow_two]

-- 2ª demostración
-- ===============

example : x ∣ x^2 :=
by
  rw [pow_two]
  -- ⊢ x ∣ x * x
  apply dvd_mul_right

-- 3ª demostración
-- ===============

example : x ∣ x^2 :=
by apply dvd_mul_left

-- Lemas usados
-- ============

variable (a b : ℕ)
#check (dvd_mul_left a b : a ∣ b * a)
#check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
#check (dvd_mul_right a b : a ∣ a * b)
#check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
#check (pow_two a : a ^ 2 = a * a)
