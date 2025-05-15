-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de grupo.
--    2. Crear el espacio de nombres Grupo
--    3. Declarar G como una variable sobre anillos.
--    4. Declarar a y b como variable sobre G.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Group.Defs -- 1
variable {G : Type _} [Group G]   -- 2
namespace Grupo                   -- 3
variable (a b : G)                -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a * a⁻¹ = 1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a·a⁻¹ = 1·(a·a⁻¹)                 [por producto con uno]
--          = (1·a)·a⁻¹                 [por asociativa]
--          = (((a⁻¹)⁻¹·a⁻¹) ·a)·a⁻¹    [por producto con inverso]
--          = ((a⁻¹)⁻¹·(a⁻¹ ·a))·a⁻¹    [por asociativa]
--          = ((a⁻¹)⁻¹·1)·a⁻¹           [por producto con inverso]
--          = (a⁻¹)⁻¹·(1·a⁻¹)           [por asociativa]
--          = (a⁻¹)⁻¹·a⁻¹               [por producto con uno]
--          = 1                         [por producto con inverso]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
theorem mul_right_inv : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by rw [one_mul]
        _ = (1 * a) * a⁻¹                := by rw [mul_assoc]
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by rw [mul_left_inv]
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by rw [← mul_assoc]
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by rw [mul_left_inv]
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by rw [mul_assoc]
        _ = (a⁻¹)⁻¹ * a⁻¹                := by rw [one_mul]
        _ = 1                            := by rw [mul_left_inv]

-- 2ª demostración
example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by simp
        _ = (1 * a) * a⁻¹                := by simp
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by simp
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by simp
        _ = (a⁻¹)⁻¹ * a⁻¹                := by simp
        _ = 1                            := by simp

-- 3ª demostración
example : a * a⁻¹ = 1 :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    a * 1 = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se tiene por la siguiente cadena de igualdades
--    a·1 = a·(a⁻¹·a)    [por producto con inverso]
--        = (a·a⁻¹)·a    [por asociativa]
--        = 1·a          [por producto con inverso]
--        = a            [por producto con uno]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
theorem mul_one : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by rw [mul_left_inv]
      _ = (a * a⁻¹) * a := by rw [mul_assoc]
      _ = 1 * a         := by rw [mul_right_inv]
      _ = a             := by rw [one_mul]

-- 2ª demostración
example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by simp
      _ = (a * a⁻¹) * a := by simp
      _ = 1 * a         := by simp
      _ = a             := by simp

-- 3ª demostración
example : a * 1 = a :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    b * a = 1
-- entonces
--    a⁻¹ = b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se tiene a partir de la siguente cadena de igualdades
--    a⁻¹ =  1·a⁻¹        [por producto por uno]
--        =  (b·a)·a⁻¹    [por hipótesis]
--        =  b·(a·a⁻¹)    [por asociativa]
--        =  b·1          [por producto con inverso]
--        =  b            [por producto por uno]

-- Demostraciones con Lean4
-- ========================

-- 1º demostración
lemma inv_eq_of_mul_eq_one
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       := by rw [one_mul]
    _ =  (b * a) * a⁻¹ := by rw [h]
    _ =  b * (a * a⁻¹) := by rw [mul_assoc]
    _ =  b * 1         := by rw [mul_right_inv]
    _ =  b             := by rw [mul_one]

-- 2º demostración
example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       := by simp
    _ =  (b * a) * a⁻¹ := by simp [h]
    _ =  b * (a * a⁻¹) := by simp
    _ =  b * 1         := by simp
    _ =  b             := by simp

-- 3º demostración
example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  (b * a) * a⁻¹ := by simp [h]
    _ =  b             := by simp

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Teniendo en cuenta la propiedad
--    ∀ a b ∈ R, ba = 1 → a⁻¹ = b :=
-- basta demostrar que
--    (b⁻¹a⁻¹)(ab) = 1
-- La identidad anterior se demuestra mediante la siguiente cadena de
-- igualdades
--    (b⁻¹a⁻¹)(ab) = b⁻¹(a⁻¹(ab))    [por la asociativa]
--                 = b⁻¹((a⁻¹a)b)    [por la asociativa]
--                 = b⁻¹(1b)         [por producto con inverso]
--                 = b⁻¹b            [por producto con uno]
--                 = 1               [por producto con inverso]

-- Demostraciones con Lean4
-- ========================

lemma mul_inv_rev_aux : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
calc
  (b⁻¹ * a⁻¹) * (a * b)
    = b⁻¹ * (a⁻¹ * (a * b)) := by rw [mul_assoc]
  _ = b⁻¹ * ((a⁻¹ * a) * b) := by rw [mul_assoc]
  _ = b⁻¹ * (1 * b)         := by rw [mul_left_inv]
  _ = b⁻¹ * b               := by rw [one_mul]
  _ = 1                     := by rw [mul_left_inv]

-- 1ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
    mul_inv_rev_aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  exact inv_eq_of_mul_eq_one (a * b) (b⁻¹ * a⁻¹) h1

-- 3ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
    mul_inv_rev_aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  simp [h1]

-- 4ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
    mul_inv_rev_aux a b
  simp [h1]

-- 5ª demostración
theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  apply inv_eq_of_mul_eq_one
  -- ⊢ (b⁻¹ * a⁻¹) * (a * b) = 1
  rw [mul_inv_rev_aux]

-- ---------------------------------------------------------------------
-- Ejercicio 6.  Cerrar el espacio de nombre Grupo.
-- ----------------------------------------------------------------------

end Grupo
