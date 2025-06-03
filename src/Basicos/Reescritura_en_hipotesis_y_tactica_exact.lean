-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c y d son números reales tales que
--    c = d * a + b
--    b = a * d
-- entonces
--    c = 2 * a * d
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    c = da + b     [por la primera hipótesis]
--      = da + ad    [por la segunda hipótesis]
--      = ad + ad    [por la conmutativa]
--      = 2(ad)      [por la def. de doble]
--      = 2ad        [por la asociativa]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
calc
  c = d * a + b     := by rw [h1]
  _ = d * a + a * d := by rw [h2]
  _ = a * d + a * d := by rw [mul_comm d a]
  _ = 2 * (a * d)   := by rw [← two_mul (a * d)]
  _ = 2 * a * d     := by rw [mul_assoc]

-- 2ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by
  rw [h2] at h1
  -- h1 : c = d * a + a * d
  clear h2
  rw [mul_comm d a] at h1
  -- h1 : c = a * d + a * d
  rw [← two_mul (a*d)] at h1
  -- h1 : c = 2 * (a * d)
  rw [← mul_assoc 2 a d] at h1
  -- h1 : c = 2 * a * d
  exact h1

-- Comentarios
-- 1. La táctica (rw [e] at h) rescribe la parte izquierda de la
--    ecuación e por la derecha en la hipótesis h.
-- 2. La táctica (exact p) tiene éxito si el tipo de p se unifica con el
--    objetivo.
-- 3. La táctica (clear h) borra la hipótesis h.

-- 3ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by rw [h1, h2, mul_comm d a, ← two_mul (a * d), mul_assoc]

-- 4ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by
  rw [h1]
  -- ⊢ d * a + b = 2 * a * d
  rw [h2]
  -- ⊢ d * a + a * d = 2 * a * d
  ring

-- 5ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by
  rw [h1, h2]
  -- ⊢ d * a + a * d = 2 * a * d
  ring

-- 6ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by rw [h1, h2] ; ring

-- 7ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by linarith

-- Lemas usados
-- ============

#check (mul_assoc a b c : a * b * c = a * (b * c))
#check (mul_comm a b : a * b = b * a)
#check (two_mul a : 2 * a = a + a)
