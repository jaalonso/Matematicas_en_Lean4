-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a y b son números reales, entonces
--    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    (a + b)(a + b)
--    = (a + b)a + (a + b)b    [por la distributiva]
--    = aa + ba + (a + b)b     [por la distributiva]
--    = aa + ba + (ab + bb)    [por la distributiva]
--    = aa + ba + ab + bb      [por la asociativa]
--    = aa + (ba + ab) + bb    [por la asociativa]
--    = aa + (ab + ab) + bb    [por la conmutativa]
--    = aa + 2(ab) + bb        [por def. de doble]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

-- 1ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
    = (a + b) * a + (a + b) * b       := by rw [mul_add]
  _ = a * a + b * a + (a + b) * b     := by rw [add_mul]
  _ = a * a + b * a + (a * b + b * b) := by rw [add_mul]
  _ = a * a + b * a + a * b + b * b   := by rw [←add_assoc]
  _ = a * a + (b * a + a * b) + b * b := by rw [add_assoc (a * a)]
  _ = a * a + (a * b + a * b) + b * b := by rw [mul_comm b a]
  _ = a * a + 2 * (a * b) + b * b     := by rw [←two_mul]

-- 2ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
    = a * a + b * a + (a * b + b * b) := by rw [mul_add, add_mul, add_mul]
  _ = a * a + (b * a + a * b) + b * b := by rw [←add_assoc, add_assoc (a * a)]
  _ = a * a + 2 * (a * b) + b * b     := by rw [mul_comm b a, ←two_mul]

-- 3ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
    = a * a + b * a + (a * b + b * b) := by ring
  _ = a * a + (b * a + a * b) + b * b := by ring
  _ = a * a + 2 * (a * b) + b * b     := by ring

-- 4ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

-- 5ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by
  rw [mul_add]
  -- ⊢ (a + b) * a + (a + b) * b = a * a + 2 * (a * b) + b * b
  rw [add_mul]
  -- ⊢ a * a + b * a + (a + b) * b = a * a + 2 * (a * b) + b * b
  rw [add_mul]
  -- ⊢ a * a + b * a + (a * b + b * b) = a * a + 2 * (a * b) + b * b
  rw [←add_assoc]
  -- ⊢ a * a + b * a + a * b + b * b = a * a + 2 * (a * b) + b * b
  rw [add_assoc (a * a)]
  -- ⊢ a * a + (b * a + a * b) + b * b = a * a + 2 * (a * b) + b * b
  rw [mul_comm b a]
  -- ⊢ a * a + (a * b + a * b) + b * b = a * a + 2 * (a * b) + b * b
  rw [←two_mul]

-- 6ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by
  rw [mul_add, add_mul, add_mul]
  -- ⊢ a * a + b * a + (a * b + b * b) = a * a + 2 * (a * b) + b * b
  rw [←add_assoc, add_assoc (a * a)]
  -- ⊢ a * a + (b * a + a * b) + b * b = a * a + 2 * (a * b) + b * b
  rw [mul_comm b a, ←two_mul]

-- Lemas usados
-- ============

#check (add_assoc a b c : a + b + c = a + (b + c))
#check (add_mul a b c   : (a + b) * c = a * c + b * c)
#check (mul_add a b c   : a * (b + c) = a * b + a * c)
#check (mul_comm a b    : a * b = b * a)
#check (two_mul a       : 2 * a = a + a)
