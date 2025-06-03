-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a y b son números reales, entonces
--    (a + b) * (a - b) = a^2 - b^2
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    (a + b)(a - b)
--    = a(a - b) + b(a - b)            [por la distributiva]
--    = (aa - ab) + b(a - b)           [por la distributiva]
--    = (a^2 - ab) + b(a - b)          [por def. de cuadrado]
--    = (a^2 - ab) + (ba - bb)         [por la distributiva]
--    = (a^2 - ab) + (ba - b^2)        [por def. de cuadrado]
--    = (a^2 + -(ab)) + (ba - b^2)     [por def. de resta]
--    = a^2 + (-(ab) + (ba - b^2))     [por la asociativa]
--    = a^2 + (-(ab) + (ba + -b^2))    [por def. de resta]
--    = a^2 + ((-(ab) + ba) + -b^2)    [por la asociativa]
--    = a^2 + ((-(ab) + ab) + -b^2)    [por la conmutativa]
--    = a^2 + (0 + -b^2)               [por def. de opuesto]
--    = (a^2 + 0) + -b^2               [por asociativa]
--    = a^2 + -b^2                     [por def. de cero]
--    = a^2 - b^2                      [por def. de resta]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- 1ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by rw [add_mul]
  _ = (a * a - a * b) + b * (a - b)     := by rw [mul_sub]
  _ = (a^2 - a * b) + b * (a - b)       := by rw [← pow_two]
  _ = (a^2 - a * b) + (b * a - b * b)   := by rw [mul_sub]
  _ = (a^2 - a * b) + (b * a - b^2)     := by rw [← pow_two]
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by rw [add_assoc]
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by rw [← add_assoc
                                              (-(a * b)) (b * a) (-b^2)]
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by rw [mul_comm]
  _ = a^2 + (0 + -b^2)                  := by rw [neg_add_cancel (a * b)]
  _ = (a^2 + 0) + -b^2                  := by rw [← add_assoc]
  _ = a^2 + -b^2                        := by rw [add_zero]
  _ = a^2 - b^2                         := by linarith

-- 2ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by ring
  _ = (a * a - a * b) + b * (a - b)     := by ring
  _ = (a^2 - a * b) + b * (a - b)       := by ring
  _ = (a^2 - a * b) + (b * a - b * b)   := by ring
  _ = (a^2 - a * b) + (b * a - b^2)     := by ring
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by ring
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by ring
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by ring
  _ = a^2 + (0 + -b^2)                  := by ring
  _ = (a^2 + 0) + -b^2                  := by ring
  _ = a^2 + -b^2                        := by ring
  _ = a^2 - b^2                         := by ring

-- 3ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

-- 4ª demostración (por reescritura usando el lema anterior)
-- =========================================================

-- El lema anterior es
lemma aux : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- La demostración es
example : (a + b) * (a - b) = a^2 - b^2 :=
by
  rw [sub_eq_add_neg]
  -- ⊢ (a + b) * (a + -b) = a ^ 2 - b ^ 2
  rw [aux]
  -- ⊢ a * a + a * -b + b * a + b * -b = a ^ 2 - b ^ 2
  rw [mul_neg]
  -- ⊢ a * a + -(a * b) + b * a + b * -b = a ^ 2 - b ^ 2
  rw [add_assoc (a * a)]
  -- ⊢ a * a + (-(a * b) + b * a) + b * -b = a ^ 2 - b ^ 2
  rw [mul_comm b a]
  -- ⊢ a * a + (-(a * b) + a * b) + b * -b = a ^ 2 - b ^ 2
  rw [neg_add_cancel]
  -- ⊢ a * a + 0 + b * -b = a ^ 2 - b ^ 2
  rw [add_zero]
  -- ⊢ a * a + b * -b = a ^ 2 - b ^ 2
  rw [← pow_two]
  -- ⊢ a ^ 2 + b * -b = a ^ 2 - b ^ 2
  rw [mul_neg]
  -- ⊢ a ^ 2 + -(b * b) = a ^ 2 - b ^ 2
  rw [← pow_two]
  -- ⊢ a ^ 2 + -b ^ 2 = a ^ 2 - b ^ 2
  rw [← sub_eq_add_neg]

-- Lemas usados
-- ============

#check (add_assoc a b c    : (a + b) + c = a + (b + c))
#check (add_mul a b c      : (a + b) * c = a * c + b * c)
#check (add_sub a b c      : a + (b - c) = a + b - c)
#check (add_zero a         : a + 0 = a)
#check (mul_comm a b       : a * b = b * a)
#check (mul_neg a b        : a * -b = -(a * b))
#check (mul_sub a b c      : a * (b - c) = a * b - a * c)
#check (neg_add_cancel a   : -a + a = 0)
#check (sub_eq_add_neg a b : a - b = a + -b)
#check (pow_two a          : a ^ 2 = a * a)
#check (sub_sub a b c      : (a - b) - c = a - (b + c))
