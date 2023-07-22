-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d, e y f son números reales
-- tales que
--    b * c = e * f
-- entonces
--    ((a * b) * c) * d = ((a * e) * f) * d
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    ((ab)c)d
--    = (a(bc))d    [por la asociativa]
--    = (a(ef))d    [por la hipótesis]
--    = ((ae)f)d    [por la asociativa]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
calc
  ((a * b) * c) * d
    = (a * (b * c)) * d := by rw [mul_assoc a]
  _ = (a * (e * f)) * d := by rw [h]
  _ = ((a * e) * f) * d := by rw [←mul_assoc a]

-- 2ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by
  rw [mul_assoc a]
  rw [h]
  rw [←mul_assoc a]

-- El desarrollo de la prueba es
--
-- inicio
--    a b c d e f : ℝ,
--    h : b * c = e * f
--    ⊢ (a * (b * c)) * d = ((a * e) * f) * d
-- rw [mul_assoc a]
--    S
--    ⊢ a * (b * c) * d = a * e * f * d
-- rw [h]
--    S
--    ⊢ a * (e * f) * d = a * e * f * d
-- rw [←mul_assoc a]
--    goals accomplished
--
-- En el desarrollo anterior, S es el conjunto de hipótesis; es decir,
--    S = {a b c d e f : ℝ,
--         h : b * c = e * f}
