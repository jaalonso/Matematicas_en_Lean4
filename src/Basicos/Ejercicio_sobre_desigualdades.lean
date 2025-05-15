-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de exponeciales y logaritmos.
--    2. Abrir la teoría de los reales
--    3. Declarar a, b, c, d y e como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b c d f : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    d ≤ f
-- entonces
--    c + exp (a + d) ≤ c + exp (a + f)
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- De la hipótesis, por la monotonia de la suma, se tiene
--    a + d ≤ a + f
-- que, por la monotonía de la exponencial, da
--    exp (a + d) ≤ exp (a + f)
-- y, por la monotonía de la suma, se tiene
--    c + exp (a + d) ≤ c + exp (a + f)

-- 2ª demostración en LN
-- =====================

-- Tenemos que demostrar que
--    c + exp (a + d) ≤ c + exp (a + f)
-- Por la monotonía de la suma, se reduce a
--    exp (a + d) ≤ exp (a + f)
-- que, por la monotonía de la exponencial, se reduce a
--    a + d ≤ a + f
-- que, por la monotonía de la suma, se reduce a
--    d ≤ f
-- que es la hipótesis.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  have h1 : a + d ≤ a + f :=
    add_le_add_left h a
  have h2 : exp (a + d) ≤ exp (a + f) :=
    exp_le_exp.mpr h1
  show c + exp (a + d) ≤ c + exp (a + f)
  exact add_le_add_left h2 c

-- 2ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  apply add_le_add_left
  -- ⊢ exp (a + d) ≤ exp (a + f)
  apply exp_le_exp.mpr
  -- ⊢ a + d ≤ a + f
  apply add_le_add_left
  -- ⊢ d ≤ f
  exact h

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    0 < 1
-- ----------------------------------------------------------------------

example : (0 : ℝ) < 1 :=
by norm_num

-- Nota: La táctica norm_num normaliza expresiones numéricas. Ver
-- https://bit.ly/3hoJMgQ

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    a ≤ b
-- entonces
--    log (1 + exp a) ≤ log (1 + exp b)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la monotonía del logaritmo, basta demostrar que
--    0 < 1 + exp(a)                 (1)
--    1 + exp(a) ≤ 1 + exp(b)        (2)
--
-- La (1), por la suma de positivos, se reduce a
--    0 < 1                          (1.1)
--    0 < exp(a)                     (1.2)
-- La (1.1) es una propiedad de los números naturales y la (1.2) de la
-- función exponencial.
--
-- La (2), por la monotonía de la suma, se reduce a
--    exp(a) ≤ exp(b)
-- que, por la monotonía de la exponencial, se reduce a
--    a ≤ b
-- que es la hipótesis.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  have h1 : (0 : ℝ) < 1 :=
    zero_lt_one
  have h2 : 0 < exp a :=
    exp_pos a
  have h3 : 0 < 1 + exp a :=
    add_pos h1 h2
  have h4 : exp a ≤ exp b :=
    exp_le_exp.mpr h
  have h5 : 1 + exp a ≤ 1 + exp b :=
    add_le_add_left h4 1
  show log (1 + exp a) ≤ log (1 + exp b)
  exact log_le_log' h3 h5

-- 2ª demostraciṕn
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  apply log_le_log'
  . -- ⊢ 0 < 1 + exp a
    apply add_pos
    . -- ⊢ 0 < 1
      exact zero_lt_one
    . -- ⊢ 0 < exp a
      exact exp_pos a
  . -- ⊢ 1 + exp a ≤ 1 + exp b
    apply add_le_add_left
    -- ⊢ exp a ≤ exp b
    exact exp_le_exp.mpr h
