-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de exponeciales y logaritmos.
--    2. Abrir la teoría de los reales
--    3. Declarar a, b, c, d y e como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b c d e : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de los siguientes lemas
--    add_lt_add_of_le_of_lt
--    exp_lt_exp
--    le_refl
-- ----------------------------------------------------------------------

#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (le_refl a : a ≤ a)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    a ≤ b
--    c < d
-- entonces
--    a + exp c + e < b + exp d + e
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Aplicando a la hipótesis 3 (c < d) la monotonía de la exponencial, se
-- tiene
--    e^c < e^d
-- que, junto a la hipótesis 1 (a ≤ b) y la monotonía de la suma da
--    a + e^c < b + e^d
-- y, de nuevo por la monotonía de la suma, se tiene
--    a + e^c + e < b + e^d + e

-- 2ª demostración en LN
-- =====================

-- Tenemos que demostrar que
--    (a + e^c) + e < (b + e^d) + e
-- que, por la monotonía de la suma, se reduce a las siguientes dos
-- desigualdades:
--    a + e^c < b + e^d                                           (1)
--    e ≤ e                                                       (2)
--
-- La (1), de nuevo por la monotonía de la suma, se reduce a las
-- siguientes dos:
--    a ≤ b                                                     (1.1)
--    e^c < e^d                                                 (1.2)
--
-- La (1.1) se tiene por la hipótesis 1.
--
-- La (1.2) se tiene aplicando la monotonía de la exponencial a la
-- hipótesis 2.
--
-- La (2) se tiene por la propiedad reflexiva.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + e < b + exp d + e :=
by
  have h3 : exp c < exp d :=
    exp_lt_exp.mpr h2
  have h4 : a + exp c < b + exp d :=
    add_lt_add_of_le_of_lt h1 h3
  show a + exp c + e < b + exp d + e
  exact add_lt_add_right h4 e

-- 2ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + e < b + exp d + e :=
by
  apply add_lt_add_of_lt_of_le
  . -- ⊢ a + exp c < b + exp d
    apply add_lt_add_of_le_of_lt
    . -- ⊢ a ≤ b
      exact h1
    . -- ⊢ exp c < exp d
      apply exp_lt_exp.mpr
      -- ⊢ c < d
      exact h2
  . -- ⊢ e ≤ e
    apply le_refl

-- 3ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + e < b + exp d + e :=
by
  apply add_lt_add_of_lt_of_le
  . -- ⊢ a + exp c < b + exp d
    apply add_lt_add_of_le_of_lt h1
    -- ⊢ exp c < exp d
    exact exp_lt_exp.mpr h2
  . -- ⊢ e ≤ e
    rfl

-- Lemas usados
-- ============

#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (le_refl a : a ≤ a)
