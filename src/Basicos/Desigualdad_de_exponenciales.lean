-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de exponeciales y logaritmos.
--    2. Abrir la teoría de los reales
--    3. Declarar a y b como variables sobre los reales.
-- ----------------------------------------------------------------------

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo del lema exp_le_exp
-- ----------------------------------------------------------------------

#check @exp_le_exp a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    exp_le_exp : a.exp ≤ b.exp ↔ a ≤ b

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    a ≤ b
-- entonces
--    exp a ≤ exp b
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (h : a ≤ b)
  : exp a ≤ exp b :=
by
  rw [exp_le_exp]
  -- ⊢ a ≤ b
  exact h

-- 2ª demostración
example
  (h : a ≤ b)
  : exp a ≤ exp b :=
by rwa [exp_le_exp]

-- 3ª demostración
example
  (h : a ≤ b)
  : exp a ≤ exp b :=
exp_le_exp.mpr h

-- Nota: Con mpr se indica en modus ponens inverso. Por ejemplo, si
-- h: A ↔ B, entonces h.mpr es B → A y h.mp es A → B
