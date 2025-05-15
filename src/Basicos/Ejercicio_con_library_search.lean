-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Demostrar que si
--    a ≤ b
-- entonces
--    c - exp b ≤ c - exp a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Aplicando la monotonía de la exponencial a la hipótesis, se tiene
--    e^a ≤ e^b
-- y, restando de c, se invierte la desigualdad
--    c - e^b ≤ c - e^a

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b c : ℝ)

-- 1ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   have h1 : exp a ≤ exp b :=
     exp_le_exp.mpr h
   show c - exp b ≤ c - exp a
   exact sub_le_sub_left h1 c

-- 2ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   apply sub_le_sub_left _ c
   apply exp_le_exp.mpr h

-- 3ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sub_le_sub_left (exp_le_exp.mpr h) c

-- 4ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- Los lemas usados son:
variable (d : ℝ)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (le_refl : ∀ (a : ℝ), a ≤ a)
#check (neg_le_neg : a ≤ b → -b ≤ -a)
variable (h : a ≤ b)
#check (sub_le_sub_left h c : c - b ≤ c - a)
