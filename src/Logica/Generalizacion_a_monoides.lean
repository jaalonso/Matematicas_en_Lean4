-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de monoides.
-- 2. Declarar α como un tipo.
-- 3. Declarar R como un monoide ordenado cancelativo.
-- 4. Declarar a, b, c y d como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

variable {α : Type*}
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

variable (a b c d : R)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de
--     @add_le_add R _ a b c d
-- ----------------------------------------------------------------------

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    FnUb (α → R) → R → Prop
-- tal que (FnUb f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que que la suma de una cota superior de f y
-- otra de g es una cota superior de f + g.
-- ----------------------------------------------------------------------

theorem fnUb_add
  {f g : α → R}
  {a b : R}
  (hfa : FnUb' f a)
  (hgb : FnUb' g b)
  : FnUb' (fun x ↦ f x + g x) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
