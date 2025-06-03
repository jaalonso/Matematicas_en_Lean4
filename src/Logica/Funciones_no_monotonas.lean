-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar f como una variable sobre las funciones de ℝ en ℝ.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {f : ℝ → ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que f es no monótona syss existen x e y tales
-- que x ≤ y y f(x) > f(y).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de equivalencias:
--    f es no monótona ↔ ¬(∀ x y)[x ≤ y → f(x) ≤ f(y)]
--                     ↔ (∃ x y)[x ≤ y ∧ f(x) > f(y)]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f y < f x  := by simp_all only [not_forall, not_le, exists_prop]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by rfl

-- 2ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by aesop

-- 3ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  push_neg
  -- ⊢ (Exists fun ⦃a⦄ => Exists fun ⦃b⦄ => a ≤ b ∧ f b < f a) ↔ ∃ x y, x ≤ y ∧ f x > f y
  rfl

-- 4ª demostración
-- ===============

lemma not_Monotone_iff :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  aesop

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la función opuesta no es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usando el lema del ejercicio anterior que afirma que una función f no
-- es monótona syss existen x e y tales que x ≤ y y f(x) > f(y), basta
-- demostrar que
--    (∃ x y)[x ≤ y ∧ -x > -y]
-- Basta elegir 2 y 3 ya que
--    2 ≤ 3 ∧ -2 > -3

-- Demostración con Lean4
-- ======================

example : ¬Monotone fun x : ℝ ↦ -x :=
by
  apply not_Monotone_iff.mpr
  -- ⊢ ∃ x y, x ≤ y ∧ -x > -y
  use 2, 3
  -- ⊢ 2 ≤ 3 ∧ -2 > -3
  norm_num

-- Lemas usados
-- ============

variable (a b : ℝ)
variable (P : ℝ → Prop)
variable (p q : Prop)
#check (exists_prop : (∃ (_ : p), q) ↔ p ∧ q)
#check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
#check (not_le : ¬a ≤ b ↔ b < a)
