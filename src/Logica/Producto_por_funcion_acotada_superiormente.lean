-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f como variable de funciones de ℝ en ℝ.
-- 3. Declarar a y c como variables sobre ℝ.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_funciones_acotadas

variable {f : ℝ → ℝ}
variable {a c : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota superior de f y c ≥ 0,
-- entonces c * a es una cota superior de c * f.
-- ----------------------------------------------------------------------

-- Demostración en lenguaj natural
-- ===============================

-- Se usará el lema
--    {b ≤ c, 0 ≤ a} ⊢ ab ≤ ac                                      (L1)
--
-- Tenemos que demostrar que
--    (∀ y ∈ ℝ) cf(y) ≤ ca.
-- Sea y ∈ R. Puesto que a es una cota de f, se tiene que
--    f(y) ≤ a
-- que, junto con c ≥ 0, por el lema L1 nos da
--    cf(y) ≤ ca

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (h : c ≥ 0)
  : FnUb (fun x ↦ c * f x) (c * a) :=
by
  intro y
  -- y : ℝ
  -- ⊢ (fun x => c * f x) y ≤ c * a
  have ha : f y ≤ a := hfa y
  calc (fun x => c * f x) y
       = c * f y := by rfl
     _ ≤ c * a   := mul_le_mul_of_nonneg_left ha h

-- 2ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (h : c ≥ 0)
  : FnUb (fun x ↦ c * f x) (c * a) :=
by
  intro y
  -- y : ℝ
  -- ⊢ (fun x => c * f x) y ≤ c * a
  calc (fun x => c * f x) y
       = c * f y := by rfl
     _ ≤ c * a   := mul_le_mul_of_nonneg_left (hfa y) h

-- 3ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (h : c ≥ 0)
  : FnUb (fun x ↦ c * f x) (c * a) :=
by
  intro y
  -- y : ℝ
  -- ⊢ (fun x => c * f x) y ≤ c * a
  exact mul_le_mul_of_nonneg_left (hfa y) h

-- 4ª demostración
-- ===============

lemma FnUb_mul
  (hfa : FnUb f a)
  (h : c ≥ 0)
  : FnUb (fun x ↦ c * f x) (c * a) :=
fun y ↦ mul_le_mul_of_nonneg_left (hfa y) h

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si c ≥ 0 y f está acotada superiormente,
-- entonces c * f también lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema:
--    FnUb_mul : FnUb f a → c ≥ 0 → FnUb (fun x ↦ c * f x) (c * a)
--
-- Puesto que f está acotada superiormente, tiene una cota superior. Sea
-- a una de dichas cotas. Entonces, por el lema FnUb_mul, ca es una cota
-- superior de cf. Por consiguiente, cf está acotada superiormente.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hf : FnHasUb f)
  (hc : c ≥ 0)
  : FnHasUb (fun x ↦ c * f x) :=
by
  rcases hf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnUb f a
  have h1 : FnUb (fun x ↦ c * f x) (c * a) :=
    FnUb_mul ha hc
  have h2 : ∃ z, ∀ x, (fun x ↦ c * f x) x ≤ z :=
    Exists.intro (c * a) h1
  show FnHasUb (fun x ↦ c * f x)
  exact h2

-- 2ª demostración
-- ===============

example
  (hf : FnHasUb f)
  (hc : c ≥ 0)
  : FnHasUb (fun x ↦ c * f x) :=
by
  rcases hf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnUb f a
  use c * a
  -- ⊢ FnUb (fun x => c * f x) (c * a)
  apply FnUb_mul ha hc

-- 3ª demostración
-- ===============

example
  (hf : FnHasUb f)
  (hc : c ≥ 0)
  : FnHasUb (fun x ↦ c * f x) :=
by
  rcases hf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnUb f a
  exact ⟨c * a, FnUb_mul ha hc⟩

-- 4ª demostración
-- ===============

example
  (hc : c ≥ 0)
  : FnHasUb f → FnHasUb (fun x ↦ c * f x) :=
by
  rintro ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnUb f a
  exact ⟨c * a, FnUb_mul ha hc⟩

-- 5ª demostración
-- ===============

example
  (hc : c ≥ 0)
  : FnHasUb f → FnHasUb (fun x ↦ c * f x) :=
fun ⟨a, ha⟩ ↦ ⟨c * a, FnUb_mul ha hc⟩

-- Lemas usados
-- ============

variable (b : ℝ)
#check (FnUb_mul : FnUb f a → c ≥ 0 → FnUb (fun x ↦ c * f x) (c * a))
#check (mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c)
