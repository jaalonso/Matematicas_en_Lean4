-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f y g como variable de funciones de ℝ en ℝ.
-- 3. Declarar a y c como variables sobre ℝ.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_funciones_acotadas

variable {f g : ℝ → ℝ}
variable {a b : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota superior de f y b es una
-- cota superior de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

theorem FnUb_add
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (f + g) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si f y g está acotadas superiormente,
-- entonces f + g también lo está.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubfb⟩
  exact ⟨a + b, FnUb_add ubfa ubfb⟩

-- Su desarrollo es
--
-- f g : ℝ → ℝ
-- ubf : FnHasUb f
-- ubg : FnHasUb g
-- ⊢ FnHasUb (λ (x : ℝ), f x + g x)
--    >> rcases ubf with ⟨a, ubfa⟩
-- f g : ℝ → ℝ
-- ubg : FnHasUb g
-- a : ℝ
-- ubfa : FnUb f a
-- ⊢ FnHasUb (λ (x : ℝ), f x + g x)
--    >> rcases ubg with ⟨b, ubfb⟩
-- f g : ℝ → ℝ
-- a : ℝ
-- ubfa : FnUb f a
-- b : ℝ
-- ubfb : FnUb g b
-- ⊢ FnHasUb (λ (x : ℝ), f x + g x)
--    >> exact ⟨a + b, FnUb_add ubfa ubfb⟩
-- no goals

-- 2ª demostración
-- ===============

example :
  FnHasUb f →
  FnHasUb g →
  FnHasUb (f + g) :=
by
  rintro ⟨a, ubfa⟩ ⟨b, ubfb⟩
  exact ⟨a + b, FnUb_add ubfa ubfb⟩

-- Su desarrollo es
--
-- f g : ℝ → ℝ
-- ⊢ FnHasUb f → FnHasUb g → FnHasUb (λ (x : ℝ), f x + g x)
--    >> rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩
-- f g : ℝ → ℝ
-- a : ℝ
-- ubfa : FnUb f a
-- b : ℝ
-- ubfb : FnUb g b
-- ⊢ FnHasUb (λ (x : ℝ), f x + g x)
--    >> exact ⟨a + b, FnUb_add ubfa ubfb⟩
-- no goals

-- 3ª demostración
-- ===============

example : FnHasUb f → FnHasUb g →
  FnHasUb (f + g) :=
fun ⟨a, ubfa⟩ ⟨b, ubfb⟩ ↦ ⟨a + b, FnUb_add ubfa ubfb⟩
