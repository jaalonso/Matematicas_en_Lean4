-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f y g como variables de funciones de ℝ en ℝ.
-- 3. Declarar a y b como variables sobre ℝ.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_funciones_acotadas
variable {f g : ℝ → ℝ}
variable {a b : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota superior de f y b lo es
-- de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema:
--    L1 : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Tenemos que demostrar que
--    (∀ x ∈ ℝ) [(f + g)(x) ≤ a + b]
-- Sea x ∈ ℝ. Puesto que a es una cota superior de f, se tiene que
--    f(x) ≤ a                                                       (1)
-- y, puesto que b es una cota superior de g, se tiene que
--    g(x) ≤ b                                                       (2)
-- Por tanto,
--    (f + g)(x) = f(x) + g(x)
--               ≤ a + b         [por L1, (1) y (2)]
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (f + g) (a + b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f + g) x ≤ a + b
  have h1 : f x ≤ a := hfa x
  have h2 : g x ≤ b := hgb x
  calc (f + g) x = f x + g x := by rfl
               _ ≤ a + b     := add_le_add h1 h2

-- 2ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (f + g) (a + b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f + g) x ≤ a + b
  change f x + g x ≤ a + b
  -- ⊢ f x + g x ≤ a + b
  apply add_le_add
  . -- ⊢ f x ≤ a
    apply hfa
  . -- ⊢ g x ≤ b
    apply hgb

-- 3ª demostración
-- ===============

theorem FnUb_add
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (f + g) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la suma de dos funciones acotadas
-- superiormente también lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema:
--    L1: FnUb f a → FnUb g b → FnUb (f + g) (a + b)
--
-- Puesto que f está acotada superiormente, tiene una cota superior. Sea
-- a una de dichas cotas. Análogamentte, puesto que g está acotada
-- superiormente, tiene una cota superior. Sea b una de dichas
-- cotas. Por el L1, a+b es una cota superior de f+g. or consiguiente,
-- f+g está acotada superiormente.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
by
  rcases ubf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnUb f a
  rcases ubg with ⟨b, hb⟩
  -- b : ℝ
  -- hb : FnUb g b
  have h : ∀ x, (f + g) x ≤ a + b :=
    FnUb_add ha hb
  have h4 : ∃ z, ∀ x, (f + g) x ≤ z :=
    Exists.intro (a + b) h
  show FnHasUb (f + g)
  exact h4

-- 2ª demostración
-- ===============

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
by
  rcases ubf with ⟨a, ubfa⟩
  -- a : ℝ
  -- ubfa : FnUb f a
  rcases ubg with ⟨b, ubfb⟩
  -- b : ℝ
  -- ubfb : FnUb g b
  use a + b
  -- ⊢ FnUb (f + g) (a + b)
  apply FnUb_add ubfa ubfb

-- 4ª demostración
-- ===============

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
by
  rcases ubf with ⟨a, ubfa⟩
  -- a : ℝ
  -- ubfa : FnUb f a
  rcases ubg with ⟨b, ubfb⟩
  -- b : ℝ
  -- ubfb : FnUb g b
  exact ⟨a + b, FnUb_add ubfa ubfb⟩

-- 5ª demostración
-- ===============

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
by
  obtain ⟨a, ubfa⟩ := ubf
  -- a : ℝ
  -- ubfa : FnUb f a
  obtain ⟨b, ubfb⟩ := ubg
  -- b : ℝ
  -- ubfb : FnUb g b
  exact ⟨a + b, FnUb_add ubfa ubfb⟩

-- 6ª demostración
-- ===============

example :
  FnHasUb f → FnHasUb g → FnHasUb (f + g) :=
by
  rintro ⟨a, ubfa⟩ ⟨b, ubfb⟩
  -- a : ℝ
  -- ubfa : FnUb f a
  -- b : ℝ
  -- ubfb : FnUb g b
  -- ⊢ FnHasUb (f + g)
  exact ⟨a + b, FnUb_add ubfa ubfb⟩

-- 7ª demostración
-- ===============

example :
  FnHasUb f → FnHasUb g → FnHasUb (f + g) :=
fun ⟨a, ubfa⟩ ⟨b, ubfb⟩ ↦ ⟨a + b, FnUb_add ubfa ubfb⟩

example
  (ubf : FnHasUb f)
  (ubg : FnHasUb g)
  : FnHasUb (f + g) :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      -- a : ℝ
      -- ubfa : FnUb f a
      -- b : ℝ
      -- ubgb : FnUb g b
      ⟨a + b, FnUb_add ubfa ubgb⟩

-- Lemas usados
-- ============

variable (c d : ℝ)
variable (w : ℝ)
variable (p : ℝ → Prop)
#check (Exists.intro w : p w → Exists p)
#check (FnUb_add : FnUb f a → FnUb g b → FnUb (f + g) (a + b))
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
