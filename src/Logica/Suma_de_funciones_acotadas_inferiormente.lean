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
-- Ejercicio 2. Demostrar que si a es una cota inferior de f y b lo es
-- de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma FnLb_add
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ a + b ≤ (f + g) x
  change a + b ≤ f x + g x
  -- ⊢ a + b ≤ f x + g x
  apply add_le_add
  . -- ⊢ a ≤ f x
    apply hfa
  . -- ⊢ b ≤ g x
    apply hgb

-- 2ª demostración
-- ===============

example
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la suma de dos funciones acotadas
-- inferiormente también lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema:
--    FnLb_add: FnLb f a → FnLb g b → FnLb (f + g) (a + b)
--
-- Puesto que f está acotada inferiormente, tiene una cota inferior. Sea
-- a una de dichas cotas. Análogamentte, puesto que g está acotada
-- inferiormente, tiene una cota inferior. Sea b una de dichas
-- cotas. Por el lema FnLb_add, a+b es una cota inferior de f+g. Por
-- consiguiente, f+g está acotada inferiormente.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (lbf : FnHasLb f)
  (lbg : FnHasLb g)
  : FnHasLb (f + g) :=
by
  rcases lbf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnLb f a
  rcases lbg with ⟨b, hb⟩
  -- b : ℝ
  -- hb : FnLb g b
  have h1 : FnLb (f + g) (a + b) := FnLb_add ha hb
  have h2 : ∃ z, ∀ x, z ≤ (f + g) x :=
    Exists.intro (a + b) h1
  show FnHasLb (f + g)
  exact h2

-- 2ª demostración
-- ===============

example
  (lbf : FnHasLb f)
  (lbg : FnHasLb g)
  : FnHasLb (f + g) :=
by
  rcases lbf with ⟨a, lbfa⟩
  -- a : ℝ
  -- lbfa : FnLb f a
  rcases lbg with ⟨b, lbgb⟩
  -- b : ℝ
  -- lbgb : FnLb g b
  use a + b
  -- ⊢ FnLb (f + g) (a + b)
  apply FnLb_add lbfa lbgb

-- 3ª demostración
-- ===============

example
  (lbf : FnHasLb f)
  (lbg : FnHasLb g)
  : FnHasLb (f + g) :=
by
  rcases lbf with ⟨a, lbfa⟩
  -- a : ℝ
  -- lbfa : FnLb f a
  rcases lbg with ⟨b, lbfb⟩
  -- b : ℝ
  -- lbfb : FnLb g b
  exact ⟨a + b, FnLb_add lbfa lbfb⟩

-- 4ª demostración
-- ===============

example :
  FnHasLb f → FnHasLb g → FnHasLb (f + g) :=
by
  rintro ⟨a, lbfa⟩ ⟨b, lbfb⟩
  -- a : ℝ
  -- lbfa : FnLb f a
  -- b : ℝ
  -- lbfb : FnLb g b
  exact ⟨a + b, FnLb_add lbfa lbfb⟩

-- 5ª demostración
-- ===============

example :
  FnHasLb f → FnHasLb g → FnHasLb (f + g) :=
fun ⟨a, lbfa⟩ ⟨b, lbfb⟩ ↦ ⟨a + b, FnLb_add lbfa lbfb⟩

-- Lemas usados
-- ============

variable (c d : ℝ)
variable (w : ℝ)
variable (p : ℝ → Prop)
#check (Exists.intro w : p w → Exists p)
#check (FnLb_add : FnLb f a → FnLb g b → FnLb (f + g) (a + b))
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
