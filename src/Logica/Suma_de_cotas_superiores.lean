-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números reales.
-- 2. Definir cota superior de una función.
-- 3. Definir cota inferior de una función.
-- 4. Declarar f y g como variables de funciones de ℝ en ℝ.
-- 5. Declarar a y b como variables sobre ℝ.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic                                      -- 1

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a                 -- 2
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x                 -- 3

variable (f g : ℝ → ℝ)                                              -- 4
variable (a b : ℝ)                                                  -- 5

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que la suma de una cota superior de f y una
-- cota superior de g es una cota superior de f + g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Por la definición de cota superior, hay que demostrar que
--    (∀ x ∈ ℝ) [f(x) + g(x) ≤ a + b]                                  (1)
-- Para ello, sea x ∈ R. Puesto que es a es una cota superior de f, se
-- tiene que
--    f(x) ≤ a                                                         (2)
-- y, puesto que b es una cota superior de g, se tiene que
--    g(x) ≤ b                                                         (3)
-- De (2) y (3), por add_le_add, se tiene que
--    f(x) + g(x) ≤ a + b
-- que es lo que había que demostrar.

-- 1ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
by
  have h1 : ∀ x, f x + g x ≤ a + b := by
    intro x
    -- x : ℝ
    -- ⊢ f x + g x ≤ a + b
    have h2 : f x ≤ a := hfa x
    have h3 : g x ≤ b := hgb x
    show f x + g x ≤ a + b
    exact add_le_add h2 h3
  show FnUb (fun x ↦ f x + g x) (a + b)
  exact h1

-- 2ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
by
  have h1 : ∀ x, f x + g x ≤ a + b := by
    intro x
    -- x : ℝ
    -- ⊢ f x + g x ≤ a + b
    show f x + g x ≤ a + b
    exact add_le_add (hfa x) (hgb x)
  show FnUb (fun x ↦ f x + g x) (a + b)
  exact h1

-- 3ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (fun x => f x + g x) x ≤ a + b
  dsimp
  -- ⊢ f x + g x ≤ a + b
  apply add_le_add
  . -- ⊢ f x ≤ a
    apply hfa
  . -- ⊢ g x ≤ b
    apply hgb

-- Notas.
-- + Nota 1. Con "intro x" se despliega la definición de FnUb y se introduce
--   la variable x en el contexto.
-- + Nota 2. Con "dsimp" se simplifica la definición del lambda. El mismo
--   efecto se consigue con "change f x + g x ≤ a + b"

-- 4ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

variable (c d : ℝ)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
