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
-- Ejercicio 2. Demostrar que la suma de una cota inferior de f y una
-- cota inferior de g es una cota inferior de f + g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Por la definición de cota inferior, hay que demostrar que
--    (∀ x ∈ ℝ) [a + b ≤ f(x) + g(x)]                                  (1)
-- Para ello, sea x ∈ R. Puesto que es a es una cota inferior de f, se
-- tiene que
--    a ≤ f(x)                                                         (2)
-- y, puesto que b es una cota inferior de g, se tiene que
--    b ≤ g(x)                                                         (3)
-- De (2) y (3), por add_le_add, se tiene que
--    a + b ≤ f(x) + g(x)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x := by
    intro x
    -- x : ℝ
    -- ⊢ a + b ≤ f x + g x
    have h1a : a ≤ f x := hfa x
    have h1b : b ≤ g x := hgb x
    show a + b ≤ f x + g x
    exact add_le_add h1a h1b
  show FnLb (f + g) (a + b)
  exact h1

-- 2ª demostración
-- ===============

example
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x := by
    intro x
    -- x : ℝ
    -- ⊢ a + b ≤ f x + g x
    show a + b ≤ f x + g x
    exact add_le_add (hfa x) (hgb x)
  show FnLb (f + g) (a + b)
  exact h1

-- 3ª demostración
-- ===============

example
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ a + b ≤ (f + g) x
  dsimp
  -- ⊢ a + b ≤ f x + g x
  apply add_le_add
  . -- ⊢ a ≤ f x
    apply hfa
  . -- ⊢ b ≤ g x
    apply hgb

-- 4ª demostración
-- ===============

example
  (hfa : FnLb f a)
  (hgb : FnLb g b)
  : FnLb (f + g) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que el producto de dos funciones no negativas
-- es no negativa.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b
--
-- Hay que demostrar que
--    (∀ x ∈ ℝ) [0 ≤ f(x) * g(x)]                                  (1)
-- Para ello, sea x ∈ R. Puesto que f es no negatica, se tiene que
--    0 ≤ f(x)                                                         (2)
-- y, puesto que g es no negativa, se tiene que
--    0 ≤ g(x)                                                         (3)
-- De (2) y (3), por mul_nonneg, se tiene que
--    0 ≤ f(x) * g(x)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (nnf : FnLb f 0)
  (nng : FnLb g 0)
  : FnLb (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x := by
    intro x
    -- x : ℝ
    -- ⊢ 0 ≤ f x * g x
    have h2: 0 ≤ f x := nnf x
    have h3: 0 ≤ g x := nng x
    show 0 ≤ f x * g x
    exact mul_nonneg h2 h3
  show FnLb (f * g) 0
  exact h1

-- 2ª demostración
-- ===============

example
  (nnf : FnLb f 0)
  (nng : FnLb g 0)
  : FnLb (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x := by
    intro x
    -- x : ℝ
    -- ⊢ 0 ≤ f x * g x
    show 0 ≤ f x * g x
    exact mul_nonneg (nnf x) (nng x)
  show FnLb (f * g) 0
  exact h1

-- 3ª demostración
-- ===============

example
  (nnf : FnLb f 0)
  (nng : FnLb g 0)
  : FnLb (f * g) 0 :=
by
  intro x
  -- x : ℝ
  -- ⊢ 0 ≤ (f * g) x
  dsimp
  -- ⊢ 0 ≤ f x * g x
  apply mul_nonneg
  . -- ⊢ 0 ≤ f x
    apply nnf
  . -- ⊢ 0 ≤ g x
    apply nng

-- 4ª demostración
-- ===============

example
  (nnf : FnLb f 0)
  (nng : FnLb g 0)
  : FnLb (f * g) 0 :=
λ x ↦ mul_nonneg (nnf x) (nng x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si a es una cota superior de f, b es una
-- cota superior de g, a es no negativa y g es no negativa, entonces
-- a * b es una cota superior de f * g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d
--
-- Hay que demostrar que
--    (∀ x ∈ ℝ) [0 ≤ f x * g x ≤ a * b]                                (1)
-- Para ello, sea x ∈ R. Puesto que a es una cota superior de f, se tiene que
--    f(x) ≤ a                                                         (2)
-- puesto que b es una cota superior de g, se tiene que
--    g(x) ≤ b                                                         (3)
-- puesto que g es no negativa, se tiene que
--    0 ≤ g(x)                                                         (4)
-- y, puesto que a es no negativa, se tiene que
--    0 ≤ a                                                            (5)
-- De (2), (3), (4) y (5), por mul_le_mul, se tiene que
--    f x * g x ≤ a * b
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  (nng : FnLb g 0)
  (nna : 0 ≤ a)
  : FnUb (f * g) (a * b) :=
by
  have h1 : ∀ x, f x * g x ≤ a * b := by
    intro x
    -- x : ℝ
    -- ⊢ f x * g x ≤ a * b
    have h2 : f x ≤ a := hfa x
    have h3 : g x ≤ b := hgb x
    have h4 : 0 ≤ g x := nng x
    show f x * g x ≤ a * b
    exact mul_le_mul h2 h3 h4 nna
  show FnUb (f * g) (a * b)
  exact h1

-- 2ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  (nng : FnLb g 0)
  (nna : 0 ≤ a)
  : FnUb (f * g) (a * b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x ≤ a * b
  dsimp
  -- ⊢ f x * g x ≤ a * b
  apply mul_le_mul
  . -- ⊢ f x ≤ a
    apply hfa
  . -- ⊢ g x ≤ b
    apply hgb
  . -- ⊢ 0 ≤ g x
    apply nng
  . -- ⊢ 0 ≤ a
    apply nna

-- 3ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  (nng : FnLb g 0)
  (nna : 0 ≤ a)
  : FnUb (f * g) (a * b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x ≤ a * b
  have h1:= hfa x
  have h2:= hgb x
  have h3:= nng x
  exact mul_le_mul h1 h2 h3 nna

-- 4ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  (nng : FnLb g 0)
  (nna : 0 ≤ a)
  : FnUb (f * g) (a * b) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x ≤ a * b
  specialize hfa x
  -- hfa : f x ≤ a
  specialize hgb x
  -- hgb : g x ≤ b
  specialize nng x
  -- nng : 0 ≤ g x
  exact mul_le_mul hfa hgb nng nna

-- 5ª demostración
-- ===============

example
  (hfa : FnUb f a)
  (hgb : FnUb g b)
  (nng : FnLb g 0)
  (nna : 0 ≤ a)
  : FnUb (f * g) (a * b) :=
λ x ↦ mul_le_mul (hfa x) (hgb x) (nng x) nna

-- Lemas usados
-- ============

variable (c d : ℝ)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
