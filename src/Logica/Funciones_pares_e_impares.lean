-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar f y g como variables sobre funciones de ℝ en ℝ.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic -- 1

namespace oculto

variable (f g : ℝ → ℝ)         -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    even (ℝ → ℝ) → Prop
-- tal que (even f) afirma que f es par.
-- ----------------------------------------------------------------------

def even (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    odd (ℝ → ℝ) → Prop
-- tal que (odd f) afirma que f es impar.
-- ----------------------------------------------------------------------

def odd  (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = - f (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que la suma de dos funciones pares es par.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f y g son funciones pares. Tenemos que demostrar que
-- f+g es par; es decir, que
--    (∀ x ∈ ℝ) (f + g)(x) = (f + g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f + g)(x) = f(x) + g(x)
--               = f(-x) + g(x)    [porque f es par]
--               = f(-x) + g(-x)   [porque g es par]
--               = (f + g)(-x)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (ef : even f)
  (eg : even g)
  : even (f + g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f + g) x = (f + g) (-x)
  have h1 : f x = f (-x) := ef x
  have h2 : g x = g (-x) := eg x
  calc (f + g) x
       = f x + g x       := rfl
     _ = f (-x) + g x    := congrArg (. + g x) h1
     _ = f (-x) + g (-x) := congrArg (f (-x) + .) h2
     _ = (f + g) (-x)    := rfl

-- 2ª demostración
-- ===============

example
  (ef : even f)
  (eg : even g)
  : even (f + g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f + g) x = (f + g) (-x)
  calc (f + g) x
       = f x + g x       := rfl
     _ = f (-x) + g x    := congrArg (. + g x) (ef x)
     _ = f (-x) + g (-x) := congrArg (f (-x) + .) (eg x)
     _ = (f + g) (-x)    := rfl

-- 3ª demostración
-- ===============

example
  (ef : even f)
  (eg : even g)
  : even (f + g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f + g) x = (f + g) (-x)
  calc (f + g) x
       = f x + g x       := rfl
     _ = f (-x) + g (-x) := by rw [ef, eg]
     _ = (f + g) (-x)    := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que el producto de dos funciones impares es
-- par.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f y g son funciones impares. Tenemos que demostrar que
-- f·g es par; es decir, que
--    (∀ x ∈ ℝ) (f·g)(x) = (f·g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f·g) x = f(x)g(x)
--            = (-f(-x))g(x)      [porque f es impar]
--            = (-f(-x)(-g(-x))   [porque g es par]
--            = f(-x)g(-x))
--            = (f·g)(-x)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (of : odd f)
  (og : odd g)
  : even (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = (f * g) (-x)
  have h1 : f x = -f (-x) := of x
  have h2 : g x = -g (-x) := og x
  calc (f * g) x
       = f x * g x             := rfl
     _ = (-f (-x)) * g x       := congrArg (. * g x) h1
     _ = (-f (-x)) * (-g (-x)) := congrArg ((-f (-x)) * .) h2
     _ = f (-x) * g (-x)       := neg_mul_neg (f (-x)) (g (-x))
     _ = (f * g) (-x)          := rfl

-- 2ª demostración
-- ===============

example
  (of : odd f)
  (og : odd g)
  : even (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = (f * g) (-x)
  calc (f * g) x
       = f x * g x             := rfl
     _ = (-f (-x)) * g x       := congrArg (. * g x) (of x)
     _ = (-f (-x)) * (-g (-x)) := congrArg ((-f (-x)) * .) (og x)
     _ = f (-x) * g (-x)       := neg_mul_neg (f (-x)) (g (-x))
     _ = (f * g) (-x)          := rfl

-- 3ª demostración
-- ===============

example
  (of : odd f)
  (og : odd g)
  : even (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = (f * g) (-x)
  calc (f * g) x
       = f x * g x         := rfl
     _ = -f (-x) * -g (-x) := by rw [of, og]
     _ = f (-x) * g (-x)   := by rw [neg_mul_neg]
     _ = (f * g) (-x)      := rfl

-- 4ª demostración
-- ===============

example
  (of : odd f)
  (og : odd g)
  : even (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = (f * g) (-x)
  calc (f * g) x
       = f x * g x       := rfl
     _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]
     _ = (f * g) (-x)    := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que el producto de una función par por una
-- impar es impar.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f es una función par y g lo es impar. Tenemos que
-- demostrar que f·g es impar; es decir, que
--    (∀ x ∈ ℝ) (f·g)(x) = -(f·g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f·g) x = f(x)g(x)
--            = f(-x)g(x)       [porque f es par]
--            = f(-x)(-g(-x))   [porque g es impar]
--            = -f(-x)g(-x))
--            = -(f·g)(-x)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (ef : even f)
  (og : odd g)
  : odd (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = -(f * g) (-x)
  have h1 : f x = f (-x) := ef x
  have h2 : g x = -g (-x) := og x
  calc (f * g) x
       = f x * g x            := rfl
     _ = (f (-x)) * g x       := congrArg (. * g x) h1
     _ = (f (-x)) * (-g (-x)) := congrArg (f (-x) * .) h2
     _ = -(f (-x) * g (-x))   := mul_neg (f (-x)) (g (-x))
     _ = -(f * g) (-x)        := rfl

-- 2ª demostración
-- ===============

example
  (ef : even f)
  (og : odd g)
  : odd (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = -(f * g) (-x)
  calc (f * g) x
       = f x * g x          := rfl
    _  = f (-x) * -g (-x)   := by rw [ef, og]
    _  = -(f (-x) * g (-x)) := by rw [mul_neg]
    _  = -(f * g) (-x)      := rfl

-- 3ª demostración
-- ===============

example
  (ef : even f)
  (og : odd g)
  : odd (f * g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f * g) x = -(f * g) (-x)
  calc (f * g) x
       = f x * g x          := rfl
     _ = -(f (-x) * g (-x)) := by rw [ef, og, mul_neg]
     _ = -((f * g) (-x))    := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que si f es par y g es impar, entonces f ∘ g
-- es par.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f es una función par y g lo es impar. Tenemos que
-- demostrar que (f ∘ g) es par; es decir, que
--    (∀ x ∈ ℝ) (f ∘ g)(x) = (f ∘ g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f ∘ g)(x) = f(g(x))
--               = f(-g(-x))    [porque g es impar]
--               = f(g(-x))     [porque f es par]
--               = (f ∘ g)(-x)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (ef : even f)
  (og : odd g)
  : even (f ∘ g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f ∘ g) x = (f ∘ g) (-x)
  calc (f ∘ g) x
       = f (g x)      := rfl
    _  = f (-g (-x))  := congrArg f (og x)
    _  = f (g (-x))   := (ef (g (-x))).symm
    _  = (f ∘ g) (-x) := rfl

-- 2ª demostración
-- ===============

example
  (ef : even f)
  (og : odd g)
  : even (f ∘ g) :=
by
  intro x
  -- x : ℝ
  -- ⊢ (f ∘ g) x = (f ∘ g) (-x)
  calc (f ∘ g) x
       = f (g x)      := rfl
     _ = f (-g (-x))  := by rw [og]
     _ = f (g (-x))   := by rw [← ef]
     _ = (f ∘ g) (-x) := rfl

-- Lemas usados
-- ============

variable (a b : ℝ)
#check (congrArg f : a = b → f a = f b)
#check (mul_neg a b : a * -b = -(a * b))
#check (neg_mul_neg a b : -a * -b = a * b)

end oculto
