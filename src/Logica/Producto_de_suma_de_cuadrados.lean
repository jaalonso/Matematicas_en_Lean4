-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar α como un tipo sobre los anillos conmutativos.
-- 3. Declarar x e y como variables sobre α.
-- ----------------------------------------------------------------------

import Mathlib.Tactic
variable {α : Type _} [CommRing α]
variable {x y : α}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    sum_of_squares : α → Prop
-- tal que (sum_of_squares x) afirma que x se puede escribir como la suma
-- de dos cuadrados.
-- ----------------------------------------------------------------------

def sum_of_squares (x : α) :=
  ∃ a b, x = a^2 + b^2

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si x e y se pueden escribir como la suma
-- de dos cuadrados, entonces también se puede escribir x * y.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que x e y se pueden escribir como la suma de dos cuadrados,
-- existen a, b , c y d tales que
--    x = a² + b²
--    y = c² + d²
-- Entonces,
--    xy = (ac - bd)² + (ad + bc)²
-- En efecto,
--    xy = (a² + b²)(c² + d²)
--       = a²c² + b²d² + a²d² + b²c²
--       = a²c² - 2acbd + b²d² + a²d² + 2adbc + b²c²
--       = (ac - bd)² + (ad + bc)²
-- Por tanto, xy es la suma de dos cuadrados.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (hx : sum_of_squares x)
  (hy : sum_of_squares y)
  : sum_of_squares (x * y) :=
by
  rcases hx with ⟨a, b, xeq⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2 :=
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2) :=
                by rw [xeq, yeq]
       _ = a^2*c^2 + b^2*d^2 + a^2*d^2 + b^2*c^2 :=
                by ring
       _ = a^2*c^2 - 2*a*c*b*d + b^2*d^2 + a^2*d^2 + 2*a*d*b*c + b^2*c^2 :=
                by ring
       _ = (a*c - b*d)^2 + (a*d + b*c)^2 :=
                by ring
  have h2 : ∃ f, x * y = (a*c - b*d)^2 + f^2 :=
    Exists.intro (a*d + b*c) h1
  have h3 : ∃ e f, x * y = e^2 + f^2 :=
    Exists.intro (a*c - b*d) h2
  show sum_of_squares (x * y)
  exact h3

-- 2ª demostración
-- ===============

example
  (hx : sum_of_squares x)
  (hy : sum_of_squares y)
  : sum_of_squares (x * y) :=
by
  rcases hx with ⟨a, b, xeq⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2 :=
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     := by rw [xeq, yeq]
       _ = (a*c - b*d)^2 + (a*d + b*c)^2 := by ring
  have h2 : ∃ e f, x * y = e^2 + f^2 :=
    by tauto
  show sum_of_squares (x * y)
  exact h2

-- 3ª demostración
-- ===============

example
  (hx : sum_of_squares x)
  (hy : sum_of_squares y)
  : sum_of_squares (x * y) :=
by
  rcases hx with ⟨a, b, xeq⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  rw [xeq, yeq]
  -- ⊢ sum_of_squares ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
  use a*c - b*d, a*d + b*c
  -- ⊢ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
  --   = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2
  ring

-- 4ª demostración
-- ===============

example
  (hx : sum_of_squares x)
  (hy : sum_of_squares y)
  : sum_of_squares (x * y) :=
by
  rcases hx with ⟨a, b, rfl⟩
  -- a b : α
  -- ⊢ sum_of_squares ((a ^ 2 + b ^ 2) * y)
  rcases hy with ⟨c, d, rfl⟩
  -- c d : α
  -- ⊢ sum_of_squares ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
  use a*c - b*d, a*d + b*c
  -- ⊢ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
  --   = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2
  ring
