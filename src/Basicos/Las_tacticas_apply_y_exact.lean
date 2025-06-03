-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de los números reales
--    2. Declarar x, y y z como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

variable (x y z : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x ≤ y
--    y ≤ z
-- entonces
--    x ≤ z
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
by
  apply le_trans
  . -- ⊢ x ≤ ?b
    apply h1
  . -- ⊢ y ≤ z
    apply h2

-- 2ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
by
  apply le_trans h1
  -- ⊢ y ≤ z
  apply h2

-- 3ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
by exact le_trans h1 h2

-- 4ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
le_trans h1 h2

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    x ≤ x
-- ----------------------------------------------------------------------

-- 1ª demostración
example : x ≤ x :=
by apply le_refl

-- 2ª demostración
example : x ≤ x :=
by exact le_refl x

-- 3ª demostración
example (x : ℝ) : x ≤ x :=
le_refl x

-- Lemas usados
-- ============

#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
