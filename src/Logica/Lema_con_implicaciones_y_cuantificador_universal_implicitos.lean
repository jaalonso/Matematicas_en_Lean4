-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de los números reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Enunciar, usando variables implícitas, el lema ej: "para
-- todos los números reales x, y, ε si
--    0 < ε
--    ε ≤ 1
--    |x| < ε
--    |y| < ε
-- entonces
--    |x * y| < ε
-- ----------------------------------------------------------------------

lemma ej :
  ∀ {x y ε : ℝ},
  0 < ε →
  ε ≤ 1 →
  |x| < ε →
  |y| < ε →
  |x * y| < ε :=
sorry

-- ---------------------------------------------------------------------
-- Ejercicio 3. Crear una sección con las siguientes declaraciones
--    a b δ : ℝ
--    h₀ : 0 < δ
--    h₁ : δ ≤ 1
--    ha : abs a < δ
--    hb : abs b < δ
-- y calcular el tipo de las siguientes expresiones
--    ej h₀ h₁ ha hb
-- ----------------------------------------------------------------------

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : abs a < δ) (hb : abs b < δ)

#check (ej h₀ h₁ ha hb : |a * b| < δ)

end
