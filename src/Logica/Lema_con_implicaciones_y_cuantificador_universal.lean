-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de los números reales.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Enunciar el lema ej: "para todos los números reales x,
-- y, ε si
--    0 < ε
--    ε ≤ 1
--    |x| < ε
--    |y| < ε
-- entonces
--    |x * y| < ε
-- ----------------------------------------------------------------------

lemma ej :
  ∀ x y ε : ℝ,
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
--    ha : |a| < δ
--    hb : |b| < δ
-- y calcular el tipo de las siguientes expresiones
--    ej a b δ
--    ej a b δ h₀ h₁
--    ej a b δ h₀ h₁ ha hb
-- ----------------------------------------------------------------------

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check (ej a b δ : 0 < δ → δ ≤ 1 → |a| < δ → |b| < δ → |a * b| < δ)
#check (ej a b δ h₀ h₁ : |a| < δ → |b| < δ → |a * b| < δ)
#check (ej a b δ h₀ h₁ ha hb : |a * b| < δ)

end
