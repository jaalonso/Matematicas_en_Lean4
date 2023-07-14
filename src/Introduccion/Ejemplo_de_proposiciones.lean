-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de los números naturales.
-- ---------------------------------------------------------------------

import Mathlib.Data.Nat.Basic

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la proposión ultimo_teorema_de_Fermat que
-- expresa el último teorema de Fermat.
-- ---------------------------------------------------------------------

def ultimo_teorema_de_Fermat :=
  ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de ultimo_teorema_de_Fermat
-- ---------------------------------------------------------------------

#check ultimo_teorema_de_Fermat

-- Comentario: Al colocar el cursor sobre check se obtiene
--    ultimo_teorema_de_Fermat : Prop
