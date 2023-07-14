-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de los números naturales.
-- ---------------------------------------------------------------------

import Mathlib.Data.Nat.Basic

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función f que le suma 3 a cada número natural.
-- ---------------------------------------------------------------------

def f (x : ℕ) :=
  x + 3

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de f.
-- ---------------------------------------------------------------------

#check f

-- Comentario: Al colocar el cursor sobre check se obtiene
--    f (x : ℕ) → ℕ

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el valor de f(2).
-- ---------------------------------------------------------------------

#eval f 2

-- Comentario: Al colocar el cursor sobre eval escribe su valor (5).
