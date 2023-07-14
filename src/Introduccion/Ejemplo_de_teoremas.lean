-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de los números naturales.
-- ---------------------------------------------------------------------

import Mathlib.Data.Nat.Basic

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el teorema facil que afirma que 2 + 3 = 5.
-- ---------------------------------------------------------------------

theorem facil : 2 + 3 = 5 := rfl

-- Comentarios:
-- 1. Para activar la ventana de objetivos (*Lean Goal*) se escribe
--    C-c TAB
-- 2. Se desactiva volviendo a escribir C-c TAB
-- 3. La táctica rfl (ver https://bit.ly/3OcOoZL) comprueba que 2+3 y 5
--    son iguales por definición.

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de facil
-- ---------------------------------------------------------------------

#check facil

-- Comentario: Colocando el cursor sobre check se obtiene
--    facil : 2 + 3 = 5

-- ---------------------------------------------------------------------
-- Ejercicio. Enunciar el teorema dificil que afirma que se verifica
-- el último teorema de Fermat, omitiendo la demostración.
-- ---------------------------------------------------------------------

def ultimo_teorema_de_Fermat :=
  ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

theorem dificil : ultimo_teorema_de_Fermat :=
sorry

-- Comentarios:
-- 1. La palabra sorry se usa para omitir la demostración.
-- 2. Se puede verificar la teoría pulsando
--       C-c ! l
--    Se obtiene
--       Line Col Level     Message
--    24   1 info      facil : 2 + 3 = 5 (lsp)
--    37   9 warning   declaration uses 'sorry' (lsp)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Calcular el tipo de dificil.
-- ---------------------------------------------------------------------

#check dificil

-- Comentario: Al colocar el cursor sobre check se obtiene
--    dificil : ultimo_teorema_de_Fermat
