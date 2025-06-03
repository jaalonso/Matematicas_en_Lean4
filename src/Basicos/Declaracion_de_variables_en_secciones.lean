-- ---------------------------------------------------------------------
-- Ejercicio. Importar la librería básica de los números reales.
-- ---------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Crear una sección.
-- ---------------------------------------------------------------------

section

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que a, b y c son variables sobre los números
-- reales.
-- ---------------------------------------------------------------------

variable (a b c : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de a.
-- ---------------------------------------------------------------------

#check a

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de a + b.
-- ---------------------------------------------------------------------

#check a + b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a + b : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio. Comprobar que a es un número real.
-- ---------------------------------------------------------------------

#check (a : ℝ)

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    mul_comm a b
-- ---------------------------------------------------------------------

#check mul_comm a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a b : a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio. Comprobar que el tipo de
--    mul_comm a b
-- es
--    a * b = b * a
-- ---------------------------------------------------------------------

#check (mul_comm a b : a * b = b * a)

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a b : a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    mul_assoc c a b
-- ---------------------------------------------------------------------

#check mul_assoc c a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_assoc c a b : c * a * b = c * (a * b)

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    mul_comm a
-- ---------------------------------------------------------------------

#check mul_comm a

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a : ∀ (b : ℝ), a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    mul_comm
-- ---------------------------------------------------------------------

#check mul_comm

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G)
--    : a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio 12. Calcular el tipo de
--    @mul_comm
-- ---------------------------------------------------------------------

#check @mul_comm

-- Comentario: Al colocar el cursor sobre check se obtiene
--    @mul_comm : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G),
--    a * b = b * a

end
