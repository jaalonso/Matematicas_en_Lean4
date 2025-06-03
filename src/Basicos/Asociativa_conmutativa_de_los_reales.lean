-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los números reales tienen la siguiente
-- propiedad
--    (a * b) * c = b * (a * c)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    (ab)c = (ba)c   [por la conmutativa]
--          = b(ac)   [por la asociativa]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

-- 1ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
calc
  (a * b) * c = (b * a) * c := by rw [mul_comm a b]
            _ = b * (a * c) := by rw [mul_assoc b a c]

-- Comentarios:
-- + El entorno calc permite escribir demostraciones ecuacionales.
-- + La táctica (rw [es]) reescribe una expresión usando las ecuaciones es.
-- + Al colocar el cursor sobre el nombre de un lema se ve su enunciado.
-- + Para completar el nombre de un lema basta escribir parte de su
--   nombre y completar con S-SPC (es decir, simultáneamente las teclas
--   de mayúscula y la de espacio).

-- 2ª demostración
-- ===============

example : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  -- ⊢ b * a * c = b * (a * c)
  rw [mul_assoc b a c]

-- 3ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by ring

-- Comentario: La táctica ring demuestra ecuaciones aplicando las
-- propiedades de anillos.

-- Lemas usados
-- ============

#check (mul_comm a b : a * b = b * a)
#check (mul_assoc a b c : (a * b) * c = a * (b * c))
