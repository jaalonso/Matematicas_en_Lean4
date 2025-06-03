-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el límite del producto de dos sucesiones
-- convergentes es el producto de sus límites.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_convergencia
import src.Logica.Convergencia_de_la_funcion_constante
import src.Logica.Convergencia_de_la_suma
import src.Logica.Convergencia_del_producto_por_una_constante
import src.Logica.Acotacion_de_convergentes
import src.Logica.Producto_por_sucesion_convergente_a_cero
import Mathlib.Tactic

variable {s t : ℕ → ℝ}
variable {a b : ℝ}

theorem limite_mul
  (cs : limite s a)
  (ct : limite t b)
  : limite (fun n ↦ s n * t n) (a * b) :=
by
  have h₁ : limite (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    -- ⊢ limite (fun n => t n + -b) 0
    convert limite_suma ct (limite_constante (-b))
    -- ⊢ 0 = b + -b
    ring
  convert (limite_suma h₁ (limite_por_constante b cs)) using 1
  . -- ⊢ (fun n => s n * t n) = (fun n => s n * (t n + -b)) + fun n => b * s n
    ext n
    -- ⊢ s n * t n = ((fun n => s n * (t n + -b)) + fun n => b * s n) n
    simp
    -- ⊢ s n * t n = s n * (t n + -b) + b * s n
    ring
  . -- ⊢ a * b = 0 + b * a
    ring
