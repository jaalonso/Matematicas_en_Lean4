-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- + Importar la teoría Definicion_de_funciones_acotadas
-- + Declarar f como una variable de ℝ en ℝ.
-- ----------------------------------------------------------------------

import src.Logica.Definicion_de_funciones_acotadas
variable (f : ℝ → ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ¬ ∀ a, ∃ x, f x > a
-- entonces f está acotada superiormente.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que f es acotada superiormente; es decir, que
--    (∃a)(∀x)[f(x) ≤ a]
-- que es exactamente la fórmula obtenida interiorizando la negación en
-- la hipótesis.

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : FnHasUb f :=
by
  unfold FnHasUb
  -- ⊢ ∃ a, FnUb f a
  unfold FnUb
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 2ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : FnHasUb f :=
by
  unfold FnHasUb FnUb
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 3ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : FnHasUb f :=
by
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- Comentario. La táctica (push_neg at h) interioriza las negaciones de
-- la hipótesis h.

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si f no tiene cota superior, entonces para
-- cada a existe un x tal que f(x) > a.
-- ----------------------------------------------------------------------

example
  (h : ¬FnHasUb f)
  : ∀ a, ∃ x, f x > a :=
by
  simp only [FnHasUb, FnUb] at h
  -- h : ¬∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- ⊢ ∀ (a : ℝ), ∃ x, f x > a
  exact h

-- Comentario: La táctica (simp only [h₁, ..., hₙ] at h) simplifica la
-- hipótesis h usando sólo los lemas h₁, ..., hₙ.
