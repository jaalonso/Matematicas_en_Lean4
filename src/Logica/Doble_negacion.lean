-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- + Importar la librería de tácticas.
-- + Declarar P como una variable proposicional.
-- ----------------------------------------------------------------------

import Mathlib.Tactic
variable (P : Prop)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--     ¬¬P
-- entonces
--    P
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por reducción al absurdo. Supongamos ¬P. Entonces, tenemos una
-- contradicción con la hipótesis (¬¬P).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by
  by_contra h1
  -- h1 : ¬P
  -- ⊢ False
  exact (h h1)

-- 2ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by_contra (fun h1 ↦ h h1)

-- 3ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
-- not_not.mp h
of_not_not h

-- 4ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by tauto

-- Comentario: La táctica tauto demuestra las tautologís
-- proposionales.

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    P
-- entonces
--    ¬¬P
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos ¬P. Entonces, tenemos una contradicción con la hipótesis
-- (P).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
by
  intro h1
  -- h1 : ¬P
  -- ⊢ False
  exact (h1 h)

-- 2ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
fun h1 ↦ h1 h

-- 3ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
not_not_intro h

-- 4ª demostración
-- ===============

example
  (h : P)
  : ¬ ¬ P :=
by tauto

-- Lemas usados
-- ============

#check (not_not_intro : P → ¬¬P)
#check (of_not_not : ¬¬P → P)
