-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Declarar α como un tipo sobre órdenes parciales.
-- 2. Declarar s como una variable sobre conjuntos de elementos de tipo α
-- 3. Declarar a y b como variables sobre α.
-- ----------------------------------------------------------------------

import Mathlib.Tactic

variable {α : Type _} [PartialOrder α] -- 1
variable (s : Set α)                   -- 2
variable (a b : α)                     -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    SetUb : set α → α → Prop
-- tal que (SetUb s a) afirma que a es una cota superior de s.
-- ----------------------------------------------------------------------

def SetUb (s : Set α) (a : α) :=
  ∀ {x}, x ∈ s → x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si a es una cota superior de s y a ≤ b,
-- entonces b es una cota superior de s.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x) [x ∈ s → x ≤ b]
-- Sea x tal que x ∈ s. Entonces,
--    x ≤ a   [porque a es una cota superior de s]
--      ≤ b
-- Por tanto, x ≤ b.

-- 1ª demostración
-- ===============

example
  (h1 : SetUb s a)
  (h2 : a ≤ b)
  : SetUb s b :=
by
  intro x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ≤ b
  have h3 : x ≤ a := h1 xs
  show x ≤ b
  exact le_trans h3 h2

-- 2ª demostración
-- ===============

example
  (h1 : SetUb s a)
  (h2 : a ≤ b)
  : SetUb s b :=
by
  intro x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ≤ b
  calc x ≤ a := h1 xs
       _ ≤ b := h2

-- Lemas usados
-- ============

variable (c : α)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
