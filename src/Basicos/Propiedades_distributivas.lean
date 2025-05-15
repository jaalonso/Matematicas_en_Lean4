-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de retículos.
--    2. Declarar α como un tipo sobre retículos
--    3. Declarar a, b y c como variabkes sobre α
-- ----------------------------------------------------------------------

import Mathlib.Order.Lattice       -- 1
variable {α : Type _} [Lattice α]  -- 2
variable (a b c : α)               -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
-- entonces
--    (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por la siguiente cadena de igualdades
--    (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)          [por conmutatividad de ⊓]
--                = (c ⊓ a) ⊔ (c ⊓ b)    [por la hipótesis]
--                = (a ⊓ c) ⊔ (c ⊓ b)    [por conmutatividad de ⊓]
--                = (a ⊓ c) ⊔ (b ⊓ c)    [por conmutatividad de ⊓]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
calc
  (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)       := by rw [inf_comm]
            _ = (c ⊓ a) ⊔ (c ⊓ b) := by rw [h]
            _ = (a ⊓ c) ⊔ (c ⊓ b) := by rw [@inf_comm _ _ c a]
            _ = (a ⊓ c) ⊔ (b ⊓ c) := by rw [@inf_comm _ _ c b]

-- 2ª demostración
example
  (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
by simp [h, inf_comm]

-- Lemas usados
-- ============

#check (inf_comm : a ⊓ b = b ⊓ a)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)
-- entonces
--    (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por la siguiente cadena de igualdades
--    (a ⊓ b) ⊔ c = c ⊔ (a ⊓ b)          [por la conmutatividad de ⊔]
--                = (c ⊔ a) ⊓ (c ⊔ b)    [por la hipótesis]
--                = (a ⊔ c) ⊓ (c ⊔ b)    [por la conmutatividad de ⊔]
--                = (a ⊔ c) ⊓ (b ⊔ c)    [por la conmutatividad de ⊔]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
calc
  (a ⊓ b) ⊔ c = c ⊔ (a ⊓ b)       := by rw [sup_comm]
            _ = (c ⊔ a) ⊓ (c ⊔ b) := by rw [h]
            _ = (a ⊔ c) ⊓ (c ⊔ b) := by rw [@sup_comm _ _ c a]
            _ = (a ⊔ c) ⊓ (b ⊔ c) := by rw [@sup_comm _ _ c b]

-- 2ª demostración
example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
by simp [h, sup_comm]

-- Lemas usados
-- ============

#check (sup_comm : a ⊔ b = b ⊔ a)
