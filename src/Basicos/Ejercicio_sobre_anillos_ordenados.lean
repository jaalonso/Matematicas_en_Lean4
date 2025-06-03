-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de los anillos ordenados.
--    2. Declarar R como un tipo sobre los anillos ordenados.
--    3. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

import Mathlib.Algebra.Order.Ring.Defs                                  -- 1
variable {R : Type _} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] -- 2
variable (a b c : R)                                                    -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a ≤ b → 0 ≤ b - a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    sub_self         : a - a = 0
--    sub_le_sub_right : a ≤ b → ∀ (c : R), a - c ≤ b - c
--
-- Supongamos que
--    a ≤ b                                                          (1)
-- La demostración se tiene por la siguiente cadena de desigualdades:
--    0 = a - a    [por sub_self]
--      ≤ b - a    [por (1) y sub_le_sub_right]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example : a ≤ b → 0 ≤ b - a :=
by
  intro h
  -- h : a ≤ b
  -- ⊢ 0 ≤ b - a
  calc
    0 = a - a := (sub_self a).symm
    _ ≤ b - a := sub_le_sub_right h a

-- 2ª demostración
example : a ≤ b → 0 ≤ b - a :=
sub_nonneg.mpr

-- 3ª demostración
example : a ≤ b → 0 ≤ b - a :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    0 ≤ b - a → a ≤ b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    zero_add a : 0 + a = a
--    add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a
--    sub_add_cancel a b : a - b + b = -a
--
-- Supongamos que
--    0 ≤ b - a                                                      (1)
-- La demostración se tiene por la siguiente cadena de desigualdades:
--    a = 0 + a          [por zero_add]
--      ≤ (b - a) + a    [por (1) y add_le_add_right]
--      = b              [por sub_add_cancel]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by
  intro h
  -- h : 0 ≤ b - a
  -- ⊢ a ≤ b
  calc
    a = 0 + a       := (zero_add a).symm
    _ ≤ (b - a) + a := add_le_add_right h a
    _ = b           := sub_add_cancel b a

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by apply?
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    a ≤ b
--    0 ≤ c
-- entonces
--    a * c ≤ b * c
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
--    mul_nonneg                 : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
--    sub_mul a b c              : (a - b) * c = a * c - b * c)
--    sub_nonneg                 : 0 ≤ a - b ↔ b ≤ a)
--
-- Supongamos que
--    a ≤ b                                                          (1)
--    0 ≤ c
-- De (1), por sub_nonneg, se tiene
--    0 ≤ b - a
-- y con (2), por mul_nonneg, se tiene
--    0 ≤ (b - a) * c
-- que, por sub_mul, da
--    0 ≤ b * c - a * c
-- y, aplicándole sub_nonneg, se tiene
--    a * c ≤ b * c

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a :=
    sub_nonneg.mpr h1
  have h4 : 0 ≤ b * c - a * c := calc
    0 ≤ (b - a) * c   := mul_nonneg h3 h2
    _ = b * c - a * c := sub_mul b a c
  show a * c ≤ b * c
  exact sub_nonneg.mp h4

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a := sub_nonneg.mpr h1
  have h4 : 0 ≤ (b - a) * c := mul_nonneg h3 h2
  rw [sub_mul] at h4
  -- h4 : 0 ≤ b * c - a * c
  exact sub_nonneg.mp h4

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  apply sub_nonneg.mp
  -- ⊢ 0 ≤ b * c - a * c
  rw [← sub_mul]
  -- ⊢ 0 ≤ (b - a) * c
  apply mul_nonneg
  . -- ⊢ 0 ≤ b - a
    exact sub_nonneg.mpr h1
  . -- ⊢ 0 ≤ c
    exact h2

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  apply sub_nonneg.mp
  -- ⊢ 0 ≤ b * c - a * c
  rw [← sub_mul]
  -- ⊢ 0 ≤ (b - a) * c
  apply mul_nonneg (sub_nonneg.mpr h1) h2

-- 5ª demostración
example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
-- by apply?
mul_le_mul_of_nonneg_right h1 h2

-- Lemas usados
-- ============

#check (add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a)
#check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
#check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check (sub_add_cancel a b : a - b + b = a)
#check (sub_le_sub_right : a ≤ b → ∀ c, a - c ≤ b - c)
#check (sub_mul a b c : (a - b) * c = a * c - b * c)
#check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
#check (sub_self a : a - a = 0)
#check (zero_add a :  0 + a = a)
