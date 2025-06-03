-- ---------------------------------------------------------------------
-- Demostrar que los productos de los números naturales por números
-- pares son pares.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Si n es par, entonces (por la definición de `Even`) existe un k tal que
--    n = k + k         (1)
-- Por tanto,
--    mn = m(k + k)     (por (1))
--       = mk + mk      (por la propiedad distributiva)
-- Por consiguiente, mn es par.

-- Demostraciones en Lean4
-- =======================

import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

variable (m n : ℕ)

open Nat

-- 1ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  use m * k
  -- ⊢ m * n = m * k + m * k
  rw [hk]
  -- ⊢ m * (k + k) = m * k + m * k
  ring

-- 2ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  use m * k
  -- ⊢ m * n = m * k + m * k
  rw [hk]
  -- ⊢ m * (k + k) = m * k + m * k
  rw [mul_add]

-- 3ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  use m * k
  -- ⊢ m * n = m * k + m * k
  rw [hk, mul_add]

-- 4ª demostración
-- ===============

example : ∀ m n : Nat, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk, mul_add]

-- 5ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  exact ⟨m * k, by rw [hk, mul_add]⟩

-- 6ª demostración
-- ===============

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

-- 7ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  use m * k
  -- ⊢ m * n = m * k + m * k
  rw [hk]
  -- ⊢ m * (k + k) = m * k + m * k
  exact mul_add m k k

-- 8ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  intros m n hn
  -- m n : ℕ
  -- hn : Even n
  -- ⊢ Even (m * n)
  unfold Even at *
  -- hn : ∃ r, n = r + r
  -- ⊢ ∃ r, m * n = r + r
  cases hn with
  | intro k hk =>
    -- k : ℕ
    -- hk : n = k + k
    use m * k
    -- ⊢ m * n = m * k + m * k
    rw [hk, mul_add]

-- 9ª demostración
-- ===============

example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  intros m n hn
  -- m n : ℕ
  -- hn : Even n
  -- ⊢ Even (m * n)
  unfold Even at *
  -- hn : ∃ r, n = r + r
  -- ⊢ ∃ r, m * n = r + r
  cases hn with
  | intro k hk =>
    -- k : ℕ
    -- hk : n = k + k
    use m * k
    -- ⊢ m * n = m * k + m * k
    calc m * n
       = m * (k + k)   := congrArg (HMul.hMul m) hk
     _ = m * k + m * k := mul_add m k k

-- 10ª demostración
-- ================

example : ∀ m n : Nat, Even n → Even (m * n) :=
by
  intros
  -- m n : ℕ
  -- a : Even n
  -- ⊢ Even (m * n)
  simp [*, parity_simps]

-- Lemas usados
-- ============

variable (a b c : ℕ)
variable (f : ℕ → ℕ)
#check (mul_add a b c : a * (b + c) = a * b + a * c)
#check (congrArg f : a = b → f a = f b)
