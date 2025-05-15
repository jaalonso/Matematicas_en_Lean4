-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los productos de los números naturales por
-- números pares son pares.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Si n es par, entonces (por la definición de `Even`) existe un k tal que
--    n = k + k         (1)
-- Por tanto,
--    mn = m(k + k)     (por (1))
--       = mk + mk      (por la propiedad distributiva)
-- Por consiguiente, mn es par.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 1ª demostración
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
example : ∀ m n : Nat, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk, mul_add]

-- 5ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) :=
by
  rintro m n ⟨k, hk⟩
  -- m n k : ℕ
  -- hk : n = k + k
  -- ⊢ Even (m * n)
  exact ⟨m * k, by rw [hk, mul_add]⟩

-- 6ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

-- 7ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
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
  | intro k hk
    -- k : ℕ
    -- hk : n = k + k
    =>
    use m * k
    -- ⊢ m * n = m * k + m * k
    rw [hk, mul_add]

-- 9ª demostración
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
  | intro k hk
    -- k : ℕ
    -- hk : n = k + k
    =>
    use m * k
    calc m * n
       = m * (k + k)   := by exact congrArg (HMul.hMul m) hk
     _ = m * k + m * k := by exact mul_add m k k

-- 10ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) :=
by
  intros; simp [*, parity_simps]

-- Comentarios:
-- 1. Al poner el curso en la línea 1 sobre Mathlib.Data.Nat.Parity y pulsar M-.
--    se abre la teoría correspondiente.
-- 2. Al colocar el cursor sobre el nombre de un lema se ve su enunciado.
-- 3. Para completar el nombre de un lema basta escribir parte de su
--    nombre y completar con S-SPC (es decir, simultáneamente las teclas
--    de mayúscula y la de espacio).
-- 4. El lema que se ha usado es
--       mul_add a b c : a * (b + c) = a * b + a * c
-- 4. Se activa la ventana de objetivos (*Lean Goal*) pulsando C-c TAB
-- 5. Al mover el cursor sobre las pruebas se actualiza la ventana de
--    objetivos.
