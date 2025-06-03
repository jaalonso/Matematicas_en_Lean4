-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que si a es un divisor de b y de c, tambien lo
-- es de b + c.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que a divide a b y a c, existen d y e tales que
--    b = ad                                                         (1)
--    c = ae                                                         (2)
-- Por tanto,
--    b + c = ad + c     [por (1)]
--          = ad + ae    [por (2)]
--          = a(d + e)   [por la distributiva]
-- Por consiguiente, a divide a b + c.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divac with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = a * e
  have h1 : b + c = a * (d + e) :=
    calc b + c
         = (a * d) + c       := congrArg (. + c) beq
       _ = (a * d) + (a * e) := congrArg ((a * d) + .) ceq
       _ = a * (d + e)       := by rw [← mul_add]
  show a ∣ (b + c)
  exact Dvd.intro (d + e) h1.symm

-- 2ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divac with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = a * e
  have h1 : b + c = a * (d + e) := by linarith
  show a ∣ (b + c)
  exact Dvd.intro (d + e) h1.symm

-- 3ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divac with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = a * e
  show a ∣ (b + c)
  exact Dvd.intro (d + e) (by linarith)

-- 4ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
by
  obtain ⟨d, beq⟩ := divab
  -- d : ℕ
  -- beq : b = a * d
  obtain ⟨e, ceq⟩ := divac
  -- e : ℕ
  -- ceq : c = a * e
  rw [ceq, beq]
  -- ⊢ a ∣ a * d + a * e
  use (d + e)
  -- ⊢ a * d + a * e = a * (d + e)
  ring

-- 5ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases divab with ⟨d, rfl⟩
  -- ⊢ a ∣ a * d + c
  rcases divac with ⟨e, rfl⟩
  -- ⊢ a ∣ a * d + a * e
  use (d + e)
  -- ⊢ a * d + a * e = a * (d + e)
  ring

-- 6ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
dvd_add divab divac

-- Lemas usados
-- ============

variable (f : ℕ → ℕ)
#check (Dvd.intro c : a * c = b → a ∣ b)
#check (congrArg f : a = b → f a = f b)
#check (dvd_add : a ∣ b →  a ∣ c → a ∣ (b + c))
#check (mul_add a b c : a * (b + c) = a * b + a * c)
