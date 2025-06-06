-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la relación de divisibilidad es transitiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que a | b y b | c. Entonces, existen d y e tales que
--    b = ad                                                         (1)
--    c = be                                                         (2)
-- Por tanto,
--    c = be       [por (2)]
--      = (ad)e    [por (1)]
--      = a(de)
-- Por consiguiente, a | c.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divbc with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = b * e
  have h1 : c = a * (d * e) :=
    calc c = b * e      := ceq
        _ = (a * d) * e := congrArg (. * e) beq
        _ = a * (d * e) := mul_assoc a d e
  show a ∣ c
  exact Dvd.intro (d * e) h1.symm

-- 2ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divbc with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = b * e
  use (d * e)
  -- ⊢ c = a * (d * e)
  rw [ceq, beq]
  -- ⊢ (a * d) * e = a * (d * e)
  exact mul_assoc a d e

-- 3ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divbc with ⟨e, rfl⟩
  -- e : ℕ
  -- ⊢ a ∣ b * e
  rcases divab with ⟨d, rfl⟩
  -- d : ℕ
  -- ⊢ a ∣ a * d * e
  use (d * e)
  -- ⊢ (a * d) * e = a * (d * e)
  ring

-- 4ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divab with ⟨d, beq⟩
  -- d : ℕ
  -- beq : b = a * d
  rcases divbc with ⟨e, ceq⟩
  -- e : ℕ
  -- ceq : c = b * e
  rw [ceq, beq]
  -- ⊢ a ∣ a * d * e
  use (d * e)
  -- ⊢ (a * d) * e = a * (d * e)
  exact mul_assoc a d e

-- Lemas usados
-- ============

variable (f : ℕ → ℕ)
#check (Dvd.intro c : a * c = b → a ∣ b)
#check (congrArg f : a = b → f a = f b)
#check (mul_assoc a b c : (a * b) * c = a * (b * c))
