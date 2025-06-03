import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set

variable {α : Type}
variable (s t : Set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ s ∩ (s ∪ t) ↔ x ∈ s]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Sea x ∈ s ∩ (s ∪ t). Entonces, x ∈ s.
--
-- (⟸) Sea x ∈ s. Entonces, x ∈ s ∪ t y, por tanto,
-- x ∈ s ∩ (s ∪ t).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intros h
  -- h : x ∈ s ∩ (s ∪ t)
  -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intro h
    -- h : x ∈ s ∩ (s ∪ t)
    -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      exact (Or.inl xs)

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨fun h ↦ h.1,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨And.left,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    rintro ⟨xs, -⟩
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    use xs
    -- ⊢ x ∈ s ∪ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  apply subset_antisymm
  . -- ⊢ s ∩ (s ∪ t) ⊆ s
    rintro x ⟨hxs, -⟩
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ s ⊆ s ∩ (s ∪ t)
    intros x hxs
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    exact ⟨hxs, Or.inl hxs⟩

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self

-- 8ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by aesop

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ s ∪ (s ∩ t) ↔ x ∈ s]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Sea x ∈ s ∪ (s ∩ t). Entonces, c ∈ s o x ∈ s ∩ t. En ambos casos,
-- x ∈ s.
--
-- (⟸) Sea x ∈ s. Entonces, x ∈ s ∩ t y, por tanto, x ∈ s ∪ (s ∩ t).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    intro hx
    -- hx : x ∈ s ∪ (s ∩ t)
    -- ⊢ x ∈ s
    rcases hx with (xs | xst)
    . -- xs : x ∈ s
      exact xs
    . -- xst : x ∈ s ∩ t
      exact xst.1
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ (s ∩ t)
    left
    -- ⊢ x ∈ s
    exact xs

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ s ∩ t ↔ x ∈ s
  exact ⟨fun hx ↦ Or.elim hx id And.left,
         fun xs ↦ Or.inl xs⟩

-- 3ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    rintro (xs | ⟨xs, -⟩) <;>
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ s ∩ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) ∪ t = s ∪ t
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t]
-- y lo demostraremos por la siguiente cadena de equivalencias:
--    x ∈ (s \ t) ∪ t ↔ x ∈ (s \ t) ∨ (x ∈ t)
--                    ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t
--                    ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t)
--                    ↔ x ∈ s ∨ x ∈ t
--                    ↔ x ∈ s ∪ t

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  calc x ∈ (s \ t) ∪ t
       ↔ x ∈ s \ t ∨ x ∈ t                 := mem_union x (s \ t) t
     _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t           := by simp only [mem_diff x]
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t) := and_or_right
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ True            := by simp only [em' (x ∈ t)]
     _ ↔ x ∈ s ∨ x ∈ t                     := (and_true (x ∈ s ∨ x ∈ t)).to_iff
     _ ↔ x ∈ s ∪ t                         := (mem_union x s t).symm

-- 2ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    intro hx
    -- hx : x ∈ (s \ t) ∪ t
    -- ⊢ x ∈ s ∪ t
    rcases hx with (xst | xt)
    . -- xst : x ∈ s \ t
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xst.1
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      intro hx
      -- hx : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      rcases hx with (xs | xt)
      . -- xs : x ∈ s
        left
        -- ⊢ x ∈ s \ t
        constructor
        . -- ⊢ x ∈ s
          exact xs
        . -- ⊢ ¬x ∈ t
          exact h
      . -- xt : x ∈ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 3ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    rintro (⟨xs, -⟩ | xt)
    . -- xs : x ∈ s
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      rintro (xs | xt)
      . -- xs : x ∈ s
        -- ⊢ x ∈ (s \ t) ∪ t
        left
        -- ⊢ x ∈ s \ t
        exact ⟨xs, h⟩
      . -- xt : x ∈ t
        -- ⊢ x ∈ (s \ t) ∪ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 4ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
diff_union_self

-- 5ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s \ t ∪ t ↔ x ∈ s ∪ t
  simp

-- 6ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
-- Se demuestra mediante la siguiente cadena de equivalencias:
--    x ∈ (s \ t) ∪ (t \ s)
--    ↔ x ∈ (s \ t) ∨ x ∈ (t \ s)
--    ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ (t \ s)
--    ↔ (x ∈ s ∨ x ∈ (t \ s)) ∧ (x ∉ t ∨ x ∈ (t \ s))
--    ↔ (x ∈ s ∨ (x ∈ t ∧ x ∉ s)) ∧ (x ∉ t ∨ (x ∈ t ∧ x ∉ s))
--    ↔ ((x ∈ s ∨ x ∈ t) ∧ (x ∈ s ∨ x ∉ s)) ∧ ((x ∉ t ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s))
--    ↔ ((x ∈ s ∨ x ∈ t) ∧ True) ∧ (True ∧ (x ∉ t ∨ x ∉ s))
--    ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s)
--    ↔ (x ∈ s ∪ t) ∧ (x ∉ t ∨ x ∉ s)
--    ↔ (x ∈ s ∪ t) ∧ (x ∉ s ∨ x ∉ t)
--    ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∧ x ∈ t)
--    ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∩ t)
--    ↔ x ∈ (s ∪ t) \ (s ∩ t)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  calc x ∈ (s \ t) ∪ (t \ s)
     ↔ x ∈ (s \ t) ∨ x ∈ (t \ s) :=
         by exact mem_union x (s \ t) (t \ s)
   _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ (t \ s) :=
         by simp only [mem_diff]
   _ ↔ (x ∈ s ∨ x ∈ (t \ s)) ∧ (x ∉ t ∨ x ∈ (t \ s)) :=
         by exact and_or_right
   _ ↔ (x ∈ s ∨ (x ∈ t ∧ x ∉ s)) ∧ (x ∉ t ∨ (x ∈ t ∧ x ∉ s)) :=
         by simp only [mem_diff]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ (x ∈ s ∨ x ∉ s)) ∧
       ((x ∉ t ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp_all only [or_and_left]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ True) ∧
       (True ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp only [em (x ∈ s), em' (x ∈ t)]
   _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [and_true (x ∈ s ∨ x ∈ t),
                       true_and (¬x ∈ t ∨ ¬x ∈ s)]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [mem_union]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ s ∨ x ∉ t) :=
         by simp only [or_comm]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∧ x ∈ t) :=
         by simp only [not_and_or]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∩ t) :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ (s ∪ t) \ (s ∩ t)     :=
         by simp only [mem_diff]

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xs : x ∈ s
      -- xnt : ¬x ∈ t
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        left
        -- ⊢ x ∈ s
        exact xs
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨-, xt⟩
        -- xt : x ∈ t
        -- ⊢ False
        exact xnt xt
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        right
        -- ⊢ x ∈ t
        exact xt
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨xs, -⟩
        -- xs : x ∈ s
        -- ⊢ False
        exact xns xs
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      left
      -- ⊢ x ∈ s \ t
      use xs
      -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      right
      -- ⊢ x ∈ t \ s
      use xt
      -- ⊢ ¬x ∈ s
      intro xs
      -- xs : x ∈ s
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
  . rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩) <;> aesop
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩ <;> aesop

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor
  . aesop
  . aesop

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor <;> aesop

-- 7ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  rw [Set.ext_iff]
  -- ⊢ ∀ (x : α), x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  intro
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  rw [iff_def]
  -- ⊢ (x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)) ∧
  --   (x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s))
  aesop

-- Lemas usados
-- ============

variable (x : α)
variable (a b c : Prop)
#check (And.left : a ∧ b → a)
#check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
#check (Or.inl : a → a ∨ b)
#check (Or.inr : b → a ∨ b)
#check (Set.ext_iff : s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
#check (and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c))
#check (and_true a : (a ∧ True) = a)
#check ((and_true a).to_iff : (a ∧ True) ↔ a)
#check (diff_union_self : (s \ t) ∪ t = s ∪ t)
#check (em a : a ∨ ¬ a)
#check (em' a : ¬ a ∨ a)
#check (iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a))
#check (inf_sup_self : s ∩ (s ∪ t) = s)
#check (mem_diff x : x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t)
#check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
#check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
#check (not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b)
#check (or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c))
#check (or_comm : a ∨ b ↔ b ∨ a)
#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)
#check (sup_inf_self : s ∪ (s ∩ t) = s)
#check (true_and a : (True ∧ a) = a)
