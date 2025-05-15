-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Inportar la librería de tácticas.
-- 2. Declarar α como una variable de tipos.
-- 3. Declarar P una variable sobre las propiedades de α.
-- ----------------------------------------------------------------------

import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ¬ ∃ x, P x
-- entonces
--    ∀ x, ¬ P x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y un elemento cualquiera. Tenemos que demostrar ¬P(y). Para ello,
-- supongamos que P(y). Entonces, (∃x)P(x) que es una contradicción con
-- la hipótesis,

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  existsi y
  -- ⊢ P y
  exact h1

-- Comentario: La táctica (existsi e) es la regla de introducción del
-- existencial; es decir, sustituye en el cuerpo del objetivo
-- existencial su variable por e

-- 2ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  use y
  -- ⊢ P y
  exact h1

-- 3ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  exact ⟨y, h1⟩

-- 4ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  exact h ⟨y, h1⟩

-- 5ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
fun y h1 ↦ h ⟨y, h1⟩

-- 6ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  push_neg at h
  -- h : ∀ (x : α), ¬P x
  exact h

-- 7ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
not_exists.mp h

-- 8ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_exists : (¬∃ x, P x) ↔ ∀ (x : α), ¬P x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    ∀ x, ¬ P x
-- entonces
--    ¬ ∃ x, P x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que (∃x)P(x). Sea y tal que P(y). Puesto que (∀x)¬P)x), se
-- tiene que ¬P(y) que es una contradicción con P(y).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  intro h1
  -- h1 : ∃ x, P x
  -- ⊢ False
  rcases h1 with ⟨y, hy⟩
  -- y : α
  -- hy : P y
  have h2 : ¬P y := h y
  exact h2 hy

-- 2ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  intro h1
  -- h1 : ∃ x, P x
  -- ⊢ False
  rcases h1 with ⟨y, hy⟩
  -- y : α
  -- hy : P y
  exact (h y) hy

-- 3ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  rintro ⟨y, hy⟩
  -- y : α
  -- hy : P y
  exact (h y) hy

-- 4ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
fun ⟨y, hy⟩ ↦ (h y) hy

-- 5ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
not_exists_of_forall_not h

-- 6ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by aesop

-- Lemas usados
-- ============

-- variable (q : Prop)
-- #check (not_exists_of_forall_not : (∀ x, P x → q) → (∃ x, P x) → q)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    ¬ ∀ x, P x
-- entonces
--    ∃ x, ¬ P x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por reducción al absurdo, supongamos que ¬(∃x)¬P(x). Para obtener una
-- contradicción, demostraremos la negación de la hipótesis; es decir,
-- que (∀x)P(x). Para ello, sea y un elemento cualquiera y tenemos que
-- demostrar P(y). De nuevo, lo haremos por reducción al absurdo: Para
-- ello, supongamos que ¬P(y). Entonces, se tiene que (∃x)¬P(x) en
-- contradicción con nuestro primer supuesto de ¬(∃x)¬P(x).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
by
  by_contra h1
  -- h1 : ¬∃ x, ¬P x
  -- ⊢ False
  apply h
  -- ⊢ ∀ (x : α), P x
  intro y
  -- y : α
  -- ⊢ P y
  show P y
  by_contra h2
  -- h2 : ¬P y
  -- ⊢ False
  exact h1 ⟨y, h2⟩

-- Comentarios:
-- 1. La táctica (by_contra h) es la regla de reducción al absurdo; es
--    decir, si el objetivo es p añade la hipótesis (h : p) y reduce el
--    objetivo a False.
-- 2. La táctica (exact h1 ⟨x, h2⟩) es la regla de inntroducción del
--    cuantificador existencial; es decir, si el objetivo es de la forma
--    (∃y, P y) demuestra (P x) con h2 y unifica h1 con (∃x, P x).

-- 2ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
not_forall.mp h

-- 3ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que si
--    ∃ x, ¬ P x
-- entonces
--    ¬ ∀ x, P x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que (∀x)P(x) y tenemos que demostrar una
-- contradicción. Por hipótesis, (∃x)¬P(x). Sea y tal que
-- ¬P(y). Entonces, como (∀x)P(x), se tiene que P(y) que es una
-- contradicción con ¬P(y).

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  rcases h with ⟨y, hy⟩
  -- y : α
  -- hy : ¬P y
  apply hy
  -- ⊢ P y
  exact (h1 y)

-- Comentarios:
-- 1. La táctica (intro h), cuando el objetivo es una negación, es la
--    regla de introducción de la negación; es decir, si el objetivo es
--    ¬P entonces añade la hipótesis (h : P) y cambia el objetivo a
--    false.
-- 2. La táctica (cases' h with x hx), cuando la hipótesis es un
--    existencial, es la regla de eliminación del existencial; es decir,
--    si h es (∃ (y : α), P y) añade las hipótesis (x : α) y (hx : P x).

-- 2ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  rcases h with ⟨y, hy⟩
  -- y : α
  -- hy : ¬P y
  apply hy
  -- ⊢ P y
  exact (h1 y)

-- 3ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  rcases h with ⟨y, hy⟩
  -- y : α
  -- hy : ¬P y
  exact hy (h1 y)

-- 4ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
not_forall.mpr h

-- 5ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
not_forall_of_exists_not h

-- 5ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
-- #check (not_forall_of_exists_not : (∃ x, ¬P x) → ¬∀ x, P x)
