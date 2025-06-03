import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set Function

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)
variable (B : I → Set β)

-- ----------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f[⋃ᵢAᵢ] = ⋃ᵢf[Aᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo y,
--    y ∈ f[⋃ᵢAᵢ] ↔ y ∈ ⋃ᵢf[Aᵢ]
-- Lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que y ∈ f[⋃ᵢAᵢ]. Entonces, existe un x tal que
--    x ∈ ⋃ᵢAᵢ                                                       (1)
--    f(x) = y                                                       (2)
-- Por (1), existe un i tal que
--    i ∈ ℕ                                                          (3)
--    x ∈ Aᵢ                                                         (4)
-- Por (4),
--    f(x) ∈ f[Aᵢ]
-- Por (3),
--    f(x) ∈ ⋃ᵢf[Aᵢ]
-- y, por (2),
--    y ∈ ⋃ᵢf[Aᵢ]
--
-- (⟸) Supongamos que y ∈ ⋃ᵢf[Aᵢ]. Entonces, existe un i tal que
--    i ∈ ℕ                                                          (5)
--    y ∈ f[Aᵢ]                                                      (6)
-- Por (6), existe un x tal que
--    x ∈ Aᵢ                                                         (7)
--    f(x) = y                                                       (8)
-- Por (5) y (7),
--    x ∈ ⋃ᵢAᵢ
-- Luego,
--    f(x) ∈ f[⋃ᵢAᵢ]
-- y, por (8),
--    y ∈ f[⋃ᵢAᵢ]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  constructor
  . -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i → y ∈ ⋃ (i : ℕ), f '' A i
    intro hy
    -- hy : y ∈ f '' ⋃ (i : ℕ), A i
    -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i
    have h1 : ∃ x, x ∈ ⋃ i, A i ∧ f x = y :=
      (mem_image f (⋃ i, A i) y).mp hy
    obtain ⟨x, hx : x ∈ ⋃ i, A i ∧ f x = y⟩ := h1
    have xUA : x ∈ ⋃ i, A i := hx.1
    have fxy : f x = y := hx.2
    have xUA : ∃ i, x ∈ A i := mem_iUnion.mp xUA
    obtain ⟨i, xAi : x ∈ A i⟩ := xUA
    have h2 : f x ∈ f '' A i := mem_image_of_mem f xAi
    have h3 : f x ∈ ⋃ i, f '' A i := mem_iUnion_of_mem i h2
    show y ∈ ⋃ i, f '' A i
    rwa [fxy] at h3
  . -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i → y ∈ f '' ⋃ (i : ℕ), A i
    intro hy
    -- hy : y ∈ ⋃ (i : ℕ), f '' A i
    -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i
    have h4 : ∃ i, y ∈ f '' A i := mem_iUnion.mp hy
    obtain ⟨i, h5 : y ∈ f '' A i⟩ := h4
    have h6 : ∃ x, x ∈ A i ∧ f x = y :=
      (mem_image f (A i) y).mp h5
    obtain ⟨x, h7 : x ∈ A i ∧ f x = y⟩ := h6
    have h8 : x ∈ A i := h7.1
    have h9 : x ∈ ⋃ i, A i := mem_iUnion_of_mem i h8
    have h10 : f x ∈ f '' (⋃ i, A i) := mem_image_of_mem f h9
    show y ∈ f '' (⋃ i, A i)
    rwa [h7.2] at h10

-- 2ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  constructor
  . -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i → y ∈ ⋃ (i : ℕ), f '' A i
    intro hy
    -- hy : y ∈ f '' ⋃ (i : ℕ), A i
    -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i
    rw [mem_image] at hy
    -- hy : ∃ x, x ∈ ⋃ (i : ℕ), A i ∧ f x = y
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ ⋃ (i : ℕ), A i ∧ f x = y
    cases' hx with xUA fxy
    -- xUA : x ∈ ⋃ (i : ℕ), A i
    -- fxy : f x = y
    rw [mem_iUnion] at xUA
    -- xUA : ∃ i, x ∈ A i
    cases' xUA with i xAi
    -- i : ℕ
    -- xAi : x ∈ A i
    rw [mem_iUnion]
    -- ⊢ ∃ i, y ∈ f '' A i
    use i
    -- ⊢ y ∈ f '' A i
    rw [←fxy]
    -- ⊢ f x ∈ f '' A i
    apply mem_image_of_mem
    -- ⊢ x ∈ A i
    exact xAi
  . -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i → y ∈ f '' ⋃ (i : ℕ), A i
    intro hy
    -- hy : y ∈ ⋃ (i : ℕ), f '' A i
    -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i
    rw [mem_iUnion] at hy
    -- hy : ∃ i, y ∈ f '' A i
    cases' hy with i yAi
    -- i : ℕ
    -- yAi : y ∈ f '' A i
    cases' yAi with x hx
    -- x : α
    -- hx : x ∈ A i ∧ f x = y
    cases' hx with xAi fxy
    -- xAi : x ∈ A i
    -- fxy : f x = y
    rw [←fxy]
    -- ⊢ f x ∈ f '' ⋃ (i : ℕ), A i
    apply mem_image_of_mem
    -- ⊢ x ∈ ⋃ (i : ℕ), A i
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ A i
    use i

-- 3ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  simp
  -- ⊢ (∃ x, (∃ i, x ∈ A i) ∧ f x = y) ↔ ∃ i x, x ∈ A i ∧ f x = y
  constructor
  . -- ⊢ (∃ x, (∃ i, x ∈ A i) ∧ f x = y) → ∃ i x, x ∈ A i ∧ f x = y
    rintro ⟨x, ⟨i, xAi⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ ∃ i x, x ∈ A i ∧ f x = y
    use i, x, xAi
  . -- ⊢ (∃ i x, x ∈ A i ∧ f x = y) → ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    rintro ⟨i, x, xAi, fxy⟩
    -- i : ℕ
    -- x : α
    -- xAi : x ∈ A i
    -- fxy : f x = y
    -- ⊢ ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    exact ⟨x, ⟨i, xAi⟩, fxy⟩

-- 4ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
image_iUnion

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y tal que
--    y ∈ f[⋂ᵢ Aᵢ]                                                   (1)
-- Tenemos que demostrar que y ∈ ⋂ᵢ f[Aᵢ]. Para ello, sea i ∈ I, tenemos
-- que demostrar que y ∈ f[Aᵢ].
--
-- Por (1), existe un x tal que
--    x ∈ ⋂ᵢ Aᵢ                                                      (2)
--    f(x) = y                                                       (3)
-- Por (2),
--    x ∈ Aᵢ
-- y, por tanto,
--    f(x) ∈ f[Aᵢ]
-- que, junto con (3), da que
--    y ∈ f[Aᵢ]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  have h1 : ∃ x, x ∈ ⋂ i, A i ∧ f x = y :=
    (mem_image f (⋂ i, A i) y).mp h
  obtain ⟨x, hx : x ∈ ⋂ i, A i ∧ f x = y⟩ := h1
  have h2 : x ∈ ⋂ i, A i := hx.1
  have h3 : f x = y := hx.2
  have h4 : ∀ i, y ∈ f '' A i := by
    intro i
    have h4a : x ∈ A i := mem_iInter.mp h2 i
    have h4b : f x ∈ f '' A i := mem_image_of_mem f h4a
    show y ∈ f '' A i
    rwa [h3] at h4b
  show y ∈ ⋂ i, f '' A i
  exact mem_iInter.mpr h4

-- 2ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  apply mem_iInter_of_mem
  -- ⊢ ∀ (i : I), y ∈ f '' A i
  intro i
  -- i : I
  -- ⊢ y ∈ f '' A i
  cases' h with x hx
  -- x : α
  -- hx : x ∈ ⋂ (i : I), A i ∧ f x = y
  cases' hx with xIA fxy
  -- xIA : x ∈ ⋂ (i : I), A i
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ f '' A i
  apply mem_image_of_mem
  -- ⊢ x ∈ A i
  exact mem_iInter.mp xIA i

-- 3ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  apply mem_iInter_of_mem
  -- ⊢ ∀ (i : I), y ∈ f '' A i
  intro i
  -- i : I
  -- ⊢ y ∈ f '' A i
  rcases h with ⟨x, xIA, rfl⟩
  -- x : α
  -- xIA : x ∈ ⋂ (i : I), A i
  -- ⊢ f x ∈ f '' A i
  exact mem_image_of_mem f (mem_iInter.mp xIA i)

-- 4ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intro y
  -- y : β
  -- ⊢ y ∈ f '' ⋂ (i : I), A i → y ∈ ⋂ (i : I), f '' A i
  simp
  -- ⊢ ∀ (x : α), (∀ (i : I), x ∈ A i) → f x = y → ∀ (i : I), ∃ x, x ∈ A i ∧ f x = y
  intros x xIA fxy i
  -- x : α
  -- xIA : ∀ (i : I), x ∈ A i
  -- fxy : f x = y
  -- i : I
  -- ⊢ ∃ x, x ∈ A i ∧ f x = y
  use x, xIA i

-- 5ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
image_iInter_subset A f

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva e I no vacío, entonces
--    (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ ⋂ᵢf[Aᵢ]. Entonces,
--    (∀i ∈ I)y ∈ f[Aᵢ]                                              (1)
--    y ∈ f[Aᵢ]
-- Por tanto, existe un x ∈ Aᵢ tal que
--    f(x) = y                                                       (2)
--
-- Veamos que x ∈ ⋂ᵢAᵢ. Para ello, sea j ∈ I. Por (1),
--    y ∈ f[Aⱼ]
-- Luego, existe un z tal que
--    z ∈ Aⱼ                                                         (3)
--    f(z) = y
-- Por (2),
--    f(x) = f(z)
-- y, por ser f inyectiva,
--    x = z
-- y, Por (3),
--    x ∈ Aⱼ
--
-- Puesto que x ∈ ⋂ᵢAᵢ se tiene que f(x) ∈ f[⋂ᵢAᵢ] y, por (2),
-- y ∈ f[⋂ᵢAᵢ].

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  have h1 : ∀ (i : I), y ∈ f '' A i := mem_iInter.mp hy
  have h2 : y ∈ f '' A i := h1 i
  obtain ⟨x : α, h3 : x ∈ A i ∧ f x = y⟩ := h2
  have h4 : f x = y := h3.2
  have h5 : ∀ i : I, x ∈ A i := by
    intro j
    have h5a : y ∈ f '' A j := h1 j
    obtain ⟨z : α, h5b : z ∈ A j ∧ f z = y⟩ := h5a
    have h5c : z ∈ A j := h5b.1
    have h5d : f z = y := h5b.2
    have h5e : f z = f x := by rwa [←h4] at h5d
    have h5f : z = x := injf h5e
    show x ∈ A j
    rwa [h5f] at h5c
  have h6 : x ∈ ⋂ i, A i := mem_iInter.mpr h5
  have h7 : f x ∈ f '' (⋂ i, A i) := mem_image_of_mem f h6
  show y ∈ f '' (⋂ i, A i)
  rwa [h4] at h7

-- 2ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  rw [mem_iInter] at hy
  -- hy : ∀ (i : I), y ∈ f '' A i
  rcases hy i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ ⋂ (i : I), A i ∧ f x = y
  constructor
  . -- ⊢ x ∈ ⋂ (i : I), A i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases hy j with ⟨z, zAj, fzy⟩
    -- z : α
    -- zAj : z ∈ A j
    -- fzy : f z = y
    convert zAj
    -- ⊢ x = z
    apply injf
    -- ⊢ f x = f z
    rw [fxy]
    -- ⊢ y = f z
    rw [←fzy]
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intro y
  -- y : β
  -- ⊢ y ∈ ⋂ (i : I), f '' A i → y ∈ f '' ⋂ (i : I), A i
  simp
  -- ⊢ (∀ (i : I), ∃ x, x ∈ A i ∧ f x = y) → ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  intro h
  -- h : ∀ (i : I), ∃ x, x ∈ A i ∧ f x = y
  -- ⊢ ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  rcases h i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ (∀ (i : I), x ∈ A i) ∧ f x = y
  constructor
  . -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases h j with ⟨z, zAi, fzy⟩
    -- z : α
    -- zAi : z ∈ A j
    -- fzy : f z = y
    have : f x = f z := by rw [fxy, fzy]
    -- this : f x = f z
    have : x = z := injf this
    -- this : x = z
    rw [this]
    -- ⊢ z ∈ A j
    exact zAi
  . -- ⊢ f x = y
    exact fxy

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ f⁻¹[⋃ᵢ Bᵢ] ↔ x ∈ ⋃ᵢ f⁻¹[Bᵢ]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que x ∈ f⁻¹[⋃ᵢ Bᵢ]. Entonces, por la definición de la
-- imagen inversa,
--    f(x) ∈ ⋃ᵢ Bᵢ
-- y, por la definición de la unión, existe un i tal que
--    f(x) ∈ Bᵢ
-- y, por la definición de la imagen inversa,
--    x ∈ f⁻¹[Bᵢ]
-- y, por la definición de la unión,
--    x ∈ ⋃ᵢ f⁻¹[Bᵢ]
--
-- (⟸) Supongamos que x ∈ ⋃ᵢ f⁻¹[Bᵢ]. Entonces, por la definición de la
-- unión, existe un i tal que
--    x ∈ f⁻¹[Bᵢ]
-- y, por la definición de la imagen inversa,
--    f(x) ∈ Bᵢ
-- y, por la definición de la unión,
--    f(x) ∈ ⋃ᵢ Bᵢ
-- y, por la definición de la imagen inversa,
--    x ∈ f⁻¹[⋃ᵢ Bᵢ]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i ↔ x ∈ ⋃ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i → x ∈ ⋃ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋃ (i : I), B i
    -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, f x ∈ B i
    cases' hx with i fxBi
    -- i : I
    -- fxBi : f x ∈ B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ f ⁻¹' B i
    use i
    -- ⊢ x ∈ f ⁻¹' B i
    apply mem_preimage.mpr
    -- ⊢ f x ∈ B i
    exact fxBi
  . -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋃ (i : I), B i
    intro hx
    -- hx : x ∈ ⋃ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, f x ∈ B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, x ∈ f ⁻¹' B i
    cases' hx with i xBi
    -- i : I
    -- xBi : x ∈ f ⁻¹' B i
    use i
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at xBi
    -- xBi : f x ∈ B i
    exact xBi

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_iUnion

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by  simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra mediante la siguiente cadena de equivalencias
--    x ∈ f⁻¹[⋂ᵢ Bᵢ] ↔ f x ∈ ⋂ᵢ Bᵢ
--                   ↔ (∀ i) f(x) ∈ Bᵢ
--                   ↔ (∀ i) x ∈ f⁻¹[Bᵢ]
--                   ↔ x ∈ ⋂ᵢ f⁻¹[Bᵢ]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  calc  (x ∈ f ⁻¹' ⋂ i, B i)
     ↔ f x ∈ ⋂ i, B i       := mem_preimage
   _ ↔ (∀ i, f x ∈ B i)     := mem_iInter
   _ ↔ (∀ i, x ∈ f ⁻¹' B i) := iff_of_eq rfl
   _ ↔ x ∈ ⋂ i, f ⁻¹' B i   := mem_iInter.symm

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i → x ∈ ⋂ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋂ (i : I), B i
    -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ f ⁻¹' B i
    intro i
    -- i : I
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_preimage]
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋂ (i : I), B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), f x ∈ B i
    exact hx i
  . -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋂ (i : I), B i
    intro hx
    -- hx : x ∈ ⋂ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋂ (i : I), B i
    rw [mem_iInter]
    -- ⊢ ∀ (i : I), f x ∈ B i
    intro i
    -- i : I
    -- ⊢ f x ∈ B i
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), x ∈ f ⁻¹' B i
    exact hx i

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  simp

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext ; simp }

-- Lemas usados
-- ============

variable (A : I → Set α)
variable (a b : Prop)
variable (i : I)
variable (s : Set α)
variable (v : Set β)
variable (x : α)
variable (y : β)
#check (iff_of_eq : a = b → (a ↔ b))
#check (image_iInter_subset A f : f '' ⋂ i, A i ⊆ ⋂ i, f '' A i)
#check (image_iUnion : f '' ⋃ i, A i = ⋃ i, f '' A i)
#check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
#check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
#check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
#check (mem_iUnion_of_mem i : x ∈ A i → x ∈ ⋃ i, A i)
#check (mem_image f s y : (y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y))
#check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
#check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
#check (preimage_iUnion : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i))
