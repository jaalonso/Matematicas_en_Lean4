-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el límite de la suma de dos sucesiones
-- convergentes es la suma de los límites.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos los siguientes lemas
--    (∀ a ∈ ℝ)[a > 0 → a / 2 > 0]                                   (L1)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → a ≤ c]                         (L2)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → b ≤ c]                         (L3)
--    (∀ a, b ∈ ℝ)[|a + b| ≤ |a| + |b|]                              (L4)
--    (∀ a ∈ ℝ)[a / 2 + a / 2 = a]                                   (L5)
--
-- Tenemos que probar que si s es una sucesión con límite a y t otra con
-- límite , entonces el límite de s + t es a+b; es decir, que para todo
-- ε ∈ ℝ, si
--    ε > 0                                                          (1)
-- entonces
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |(s + t)(n) - (a + b)| < ε]           (2)
--
-- Por (1) y el lema L1, se tiene que
--    ε/2 > 0                                                        (3)
-- Por (3) y porque el límite de s es a, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |s(n) - a| < ε/2]
-- Sea N₁ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₁ → |s(n) - a| < ε/2]                            (4)
-- Por (3) y porque el límite de t es b, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |t(n) - b| < ε/2]
-- Sea N₂ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₂ → |t(n) - b| < ε/2]                            (5)
-- Sea N = max(N₁, N₂). Veamos que verifica la condición (1). Para ello,
-- sea n ∈ ℕ tal que n ≥ N. Entonces, n ≥ N₁ (por L2) y n ≥ N₂ (por
-- L3). Por tanto, por las propiedades (4) y (5) se tiene que
--    |s(n) - a| < ε/2                                               (6)
--    |t(n) - b| < ε/2                                               (7)
-- Finalmente,
--    |(s + t)(n) - (a + b)| = |(s(n) + t(n)) - (a + b)|
--                           = |(s(n) - a) + (t(n) - b)|
--                           ≤ |s(n) - a| + |t(n) - b|      [por L4]
--                           < ε / 2 + ε / 2                [por (6) y (7)
--                           = ε                            [por L5]

-- Demostraciones con Lean4
-- ========================

import src.Logica.Definicion_de_convergencia

variable {s t : ℕ → ℝ} {a b c : ℝ}

lemma ConvergesTo_add
  (cs : ConvergesTo s a)
  (ct : ConvergesTo t b)
  : ConvergesTo (s + t) (a + b) :=
by
  intros ε εpos
  -- ε : ℝ
  -- εpos : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(s + t) n - (a + b)| < ε
  have ε2pos : 0 < ε / 2 := half_pos εpos
  cases' cs (ε / 2) ε2pos with Ns hs
  -- Ns : ℕ
  -- hs : ∀ (n : ℕ), n ≥ Ns → |s n - a| < ε / 2
  cases' ct (ε / 2) ε2pos with Nt ht
  -- Nt : ℕ
  -- ht : ∀ (n : ℕ), n ≥ Nt → |t n - b| < ε / 2
  clear cs ct ε2pos εpos
  let N := max Ns Nt
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(s + t) n - (a + b)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have nNs : n ≥ Ns := le_of_max_le_left hn
  specialize hs n nNs
  -- hs : |s n - a| < ε / 2
  have nNt : n ≥ Nt := le_of_max_le_right hn
  specialize ht n nNt
  -- ht : |t n - b| < ε / 2
  clear hn nNs nNt
  calc |(s + t) n - (a + b)|
       = |s n + t n - (a + b)|    := rfl
     _ = |(s n - a) + (t n -  b)| := by { congr; ring }
     _ ≤ |s n - a| + |t n -  b|   := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith [hs, ht]
     _ = ε                        := by apply add_halves

-- Lemas usados
-- ============

-- #check (half_pos : a > 0 → a / 2 > 0)
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_halves a : a / 2 + a / 2 = a)
