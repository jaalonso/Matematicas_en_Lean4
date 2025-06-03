-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si s es una sucesión convergente y el límite de
-- t es 0, entonces el límite de s * t es 0.
-- ----------------------------------------------------------------------

import src.Logica.Acotacion_de_convergentes

variable {s t : ℕ → ℝ}
variable {a : ℝ}

lemma aux_l1
  (B ε : ℝ)
  (εpos : ε > 0)
  (Bpos : 0 < B)
  (pos0 : ε / B > 0)
  (n : ℕ)
  (h0 : |s n| < B)
  (h1 : |t n - 0| < ε / B)
  : |s n| * |t n - 0| < ε :=
by
  by_cases h3 : s n = 0
  . -- h3 : s n = 0
    calc |s n| * |t n - 0|
             = |0| * |t n - 0|  := by rw [h3]
           _ = 0 * |t n - 0|    := by rw [abs_zero]
           _ = 0                := by exact zero_mul (abs (t n - 0))
           _ < ε                := by exact εpos
  . -- h3 : ¬s n = 0
    have h4 : |s n| > 0 :=
      by exact abs_pos.mpr h3
    clear h3
    have h5 : |s n| * |t n - 0| < |s n| * (ε / B) :=
      by exact mul_lt_mul_of_pos_left h1 h4
    have h6 : |s n| * (ε / B) < B * (ε / B) :=
      by exact mul_lt_mul_of_pos_right h0 pos0
    have h7 : B ≠ 0 :=
      by exact ne_of_gt Bpos
    have h8 : B * (ε / B) = ε :=
      calc B * (ε / B) = (B * B⁻¹) * ε := by ring
                     _ = 1 * ε         := by rw [Field.mul_inv_cancel B h7]
                     _ = ε             := by exact one_mul ε
    have h9 : |s n| * |t n - 0| < B * (ε / B) :=
      by exact lt_trans h5 h6
    rw [h8] at h9
    assumption


lemma aux
  (cs : limite s a)
  (ct : limite t 0)
  : limite (fun n ↦ s n * t n) 0 :=
by
  intros ε εpos
  -- ε : ℝ
  -- εpos : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => s n * t n) n - 0| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |s n * t n - 0| < ε
  rcases convergentes_acotadas cs with ⟨N₀, B, h₀⟩
  -- N₀ : ℕ
  -- B : ℝ
  -- h₀ : ∀ n ≥ N₀, |s n| ≤ B
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intros n hn
  have hn0 : n ≥ N₀ := by
    exact le_of_max_le_left hn
  specialize h₀ n hn0
  have hn1 : n ≥ N₁ := by
    exact le_of_max_le_right hn
  specialize h₁ n hn1
  clear cs ct hn hn0 hn1 N₀ N₁
  calc
    |s n * t n - 0|
        = |s n * (t n - 0)|
          := by { congr; ring }
      _ = |s n| * |t n - 0|
          := by exact abs_mul (s n) (t n - 0)
      _ < ε
          := by exact aux_l1 B ε εpos Bpos pos₀ n h₀ h₁

-- Lemas usados
-- ============

variable (b c : ℝ)
#check (Field.mul_inv_cancel a : a ≠ 0 → a * a⁻¹ = 1)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_nonneg a : 0 ≤ |a|)
#check (abs_pos : 0 < |a| ↔ a ≠ 0)
#check (abs_zero : |(0 : ℝ)| = 0)
#check (div_pos : 0 < a → 0 < b → 0 < a / b)
#check (le_of_max_le_left : max a b ≤ c → a ≤ c)
#check (le_of_max_le_right : max a b ≤ c → b ≤ c)
#check (le_refl a : a ≤ a)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_trans : a < b → b < c → a < c)
#check (mul_lt_mul_of_pos_left : b < c → 0 < a → a * b < a * c)
#check (mul_lt_mul_of_pos_right : b < c → 0 < a → b * a < c * a)
#check (ne_of_gt : b < a → a ≠ b)
#check (one_mul a : 1 * a = a)
#check (zero_mul a : 0 * a = 0)
