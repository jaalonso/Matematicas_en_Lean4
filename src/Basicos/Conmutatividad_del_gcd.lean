-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    gcd m n = gcd n m
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia del siguiente lema auxiliar
--    (∀ x, y ∈ ℕ)[gcd(x,y) ∣ gcd(y,x)]                               (1)
-- En efecto, sustituyendo en (1) x por m e y por n, se tiene
--    gcd(m, n) ∣ gcd(n, m)                                           (2)
-- y sustituyendo en (1) x por n e y por m, se tiene
--    gcd(n, m) ∣ gcd(m, n)                                           (3)
-- Finalmente, aplicando la propiedad antisimétrica de la divisibilidad
-- a (2) y (3), se tiene
--    gcd(m, n) = gcd(n, m)
--
-- Para demostrar (1), por la definición del máximo común divisor, basta
-- demostrar las siguientes relaciones
--    gcd m n ∣ n
--    gcd m n ∣ m
-- y ambas se tienen por la definición del máximo común divisor.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (k m n : ℕ)

open Nat

-- 1ª demostración del lema auxiliar
lemma aux : gcd m n ∣ gcd n m :=
by
  have h1 : gcd m n ∣ n :=
    gcd_dvd_right m n
  have h2 : gcd m n ∣ m :=
    gcd_dvd_left m n
  show gcd m n ∣ gcd n m
  exact dvd_gcd h1 h2

-- 2ª demostración del lema auxiliar
example : gcd m n ∣ gcd n m :=
dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)

-- 1ª demostración
example : gcd m n = gcd n m :=
by
  have h1 : gcd m n ∣ gcd n m := aux m n
  have h2 : gcd n m ∣ gcd m n := aux n m
  show gcd m n = gcd n m
  exact _root_.dvd_antisymm h1 h2

-- 2ª demostración
example : gcd m n = gcd n m :=
by
  apply _root_.dvd_antisymm
  . -- ⊢ gcd m n ∣ gcd n m
    exact aux m n
  . -- ⊢ gcd n m ∣ gcd m n
    exact aux n m

-- 3ª demostración
example : gcd m n = gcd n m :=
_root_.dvd_antisymm (aux m n) (aux n m)

-- 4ª demostración
example : gcd m n = gcd n m :=
-- by apply?
gcd_comm m n

-- Lemas usados
-- ============

-- #check (_root_.dvd_antisymm : m ∣ n → n ∣ m → m = n)
-- #check (dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n)
-- #check (gcd_comm m n : gcd m n = gcd n m)
-- #check (gcd_dvd_left  m n: gcd m n ∣ m)
-- #check (gcd_dvd_right m n : gcd m n ∣ n)
