import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

set_option linter.style.whitespace false

theorem th (h : 2 = 2)
  : 2 = 2 := by
    exact h

theorem th2
  : 2 = 2 := by
    norm_num

theorem plus_comm
  : ∀ (a b : Nat), a + b = b + a := by
    intro a b
    have h := Nat.add_comm a b
    exact h

theorem plus_comm'
  : ∀ (a b: Nat), a + b = b + a := by
    intro a b
    have h := Nat.add_comm a b
    exact h

example (a b : Nat) (h : a = b)
  : a + 1 = b + 1 := by
    rw [h]

theorem plus_assoc
  : ∀ (a b c : Nat), a + (b + c) = (a + b) + c := by
  intro a b c
  have h := Nat.add_assoc a b c
  rw [h]

theorem alg1
  : ∀ (a b c : Nat), a * (b + c) = (c + b) * a:= by
    intro a b c
    have h1 : b + c = c + b := by
      have g := Nat.add_comm b c
      exact g
    rw [← h1]
    --
    set d := b + c
    have h2 : a * d = d * a := by
      have g := Nat.mul_comm a d
      exact g
    rw [← h2]

theorem alg10
  : ∀ (a b c : Nat), a * (b + c) = (c + b) * a := by
    intro a b c
    have h1 : b + c = c + b := by
      have g := Nat.add_comm b c
      exact g
    rw [h1]
    --
    set d := c + b
    have h2 : a * d = d * a := by
      have g := Nat.mul_comm a d
      exact g
    rw [h2]


theorem alg1'
  : ∀ (a b c : Nat), a * (b + c) = (c + b) * a:= by
    intro a b c
    rw [Nat.add_comm b c]
    rw [Nat.mul_comm]

theorem alg2
  : ∀ (a b c d : Nat),
      (c + d)^2 + (a + b)^2 =  a^2 + b^2 + c^2 + d^2 + 2*a*b + 2*c*d := by
      intro a b c d
      ring

theorem ev10
  : Even 10 := by
    unfold Even
    use 5

theorem two_div_even
  : ∀ n : Nat, Even n → 2 ∣ n := by
    intro n h
    unfold Even at h
    obtain ⟨r, hr⟩ := h
    have n_eq_2r : n = 2 * r := by
      rw [hr]
      ring
    rw [n_eq_2r]
    simp

-- Proof that 10 is even
#check ev10
-- Proof that 2 divides 10 if 10 is even
#check two_div_even 10
-- Proof that 2 divides 10
#check two_div_even 10 ev10

def PrimeNum (n : Nat) : Prop :=
  n ≥ 2 ∧ (∀ m : Nat, m ∣ n → (m = 1 ∨ m = n))

theorem not_prime_1
  : ¬ PrimeNum 1 := by
    intro h
    unfold PrimeNum at h
    obtain ⟨hₗ, hᵣ⟩ := h
    contradiction

theorem not_prime_9
  : ¬ PrimeNum 9 := by
    intro h
    unfold PrimeNum at h
    obtain ⟨hl, hr⟩ := h
    have div₉ : 3 ∣ 9 := by
      norm_num
    have hr₃ := hr 3
    have or_cases := hr₃ div₉
    rcases or_cases with c1 | c2
    · contradiction
    · contradiction

theorem not_prime_9'
  : ¬ PrimeNum 9 := by
    intro h
    unfold PrimeNum at h
    obtain ⟨hl, hr⟩ := h
    have div : 3 ∣ 9 := by norm_num
    have hr_3 := hr 3
    have or_cases := hr_3 div
    rcases or_cases with c1 | c2
    · contradiction
    · contradiction

-- #check Nat.eq_zero_of_dvd_of_lt

theorem prime_5 : PrimeNum 5 := by
  unfold PrimeNum
  have h₁ : 5 ≥ 2 := by
    norm_num
  have h₂ : ∀ (m : Nat), m ∣ 5 → m = 1 ∨ m = 5 := by
    intro m h₃
    match m with
    | 0 => contradiction
    | 1 =>
      have h : 1 = 1 := by norm_num
      exact Or.inl h
    | 2 => contradiction
    | 3 => contradiction
    | 4 => contradiction
    | 5 =>
      have h : 5 = 5 := by norm_num
      exact Or.inr h
    | n + 6 =>
      have g₁ : 5 < n + 6 := by norm_num
      have g₂ := Nat.eq_zero_of_dvd_of_lt h₃ g₁
      contradiction
  exact ⟨h₁, h₂⟩

#check Classical.em
#check irrational_sqrt_two
#check Real.rpow_mul

theorem exists_irrat_pow_irrat_rat'
  : ∃ (x y : ℝ),
    Irrational x ∧ Irrational y ∧
      ¬ (Irrational (x ^ y)) := by
    have em := Classical.em (Irrational (√2 ^ √2))
    rcases em with hl | hr
    · use √2 ^ √2, √2
      have eq : (√2^√2)^√2 = 2 := by
        calc
          (√2^√2)^√2 = √2^(√2 * √2) := by
            have nonneg_sqrt2 : 0 ≤ √2 := by simp
            have h := Real.rpow_mul nonneg_sqrt2 √2 √2
            rw [h]
          _ = √2^(2) := by simp
          _ = 2 := by simp
      have rat : ¬ Irrational ((√2^√2)^√2) := by
        rw [eq]
        simp
      have irrat : Irrational √2 := by
        exact irrational_sqrt_two
      exact ⟨hl, irrat, rat⟩
    · use √2, √2
      have irrat : Irrational √2 := by
        exact irrational_sqrt_two
      exact ⟨irrat, irrat, hr⟩

#check Nat.exists_prime_and_dvd
#check Nat.factorial_pos
#check Classical.byContradiction
#check Nat.dvd_factorial
#check Nat.dvd_add_right
#check Nat.Prime.two_le
#check Nat.eq_zero_of_dvd_of_lt

theorem primes_infinite'
  : ∀ n, ∃ p, Nat.Prime p ∧ p > n := by
    intro n
    have not1 : n.factorial + 1 ≠ 1 := by
      have h := Nat.factorial_pos n
      linarith
    have p_exists := Nat.exists_prime_and_dvd not1
    obtain ⟨p, p_prime, p_dvd_nfp1⟩ := p_exists
    use p
    have plen_false : ¬ (p > n) → False := by
      intro plen
      push_neg at plen
      have pgt1 : 1 < p := by
        have h := Nat.Prime.two_le p_prime
        linarith
      have pgt0 : 0 < p := by
        linarith
      have p_dvd_nf : p ∣ n.factorial := by
        have h := Nat.dvd_factorial pgt0 plen
        exact h
      have p_dvd_1 : p ∣ 1 := by
        obtain ⟨hl,hr⟩ := Nat.dvd_add_right p_dvd_nf
        have h := hl p_dvd_nfp1
        exact h
      have f : 1 = 0 := by
        have h := Nat.eq_zero_of_dvd_of_lt p_dvd_1 pgt1
        exact h
      contradiction
    have pgtn : p > n := by
      have h := Classical.byContradiction plen_false
      exact h
    exact ⟨p_prime, pgtn⟩
