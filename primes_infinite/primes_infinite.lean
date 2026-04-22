import Mathlib

theorem primes_infinite
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
