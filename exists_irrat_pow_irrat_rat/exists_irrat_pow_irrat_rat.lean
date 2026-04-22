import Mathlib

theorem exists_irrat_pow_irrat_rat
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
      --
      have rat : ¬ Irrational ((√2^√2)^√2) := by
        rw [eq]
        simp
      have irrat : Irrational √2 := by
        exact irrational_sqrt_two
      exact ⟨hl, irrat, rat⟩
    --
    · use √2, √2
      have irrat : Irrational √2 := by
        exact irrational_sqrt_two
      exact ⟨irrat, irrat, hr⟩
