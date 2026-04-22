import mathlib

example (a b : Nat) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  --
  have h1 : (a + b) ^ 2 = (a + b) * (a + b) := by
    rw [pow_two]
  rw [h1]
  --
  have h2 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
    rw [Nat.mul_add]
    rw [Nat.mul_comm (a + b) a]
    rw [Nat.mul_comm (a + b) b]
  rw [h2]
  --
  have h3 : a * (a + b) = a^2 + a * b := by
    rw [Nat.mul_add]
    rw [pow_two]
  rw [h3]
  --
  have h4 : b * (a + b) = a * b + b^2 := by
    rw [Nat.mul_add]
    rw [← Nat.mul_comm a b]
    rw [← pow_two b]
  rw [h4]
  --
  simp only [← Nat.add_assoc]
  norm_num
  have h : a * b + a * b = 2 * (a * b) := by
    rw [← Nat.mul_two (a * b), Nat.mul_comm]
  --
  simp only [Nat.add_assoc]
  rw [h]
  simp only [Nat.mul_assoc]


example (a b : Nat) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  ring
