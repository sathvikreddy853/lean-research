import Mathlib
open Finset

#check 5          -- 5 : ℕ
#check true       -- true : Bool
#check (5 : ℤ)    -- 5 : ℤ
#eval 2 + 2       -- 4

def double (n : ℕ) : ℕ := 2 * n
#eval double 7    -- 14

example : 2 + 2 = 4 := by
  rfl
-- rfl means "reflexivity" — both sides compute to the same thing


example (n : ℕ) : n + 0 = n := by
  simp        -- simplifier, knows basic arithmetic facts

example (a b : ℕ) (h : a = b) : b = a := by
  exact h.symm   -- h.symm flips an equality

-- Exercices

-- Prove that 3 * 4 = 12
example : 3 * 4 = 12 := by
  simp

example : 3 * 4 = 12 := by
  norm_num

example : 3 * 4 = 12 := by
  rfl

example : (5 : ℕ) ≤ 10 := by
  trivial

example (n : ℕ) (h : n = 7) : n + 1 = 8 := by
  rw [h]

example (n m : ℕ) (h : n ≤ m) : n ≤ m + 5 := by
  omega
