import Mathlib.Data.Set.Basic

-- This is a trivial proof to check if Mathlib is loaded
example (A : Set ℕ) : A ⊆ A := by
  intro x h
  exact h

#eval 1+1
