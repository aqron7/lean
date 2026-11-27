import Mathlib
example (a b : ℤ) (h1 : -1 ≤ a ^ 2 + a * b - b ^ 2) (h1' : a ^ 2 + a * b - b ^ 2 ≤ 1)
    (h2 : -2 ≤ 4 - 4 * a - 2 * b) (h2' : 4 - 4 * a - 2 * b ≤ 2) : a ≤ 3 ∧ -2 ≤ a := by
  constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (2 * a + b - 2)]
