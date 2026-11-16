module

import Mathlib

namespace aosd.apply_discount

section Definition

-- Discount function
def apply_discount (price discount : ℚ)
  (_:0 ≤ discount ∧ discount ≤ 1)
  (_:price ≥ 0):ℚ
  := price - price * discount

-- Example usage
def p:ℚ := 100
def d:ℚ := 0.1
def dp:ℚ := apply_discount p d (by rw [d];norm_num) (by rw [p];norm_num)
def dp2:ℚ := apply_discount 100 0.1 (by norm_num) (by norm_num)

end Definition


section Proofs

-- The discounted price is always positive
example
  {dp p d:ℚ}
  (h1: 0 ≤ d ∧ d ≤ 1)
  (h2: p ≥ 0)
  (h3:dp = apply_discount p d h1 h2):
  0 ≤ dp := by
  unfold apply_discount at h3
  nlinarith

-- The discounted price is always <= the original price
example
  {dp p d:ℚ}
  (h1: 0 ≤ d ∧ d ≤ 1)
  (h2: p ≥ 0)
  (h3:dp = apply_discount p d h1 h2):
  p ≥ dp := by
  unfold apply_discount at h3
  rcases h1 with ⟨hd_ge, hd_le⟩
  have h_mul : 0 ≤ p * d := mul_nonneg h2 hd_ge
  linarith

-- The discounted price equals the price for a discount of 0
example
  (h1: 0 ≤ 0 ∧ 0 ≤ 1)
  (h2: p ≥ 0)
  : p = apply_discount p 0 h1 h2 := by
  dsimp [apply_discount]
  linarith

-- The discounted price is 0 for 100% discount
example
  (h1: 0 ≤ 1 ∧ 1 ≤ 1)
  (h2: p ≥ 0)
  : 0 = apply_discount p 1 h1 h2 := by
  dsimp [apply_discount]
  linarith

end Proofs
