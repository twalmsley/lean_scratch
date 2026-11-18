import Mathlib

namespace aosd.ShoppingBasket

section Definitions

-- Define the type for rational numbers between 0 and 100 (inclusive)
def Rat0TO100 : Type := { x : ℚ // 0 ≤ x ∧ x ≤ 100 }
  deriving Repr

structure ShoppingBasketItem where
  item : String
  unitPrice : ℚ≥0
  quantity : ℚ≥0
  discountPercent : Rat0TO100 -- 0 to 100

def basketTotal (basket : List ShoppingBasketItem) : ℚ :=
  basket.foldl (fun acc item => acc + item.unitPrice.val * item.quantity.val * (100 - item.discountPercent.val) / 100) 0

end Definitions

section Examples
#eval basketTotal [{ item := "Apple", unitPrice := 20 , quantity := 3 , discountPercent := ⟨ 10, by norm_num ⟩ },
                   { item := "Banana", unitPrice := 30 , quantity := 5 , discountPercent := ⟨ 5, by norm_num ⟩ },
                   { item := "Orange", unitPrice := 15 , quantity := 2 , discountPercent := ⟨ 15, by norm_num ⟩ }]
end Examples

section Proofs

-- Empty basket should have a total of 0
theorem emptyBasketTotal : basketTotal [] = 0 := by
  simp [basketTotal]

-- Adding an item with 0 quantity should not change the total
theorem zeroQuantityItemDoesNotChangeTotal
(item : ShoppingBasketItem)
(h : item.quantity = 0 ) :
    basketTotal [item] = 0 := by
  simp [basketTotal, h]

-- The total should be non-negative
theorem totalNonNegative
{item1 item2 : ShoppingBasketItem}
(h1: (item1 : ShoppingBasketItem) = { item := "Test", unitPrice := 10 , quantity := 1 , discountPercent := ⟨ 100, by norm_num ⟩  })
(h2: (item2 : ShoppingBasketItem) = { item := "Test2", unitPrice := 20 , quantity := 2 , discountPercent := ⟨ 100, by norm_num ⟩  })
:
  basketTotal [item1, item2] ≥ 0 := by
  rw [h1, h2]
  simp [basketTotal]

-- Increasing the quantity of an item should not decrease the total
theorem increasingQuantityIncreasesTotal
(item : ShoppingBasketItem)
(h1 : item.quantity = 1 )
(h2 : item.unitPrice = 1 )
(h3: item.discountPercent = ⟨ 0, by norm_num ⟩ ) :
  basketTotal [item] ≤ basketTotal [{ item := item.item, unitPrice := item.unitPrice, quantity := ⟨ item.quantity.val + 1, by rw [h1];simp ⟩ , discountPercent := item.discountPercent }] := by
  simp [basketTotal, h1, h2, h3]

-- Reordering the items does not change the total basket price
theorem orderDoesNotMatter :
∀ (item1 item2 : ShoppingBasketItem), basketTotal [item1, item2] = basketTotal [item2, item1] := by
  simp [basketTotal]
  intro item1 item2
  linarith

end Proofs

end aosd.ShoppingBasket
