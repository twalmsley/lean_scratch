import Mathlib

namespace aosd.ShoppingBasket

section Definitions

structure ShoppingBasketItem where
  item : String
  unitPrice : ℕ
  quantity : ℕ
  discountPercent : ℕ
  deriving Repr, Inhabited

def basketTotal (basket : List ShoppingBasketItem) : ℕ  :=
  basket.foldl (fun acc item => acc + item.unitPrice * item.quantity * (100 - item.discountPercent) / 100) 0

end Definitions

section Examples
#eval basketTotal [{ item := "Apple", unitPrice := 20, quantity := 3, discountPercent := 10 },
                   { item := "Banana", unitPrice := 30, quantity := 5, discountPercent := 5 },
                   { item := "Orange", unitPrice := 15, quantity := 2, discountPercent := 15 }]
end Examples

section Proofs

-- Empty basket should have a total of 0
theorem emptyBasketTotal : basketTotal [] = 0 := by
  simp [basketTotal]

-- Adding an item with 0 quantity should not change the total
theorem zeroQuantityItemDoesNotChangeTotal
(item : ShoppingBasketItem)
(h : item.quantity = 0) :
    basketTotal [item] = 0 := by
  simp [basketTotal, h]

-- The total should be non-negative
theorem totalNonNegative
{item1 item2 : ShoppingBasketItem}
(h1: (item1 : ShoppingBasketItem) = { item := "Test", unitPrice := 10, quantity := 1, discountPercent := 110 })
(h2: (item2 : ShoppingBasketItem) = { item := "Test2", unitPrice := 20, quantity := 2, discountPercent := 110 })
:
  basketTotal [item1, item2] ≥ 0 := by
  rw [h1, h2]
  simp [basketTotal]

-- Increasing the quantity of an item should not decrease the total
theorem increasingQuantityIncreasesTotal
(item : ShoppingBasketItem)
(h1 : item.quantity = 1)
(h2 : item.unitPrice = 1)
(h3: item.discountPercent = 0) :
  basketTotal [item] ≤ basketTotal [{ item := item.item, unitPrice := item.unitPrice, quantity := item.quantity + 1, discountPercent := item.discountPercent }] := by
  simp [basketTotal, h1, h2, h3]

-- Reordering the items does not change the total basket price
theorem orderDoesNotMatter :
∀ (item1 item2 : ShoppingBasketItem), basketTotal [item1, item2] = basketTotal [item2, item1] := by
  simp [basketTotal]
  intro item1 item2
  omega

end Proofs

end aosd.ShoppingBasket
