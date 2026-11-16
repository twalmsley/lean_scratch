module

import Mathlib

namespace aosd.reserve_stock

section Definition
-- Reserve some stock, maybe
def reserve
  (available requested : ℕ )
    :Option ℕ :=
    if available >= requested
    then some (available - requested)
    else none

-- Examle usage
def result:Option ℕ := reserve 100 10
-- #eval reserve 1 0
-- #eval reserve 1 1
-- #eval reserve 1 2
-- #eval reserve 0 0
-- #eval reserve 0 1

end Definition

section Proofs

example
  {available requested remaining : ℕ }
  (h1: available ≥ requested)
  (h2: some remaining = reserve available requested)
  :
  available = remaining + requested := by
  dsimp [reserve] at h2
  split_ifs at h2
  norm_num at h2
  rw [h2]
  omega

example
  {available requested : ℕ }
  (h1: available ≥ requested)
  :
  (0:ℕ) ≤ reserve available requested
  := by
  dsimp [reserve]
  split_ifs
  norm_num


example
  {available requested : ℕ }
  (h1: available < requested)
  :
  none = reserve available requested
  := by
  dsimp [reserve]
  split_ifs
  linarith
  rfl

end Proofs
