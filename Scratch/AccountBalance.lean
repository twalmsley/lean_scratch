module

import Mathlib

namespace aosd.account_balance

section Definition

-- An account
structure Account where
  balance: ℚ≥0

-- Withdrawal Result
inductive WithdrawalResult where
  | Success(amount:ℚ≥0)
  | InsufficientFunds

-- Withdraw function
def withdraw (account:Account) (amount:ℚ≥0)
  : (Account × WithdrawalResult) :=
    if amount > account.balance
    then (account, WithdrawalResult.InsufficientFunds)
    else ({account with balance := account.balance - amount}, WithdrawalResult.Success amount)

-- Example usage
def result:(Account × WithdrawalResult) := withdraw {balance := 10} 100

end Definition

section Proofs

-- Theorem stating that the balance is updated correctly in all cases
example
(acc : Account)
(amt : ℚ≥0)
:
    (withdraw acc amt).1.balance =
      if amt > acc.balance then acc.balance else acc.balance - amt := by
  dsimp [withdraw]
  split_ifs
  rfl
  rfl


-- Theorem: A withdrawal never results in a negative balance
example
  (acc : Account)
  (amt : ℚ≥0)
  :
    (withdraw acc amt).1.balance ≥ 0 := by
  dsimp [withdraw]
  split_ifs with h_gt
  · -- Case 1: amount > acc.balance (Insufficient funds, balance unchanged)
    norm_num
  · -- Case 2: amount ≤ acc.balance (Successful withdrawal)
    -- h_gt is `¬ amt > acc.balance`, which means `amt ≤ acc.balance`
    push Not at h_gt
    norm_num

-- Theorem: Withdrawing 0 leaves the account balance unchanged
example
  (acc : Account):
    (withdraw acc 0).1.balance = acc.balance := by
  dsimp [withdraw]
  split
  norm_num
  norm_num


-- Theorem: Withdrawing all leaves the account balance 0
example
  (acc : Account) :
    (withdraw acc acc.balance).1.balance = 0 := by
  dsimp [withdraw]
  norm_num

end Proofs
