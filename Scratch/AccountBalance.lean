module

import Mathlib

namespace aosd.account_balance

section Definition

-- An account
structure Account where
  balance:ℕ
  deriving Repr

-- Withdrawal Result
inductive WithdrawalResult where
  | Success(amount:ℕ)
  | InsufficientFunds
  deriving Repr

-- Withdraw function
def withdraw (account:Account) (amount:ℕ)
  : (Account × WithdrawalResult) :=
    if amount > account.balance
    then (account, WithdrawalResult.InsufficientFunds)
    else ({account with balance := account.balance - amount}, WithdrawalResult.Success amount)

-- Example usage
def result:(Account × WithdrawalResult) := withdraw {balance := 10} 100
#eval withdraw {balance := 100} 10

end Definition

section Proofs

-- Theorem stating that the balance is updated correctly in all cases
example
(acc : Account)
(amt : ℕ)
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
  (amt : ℕ)
  :
    (withdraw acc amt).1.balance ≥ 0 := by
  dsimp [withdraw]
  split_ifs with h_gt
  · -- Case 1: amount > acc.balance (Insufficient funds, balance unchanged)
    omega
  · -- Case 2: amount ≤ acc.balance (Successful withdrawal)
    -- h_gt is `¬ amt > acc.balance`, which means `amt ≤ acc.balance`
    push Not at h_gt
    linarith

-- Theorem: Withdrawing 0 leaves the account balance unchanged
example
  (acc : Account):
    (withdraw acc 0).1.balance = acc.balance := by
  dsimp [withdraw]


-- Theorem: Withdrawing all leaves the account balance 0
example
  (acc : Account) :
    (withdraw acc acc.balance).1.balance = 0 := by
  dsimp [withdraw]
  split_ifs with h_gt
  · -- Case 1: 0 > acc.balance. This contradicts h2 (acc.balance ≥ 0).
    linarith
  · -- Case 2: ¬ (0 > acc.balance). The balance becomes acc.balance - 0.
    simp

end Proofs
