/-! Computable (Float) version of the model in Capital.lean, for `#eval` demos.
`Real` is noncomputable, so it cannot be evaluated; Float is used instead.
Float rounding means borderline cases (balance exactly 0, or exactly constant)
can print tiny errors such as 999.9999999999999. -/

/-- Balance after `n` years: grow by `I`, then withdraw `D`. -/
def balanceF (C I D : Float) : Nat → Float
  | 0 => C
  | n + 1 => balanceF C I D n * (1 + I) - D

/-- Balances for years 0 … N. -/
def trajectory (C I D : Float) (N : Nat) : List Float :=
  (List.range (N + 1)).map (balanceF C I D)

/-- True iff the balance is non-negative in every year 0 … N. -/
def staysNonneg (C I D : Float) (N : Nat) : Bool :=
  (trajectory C I D N).all (fun x => x >= 0.0)

/-- First year in 0 … N where the balance is negative, if any. -/
def firstNegativeYear (C I D : Float) (N : Nat) : Option Nat :=
  (List.range (N + 1)).find? (fun n => balanceF C I D n < 0.0)

/-- Closed form (I > 0): D/I + (C - D/I) * (1+I)^n. -/
def balanceClosed (C I D : Float) (n : Nat) : Float :=
  D / I + (C - D / I) * Float.pow (1 + I) n.toFloat

/-- Exact test from `balance_nonneg_iff`: D*((1+I)^N - 1) ≤ C*I*(1+I)^N. -/
def exactTest (C I D : Float) (N : Nat) : Bool :=
  let g := Float.pow (1 + I) N.toFloat
  D * (g - 1) <= C * I * g

/-! ## 1. Interest covers the withdrawal (D ≤ C·I): balance never falls -/

-- C = 1000, I = 5 %, D = 40 < 50: balance grows every year
#eval trajectory 1000 0.05 40 10
#eval staysNonneg 1000 0.05 40 50          -- true

-- D = C·I = 50: balance is constant at 1000 (up to float rounding)
#eval trajectory 1000 0.05 50 5
#eval staysNonneg 1000 0.05 50 50          -- true (modulo rounding)

/-! ## 2. Withdrawal exceeds interest (D > C·I): balance declines, runs out -/

-- C = 1000, I = 5 %, D = 100: closed form 2000 - 1000·1.05^n
#eval trajectory 1000 0.05 100 16
#eval firstNegativeYear 1000 0.05 100 30   -- some 15
#eval staysNonneg 1000 0.05 100 14         -- true
#eval staysNonneg 1000 0.05 100 15         -- false

/-! ## 3. Zero interest: balance is C - n·D (finite-horizon result, N·D ≤ C) -/

#eval trajectory 1000 0.0 100 10           -- ends at exactly 0
#eval staysNonneg 1000 0.0 100 10          -- true  (10·100 ≤ 1000)
#eval staysNonneg 1000 0.0 100 11          -- false (11·100 > 1000)

/-! ## 4. Higher rate buys more years for the same withdrawal -/

#eval firstNegativeYear 1000 0.02 100 60   -- low rate: runs out sooner
#eval firstNegativeYear 1000 0.08 100 60   -- 8 % = 80 < 100 but runs out later
#eval firstNegativeYear 1000 0.10 100 60   -- D = C·I: never (none)

/-! ## 5. Closed form agrees with the recursion -/

#eval (List.range 6).map (balanceClosed 1000 0.05 100)
#eval trajectory 1000 0.05 100 5

/-! ## 6. Exact test (balance_nonneg_iff) matches the simulation -/

#eval exactTest 1000 0.05 100 14           -- true
#eval exactTest 1000 0.05 100 15           -- false
#eval (List.range 20).map fun N =>
  (N, staysNonneg 1000 0.05 100 N, exactTest 1000 0.05 100 N)

/-! ## 7. Sweep: how many years does C = 1000 last for various D at 5 %? -/

#eval [20, 40, 50, 60, 80, 100, 150, 200].map fun D =>
  (D, firstNegativeYear 1000 0.05 D.toFloat 100)

#eval trajectory 720000 0.05 50000 30
#eval firstNegativeYear 720000 0.05 50000 30   -- some 15
#eval staysNonneg 720000 0.05 50000 26         -- true
#eval staysNonneg 720000 0.05 50000 27         -- false
