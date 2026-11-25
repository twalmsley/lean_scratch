# scratch

A collection of Lean 4 examples and exercises exploring type-safe domain modelling, functional data structures, numerical simulations, and formal proofs (using `Mathlib`).

## Root Files

- **`Scratch.lean`** — Root module of the `Scratch` library; imports all modules in `Scratch/`.
- **`Main.lean`** — Entry point (`main : IO Unit`) that imports `Scratch` and `Scratch.Basic` and prints `"Hello, world!"`.

## `Scratch/` Modules

### Data Structures & Systems

- **`Scratch/LRUCache.lean`** — Purely functional Least Recently Used cache (`LRU.Cache K V`) supporting `empty`, `lookup`, `contains`, `get`, `put`, and `remove`, with capacity-based eviction. Includes proofs for lookup membership/absence, key removal preservation, `markUsed` access-order invariants, and `get`/`remove` behaviour.
- **`Scratch/RateLimiter.lean`** — Token bucket rate limiter (`TokenBucket` and `processRequest`) that refills tokens over elapsed time up to capacity and consumes a token when accepting a request. Includes proofs that token counts never exceed capacity, rejected requests leave zero tokens, accepted requests consume one token, and `lastRefill` never decreases.

### Domain Modelling & Business Rules

- **`Scratch/Basic.lean`** — Demonstrates phantom-typed, unforgeable entity identifiers (`Identifier α` with a private constructor) over an inheritance hierarchy (`Thing`, `Agent`, `Person`, `Organisation`) using a `ToThing` typeclass so identifiers of distinct entity types cannot be mixed.
- **`Scratch/AccountBalance.lean`** — Bank account withdrawal model (`Account` with `ℚ≥0` balance, `WithdrawalResult`, and `withdraw`) with proofs that balances update as specified, remain non-negative, stay unchanged when withdrawing `0`, and reach `0` when withdrawing the full balance.
- **`Scratch/ApplyDiscount.lean`** — Rational discount calculation (`apply_discount`) parameterized by proof obligations (`0 ≤ discount ≤ 1` and `price ≥ 0`), with proofs that discounted prices are non-negative, do not exceed the original price, equal the original price at `0` discount, and equal `0` at full discount.
- **`Scratch/ReserveStock.lean`** — Inventory reservation function (`reserve : ℕ → ℕ → Option ℕ`) with proofs for stock conservation (`available = remaining + requested`), non-negativity when stock is sufficient, and returning `none` when requested stock exceeds availability.
- **`Scratch/ShoppingBasket.lean`** — Shopping basket pricing (`ShoppingBasketItem`, bounded rational percentage `Rat0TO100`, and `basketTotal`) with `#eval` examples and theorems covering empty baskets, zero-quantity items, non-negativity, quantity increases, and item-order invariance (`orderDoesNotMatter`).

### Geometry, Expressions & Numerical Models

- **`Scratch/FittingObjects.lean`** — Generic 3D spatial fitting (`Dims α`, `Object3D α` with per-side padding, `Space α`, and `canFit`) paired with phantom-typed length units (`Length U` and `LengthUnit` instances for `Metre`, `Centimetre`, `Inch`, and `Foot`). Proves monotonicity of `canFit`, unit self-conversion identity, and concrete fitting examples via `decide_cbv`.
- **`Scratch/Expr.lean`** — Arithmetic expression AST (`Const`, `Plus`, `Mult`, `Inc`) evaluated over `ℝ` (`evalExpr`), with proofs of evaluation rules, increment behaviour, commutativity of `Plus` and `Mult`, and termination.
- **`Scratch/Capital.lean`** — Computable `Float` model of capital growth with annual interest and withdrawals (`balanceF`, `trajectory`, `staysNonneg`, `firstNegativeYear`, `balanceClosed`, `exactTest`), accompanied by `#eval` experiments comparing recursive trajectories against closed-form expressions and depletion thresholds.
- **`Scratch/Dependencies.lean`** — Skeleton module (`aosd.dependencies`) with placeholder `Definitions` and `Proofs` sections.
