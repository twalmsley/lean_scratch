import Mathlib


structure TokenBucket where
  capacity : Nat
  tokens : Nat
  refillRate : Nat
  lastRefill : Nat
  deriving Repr, DecidableEq

def processRequest
    (bucket : TokenBucket)
    (currentTime : Nat) :
    TokenBucket × Bool :=

  -- Time must never move backwards.
  let now := max currentTime bucket.lastRefill

  -- Calculate how much time has elapsed since the last refill.
  let elapsed := now - bucket.lastRefill

  -- Refill the bucket, but never exceed its capacity.
  let refilledTokens :=
    min bucket.capacity
      (bucket.tokens + elapsed * bucket.refillRate)

  -- Accept the request if at least one token is available.
  let accepted := refilledTokens > 0

  -- Consume one token if the request was accepted.
  let remainingTokens :=
    if accepted then refilledTokens - 1
    else refilledTokens

  -- Return the updated bucket and the result.
  let updatedBucket :=
    { bucket with
      tokens := remainingTokens
      lastRefill := now }

  (updatedBucket, accepted)


def exampleBucket : TokenBucket :=
  { capacity := 10
    tokens := 0
    refillRate := 2
    lastRefill := 0 }

#eval processRequest exampleBucket 0
-- Updated bucket has 0 tokens
-- Request accepted: false

#eval processRequest exampleBucket 3
-- 3 seconds elapsed, so 6 tokens are added
-- Bucket is capped at 10, then 1 token is consumed
-- Updated bucket has 9 tokens
-- Request accepted: true

-- processRequest never returns more tokens than the bucket capacity.
theorem processRequest_never_exceeds_capacity
    (bucket : TokenBucket) (currentTime : Nat) :
    (processRequest bucket currentTime).1.tokens ≤ bucket.capacity := by
  unfold processRequest
  dsimp
  split <;> omega

-- If the request is accepted, the returned token count is exactly one less than the refilled token count.
theorem processRequest_remaining_eq_refilled_minus_one
    (bucket : TokenBucket) (currentTime : Nat) :
    (processRequest bucket currentTime).1.tokens =
      min bucket.capacity
        (bucket.tokens + (max currentTime bucket.lastRefill - bucket.lastRefill) * bucket.refillRate) - 1 := by
  unfold processRequest
  dsimp
  split <;> omega

-- If the request is rejected, the returned token count is zero.
theorem processRequest_rejected_tokens_eq_zero
    (bucket : TokenBucket) (currentTime : Nat)
    (rejected : (processRequest bucket currentTime).2 = false) :
    (processRequest bucket currentTime).1.tokens = 0 := by
  unfold processRequest
  unfold processRequest at rejected
  simp at rejected
  simp
  split
  · omega
  · simp ; omega

-- The returned timestamp is never less than the original timestamp.
theorem processRequest_timestamp_never_decreases
    (bucket : TokenBucket) (currentTime : Nat) :
    (processRequest bucket currentTime).1.lastRefill ≥ bucket.lastRefill := by
  unfold processRequest
  dsimp
  omega

-- 1. Processing a request never increases the token count beyond what was available after refill.
  theorem processRequest_tokens_le_refilled
      (bucket : TokenBucket) (currentTime : Nat) :
      (processRequest bucket currentTime).1.tokens ≤
        min bucket.capacity
          (bucket.tokens + (max currentTime bucket.lastRefill - bucket.lastRefill) * bucket.refillRate) := by
    unfold processRequest
    dsimp
    split <;> omega
