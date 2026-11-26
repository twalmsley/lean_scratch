import Mathlib

namespace RingBuffer

/--
A bounded FIFO ring buffer.

`contents` stores live elements oldest-first (head = front).
Capacity is fixed; `push` rejects when full.
-/
structure Buffer (α : Type) where
  capacity : Nat
  contents : List α
  deriving Repr

variable {α : Type}

/-- Create an empty buffer with the given capacity. -/
def empty (capacity : Nat) : Buffer α :=
  { capacity := capacity, contents := [] }

/-- Number of elements currently stored. -/
def size (b : Buffer α) : Nat :=
  b.contents.length

/-- True when the buffer holds no elements. -/
def isEmpty (b : Buffer α) : Bool :=
  decide (b.contents.length = 0)

/-- True when the buffer cannot accept another element. -/
def isFull (b : Buffer α) : Bool :=
  decide (b.capacity ≤ b.contents.length)

/--
Push an element onto the back of the buffer.

Returns `none` if the buffer is full (unchanged);
otherwise returns the updated buffer.
-/
def push (b : Buffer α) (x : α) : Option (Buffer α) :=
  if b.contents.length < b.capacity then
    some { b with contents := b.contents ++ [x] }
  else
    none

/--
Pop the oldest element from the front.

Returns `none` if the buffer is empty.
-/
def pop (b : Buffer α) : Option (α × Buffer α) :=
  match b.contents with
  | [] => none
  | x :: xs => some (x, { b with contents := xs })

/-- Peek at the oldest element without removing it. -/
def peek (b : Buffer α) : Option α :=
  b.contents.head?

/-- Peek at the newest element without removing it. -/
def back (b : Buffer α) : Option α :=
  b.contents.getLast?

/-- Empty the buffer, keeping the same capacity. -/
def clear (b : Buffer α) : Buffer α :=
  { b with contents := [] }

/-- Logical contents oldest-first. -/
def toList (b : Buffer α) : List α :=
  b.contents

/-- Indexed access into the logical contents (0 = oldest). -/
def get? (b : Buffer α) (i : Nat) : Option α :=
  b.contents[i]?

/--
Push as many elements as will fit.

Returns the unpushed suffix together with the (possibly fuller) buffer.
-/
def pushAll (b : Buffer α) (xs : List α) : List α × Buffer α :=
  match xs with
  | [] => ([], b)
  | x :: rest =>
      match push b x with
      | none => (xs, b)
      | some b' => pushAll b' rest

/--
Pop up to `n` elements from the front.

Returns the taken elements (oldest-first) and the remaining buffer.
-/
def popN (b : Buffer α) (n : Nat) : List α × Buffer α :=
  match n, b.contents with
  | 0, _ => ([], b)
  | _, [] => ([], b)
  | n + 1, x :: xs =>
      let (taken, b') := popN { b with contents := xs } n
      (x :: taken, b')

/-! ### Invariants -/

/-- An empty buffer has size zero. -/
theorem empty_size (capacity : Nat) :
    size (empty capacity : Buffer α) = 0 := by
  simp [empty, size]

/-- An empty buffer never exceeds its capacity. -/
theorem empty_size_le_capacity (capacity : Nat) :
    size (empty capacity : Buffer α) ≤ capacity := by
  simp [empty, size]

/-- `isEmpty` holds exactly when the size is zero. -/
theorem isEmpty_iff (b : Buffer α) :
    isEmpty b = true ↔ size b = 0 := by
  simp [isEmpty, size]

/-- `isFull` holds exactly when capacity ≤ size. -/
theorem isFull_iff (b : Buffer α) :
    isFull b = true ↔ b.capacity ≤ size b := by
  simp [isFull, size]

/-- For a well-formed buffer, `isFull` means size equals capacity. -/
theorem isFull_iff_size_eq_capacity (b : Buffer α)
    (hsize : size b ≤ b.capacity) :
    isFull b = true ↔ size b = b.capacity := by
  simp [isFull_iff]
  omega

/-- A buffer created empty is empty. -/
theorem empty_isEmpty (capacity : Nat) :
    isEmpty (empty capacity : Buffer α) = true := by
  simp [empty, isEmpty]

/-! ### Push -/

/-- Pushing into a full buffer fails. -/
theorem push_eq_none_of_isFull (b : Buffer α) (x : α)
    (h : isFull b = true) :
    push b x = none := by
  unfold push isFull at *
  simp only [decide_eq_true_eq] at h
  split_ifs with hlt
  · omega
  · rfl

/-- Pushing into a non-full buffer succeeds. -/
theorem push_eq_some_of_not_full (b : Buffer α) (x : α)
    (h : isFull b = false) :
    push b x = some { b with contents := b.contents ++ [x] } := by
  unfold push isFull at *
  simp only [decide_eq_false_iff_not, not_le] at h
  split_ifs with hlt
  · rfl
  · omega

/-- A successful push preserves capacity. -/
theorem push_preserves_capacity (b : Buffer α) (x : α) (b' : Buffer α)
    (h : push b x = some b') :
    b'.capacity = b.capacity := by
  by_cases hlt : b.contents.length < b.capacity
  · simp [push, hlt] at h
    subst b'
    rfl
  · simp [push, hlt] at h

/-- A successful push increases size by one. -/
theorem push_size (b : Buffer α) (x : α) (b' : Buffer α)
    (h : push b x = some b') :
    size b' = size b + 1 := by
  by_cases hlt : b.contents.length < b.capacity
  · simp [push, hlt] at h
    subst b'
    simp [size]
  · simp [push, hlt] at h

/-- After a successful push, size still does not exceed capacity. -/
theorem push_size_le_capacity (b : Buffer α) (x : α) (b' : Buffer α)
    (_hsize : size b ≤ b.capacity)
    (h : push b x = some b') :
    size b' ≤ b'.capacity := by
  have hcap := push_preserves_capacity b x b' h
  have hsz := push_size b x b' h
  by_cases hlt : b.contents.length < b.capacity
  · simp [push, hlt] at h
    subst b'
    simp [size] at hsz hcap ⊢
    omega
  · simp [push, hlt] at h

/-- A successful push appends the element to the logical contents. -/
theorem push_toList (b : Buffer α) (x : α) (b' : Buffer α)
    (h : push b x = some b') :
    toList b' = toList b ++ [x] := by
  by_cases hlt : b.contents.length < b.capacity
  · simp [push, hlt] at h
    subst b'
    simp [toList]
  · simp [push, hlt] at h

/-- A successful push makes the new element the back. -/
theorem push_back (b : Buffer α) (x : α) (b' : Buffer α)
    (h : push b x = some b') :
    back b' = some x := by
  have hlist := push_toList b x b' h
  simp only [back, toList] at hlist ⊢
  rw [hlist]
  exact List.getLast?_concat

/-! ### Pop / peek -/

/-- Popping from an empty buffer fails. -/
theorem pop_eq_none_of_isEmpty (b : Buffer α)
    (h : isEmpty b = true) :
    pop b = none := by
  unfold isEmpty at h
  simp only [decide_eq_true_eq, List.length_eq_zero_iff] at h
  simp [pop, h]

/-- Popping from a non-empty buffer succeeds with the head. -/
theorem pop_eq_some_of_not_empty (b : Buffer α)
    (h : isEmpty b = false) :
    ∃ x xs, b.contents = x :: xs ∧
      pop b = some (x, { b with contents := xs }) := by
  cases hc : b.contents with
  | nil =>
      simp [isEmpty, hc] at h
  | cons x xs =>
      refine ⟨x, xs, rfl, ?_⟩
      simp [pop, hc]

/-- A successful pop preserves capacity. -/
theorem pop_preserves_capacity (b : Buffer α) (x : α) (b' : Buffer α)
    (h : pop b = some (x, b')) :
    b'.capacity = b.capacity := by
  unfold pop at h
  match hc : b.contents with
  | [] => simp [hc] at h
  | y :: ys =>
      simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- A successful pop decreases size by one. -/
theorem pop_size (b : Buffer α) (x : α) (b' : Buffer α)
    (h : pop b = some (x, b')) :
    size b' = size b - 1 := by
  unfold pop at h
  match hc : b.contents with
  | [] => simp [hc] at h
  | y :: ys =>
      simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [size, hc]

/-- After a successful pop, size still does not exceed capacity. -/
theorem pop_size_le_capacity (b : Buffer α) (x : α) (b' : Buffer α)
    (hsize : size b ≤ b.capacity)
    (h : pop b = some (x, b')) :
    size b' ≤ b'.capacity := by
  have hcap := pop_preserves_capacity b x b' h
  have hsz := pop_size b x b' h
  simp [size] at hsize hsz hcap ⊢
  omega

/-- Peek agrees with the element returned by pop. -/
theorem peek_eq_pop_fst (b : Buffer α) (x : α) (b' : Buffer α)
    (h : pop b = some (x, b')) :
    peek b = some x := by
  unfold pop at h
  match hc : b.contents with
  | [] => simp [hc] at h
  | y :: ys =>
      simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [peek, hc]

/-- A successful pop drops the head of the logical contents. -/
theorem pop_toList (b : Buffer α) (x : α) (b' : Buffer α)
    (h : pop b = some (x, b')) :
    toList b = x :: toList b' := by
  unfold pop at h
  match hc : b.contents with
  | [] => simp [hc] at h
  | y :: ys =>
      simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [toList, hc]

/-! ### FIFO -/

/-- Pushing into an empty buffer then popping returns that element. -/
theorem push_pop_empty (capacity : Nat) (x : α)
    (hpos : 0 < capacity) :
    ∃ b',
      push (empty capacity : Buffer α) x = some b' ∧
      pop b' = some (x, empty capacity) := by
  have hpush :
      push (empty capacity : Buffer α) x =
        some { capacity := capacity, contents := [x] } := by
    simp [push, empty, hpos]
  refine ⟨{ capacity := capacity, contents := [x] }, hpush, ?_⟩
  simp [pop, empty]

/--
After pushing a list that fits entirely, `toList` recovers that list.
-/
theorem pushAll_toList_of_fits (b : Buffer α) (xs : List α)
    (hfit : size b + xs.length ≤ b.capacity) :
    (pushAll b xs).1 = [] ∧ toList (pushAll b xs).2 = toList b ++ xs := by
  induction xs generalizing b with
  | nil =>
      simp [pushAll, toList]
  | cons x rest ih =>
      simp [size] at hfit
      have hnotFull : isFull b = false := by
        simp [isFull]
        omega
      have hpush := push_eq_some_of_not_full b x hnotFull
      simp [pushAll, hpush]
      have hsize' : size { b with contents := b.contents ++ [x] } + rest.length ≤
          { b with contents := b.contents ++ [x] }.capacity := by
        simp [size]
        omega
      have ⟨hleftover, hlist⟩ := ih _ hsize'
      refine ⟨hleftover, ?_⟩
      simpa [toList, List.append_assoc] using hlist

/-! ### Clear / indexing -/

/-- Clearing empties the buffer. -/
theorem clear_isEmpty (b : Buffer α) :
    isEmpty (clear b) = true := by
  simp [clear, isEmpty]

/-- Clearing preserves capacity. -/
theorem clear_preserves_capacity (b : Buffer α) :
    (clear b).capacity = b.capacity := by
  simp [clear]

/-- Clearing yields size zero. -/
theorem clear_size (b : Buffer α) :
    size (clear b) = 0 := by
  simp [clear, size]

/-- `get?` succeeds exactly for indices below the size. -/
theorem get?_eq_none_iff (b : Buffer α) (i : Nat) :
    get? b i = none ↔ size b ≤ i := by
  simp [get?, size]

/-- When `i < size`, `get?` returns the corresponding element. -/
theorem get?_eq_some_of_lt (b : Buffer α) (i : Nat)
    (h : i < size b) :
    get? b i = some (b.contents[i]'(by simpa [size] using h)) := by
  simp [get?, List.getElem?_eq_getElem (by simpa [size] using h)]

/-! ### Capacity zero -/

/-- A zero-capacity buffer is always full. -/
theorem capacity_zero_isFull (b : Buffer α) (h : b.capacity = 0) :
    isFull b = true := by
  simp [isFull, h]

/-- Pushing into a zero-capacity buffer always fails. -/
theorem capacity_zero_push_none (capacity : Nat) (x : α)
    (h : capacity = 0) :
    push (empty capacity : Buffer α) x = none := by
  subst h
  simp [push, empty]

/-- A zero-capacity empty buffer is empty. -/
theorem capacity_zero_isEmpty :
    isEmpty (empty 0 : Buffer α) = true := by
  simp [empty, isEmpty]

/-! ### pushAll / popN capacity preservation -/

/-- `pushAll` never exceeds capacity when the input buffer was within capacity. -/
theorem pushAll_size_le_capacity (b : Buffer α) (xs : List α)
    (hsize : size b ≤ b.capacity) :
    size (pushAll b xs).2 ≤ (pushAll b xs).2.capacity := by
  induction xs generalizing b with
  | nil =>
      simpa [pushAll] using hsize
  | cons x rest ih =>
      unfold pushAll
      cases hpush : push b x with
      | none =>
          simpa using hsize
      | some b' =>
          simp only
          exact ih b' (push_size_le_capacity b x b' hsize hpush)

/-- `popN` never exceeds capacity when the input buffer was within capacity. -/
theorem popN_size_le_capacity (b : Buffer α) (n : Nat)
    (hsize : size b ≤ b.capacity) :
    size (popN b n).2 ≤ (popN b n).2.capacity := by
  induction n generalizing b with
  | zero =>
      simpa [popN] using hsize
  | succ n ih =>
      cases b with
      | mk capacity contents =>
        cases contents with
        | nil =>
            simpa [popN] using hsize
        | cons x xs =>
            simp only [popN]
            have hsize' : size (⟨capacity, xs⟩ : Buffer α) ≤ capacity := by
              simp [size] at hsize ⊢
              omega
            exact ih ⟨capacity, xs⟩ hsize'

/-- `popN` of zero returns the original buffer. -/
theorem popN_zero (b : Buffer α) :
    popN b 0 = ([], b) := by
  simp [popN]

/-- `pushAll` of the empty list leaves the buffer unchanged. -/
theorem pushAll_nil (b : Buffer α) :
    pushAll b ([] : List α) = ([], b) := by
  simp [pushAll]

/-! ### Demos -/

def buf0 : Buffer Nat := empty 2

def buf1 : Buffer Nat := (push buf0 10).getD buf0
def buf2 : Buffer Nat := (push buf1 20).getD buf1

-- Buffer is now full: [10, 20]
-- Further push is rejected.
def buf2_reject : Option (Buffer Nat) := push buf2 30

def buf3 : Buffer Nat :=
  match pop buf2 with
  | some (_, b) => b
  | none => buf2

#eval toList buf0
-- []

#eval toList buf1
-- [10]

#eval toList buf2
-- [10, 20]

#eval buf2_reject
-- none

#eval peek buf2
-- some 10

#eval back buf2
-- some 20

#eval toList buf3
-- [20]

#eval toList (clear buf2)
-- []

end RingBuffer
