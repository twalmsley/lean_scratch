import Mathlib

namespace LRU

structure Cache (K V : Type) where
  capacity : Nat
  entries : List (K × V)
  accessOrder : List K

variable {K V : Type}
variable [DecidableEq K]

/-- Create an empty cache. -/
def empty (capacity : Nat) : Cache K V :=
  { capacity := capacity
    entries := []
    accessOrder := [] }

/-- Look up a key in the entry list. -/
def lookup : List (K × V) → K → Option V
  | [], _ => none
  | (k, v) :: rest, key =>
      if k = key then
        some v
      else
        lookup rest key

/-- Remove all entries with the given key. -/
def removeKey (entries : List (K × V)) (key : K) :
    List (K × V) :=
  entries.filter (fun entry => decide (entry.1 ≠ key))

/-- Remove all occurrences of a key from the access order. -/
def removeFromOrder (order : List K) (key : K) : List K :=
  order.filter (fun k => decide (k ≠ key))

/-- Removing a key removes every occurrence of that key from the access order. -/
theorem removeFromOrder_none (order : List K) (key : K) :
    key ∉ removeFromOrder order key := by
  simp [removeFromOrder]

/-- Membership in the filtered access order retains exactly entries for other keys. -/
theorem removeFromOrder_mem_iff (order : List K) (key other : K) :
    other ∈ removeFromOrder order key ↔ other ∈ order ∧ other ≠ key := by
  simp [removeFromOrder]

/-- Removing a key leaves every other key in the access order unchanged with respect to membership. -/
theorem removeFromOrder_preserves_other
    (order : List K) (removed other : K) (hne : other ≠ removed) :
    other ∈ removeFromOrder order removed ↔ other ∈ order := by
  rw [removeFromOrder_mem_iff]
  simp [hne]

/-- Mark a key as most recently used. -/
def markUsed (order : List K) (key : K) : List K :=
  key :: removeFromOrder order key

/-- Marking a key most recently used puts it at the front. -/
theorem markUsed_head (order : List K) (key : K) :
    (markUsed order key).head? = some key := by
  simp [markUsed]

/-- Marking a key removes earlier occurrences and retains membership of every other key. -/
theorem markUsed_mem_iff (order : List K) (key other : K) :
    other ∈ markUsed order key ↔ other = key ∨ other ∈ order := by
  simp [markUsed, removeFromOrder_mem_iff]
  constructor
  · intro h
    rcases h with hEq | hmem
    · exact Or.inl hEq
    · exact Or.inr hmem.1
  · intro h
    rcases h with hEq | hmem
    · exact Or.inl hEq
    · by_cases hne : other = key
      · exact Or.inl hne
      · exact Or.inr ⟨hmem, hne⟩

/-- Check whether a key is present. -/
def contains (cache : Cache K V) (key : K) : Bool :=
  match lookup cache.entries key with
  | none => false
  | some _ => true

/--
Retrieve a value and update its access order.

If the key is not present, return none and leave
the cache unchanged.
-/
def get (cache : Cache K V) (key : K) :
    Option V × Cache K V :=
  match lookup cache.entries key with
  | none =>
      (none, cache)
  | some value =>
      let updated :=
        { cache with
          accessOrder := markUsed cache.accessOrder key }
      (some value, updated)

/--
Insert or update a key-value pair.

If the cache is at capacity, evict the least
recently used key.

A cache with capacity zero stores no entries.
-/
def put (cache : Cache K V) (key : K) (value : V) :
    Cache K V :=

  if cache.capacity = 0 then
    { cache with
      entries := []
      accessOrder := [] }
  else
    let newEntries :=
      (key, value) :: removeKey cache.entries key

    let newOrder :=
      markUsed cache.accessOrder key

    if newOrder.length > cache.capacity then
      match newOrder.reverse.head? with
      | none =>
          { cache with
            entries := newEntries
            accessOrder := newOrder }
      | some oldest =>
          { cache with
            entries := removeKey newEntries oldest
            accessOrder := removeFromOrder newOrder oldest }
    else
      { cache with
        entries := newEntries
        accessOrder := newOrder }

/--
Remove a key from the cache.

Returns the previous value, if one existed,
along with the updated cache.
-/
def remove (cache : Cache K V) (key : K) :
    Option V × Cache K V :=
  let previous := lookup cache.entries key

  let updated :=
    { cache with
      entries := removeKey cache.entries key
      accessOrder := removeFromOrder cache.accessOrder key }

  (previous, updated)


-- Prove the lookup function is correct

/-- A successful lookup proves that the returned entry is in the cache. -/
theorem lookup_some_mem (entries : List (K × V)) (key : K) (value : V)
    (h : lookup entries key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
      obtain ⟨k, v⟩ := entry
      change (if k = key then some v else lookup rest key) = some value at h
      by_cases hk : k = key
      · simp [hk] at h
        subst value
        simp [hk]
      · have hrest : lookup rest key = some value := by
          simpa [hk] using h
        exact List.mem_cons_of_mem _ (ih hrest)



/-- A failed lookup proves that no matching entry occurs in the cache. -/
theorem lookup_none_of_no_entry (entries : List (K × V)) (key : K)
    (h : ¬ ∃ value : V, (key, value) ∈ entries) :
    lookup entries key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨k, v⟩ := entry
      have hrest : ¬ ∃ value : V, (key, value) ∈ rest := by
        intro hex
        apply h
        obtain ⟨value, hmem⟩ := hex
        exact ⟨value, List.mem_cons_of_mem _ hmem⟩
      change (if k = key then some v else lookup rest key) = none
      by_cases hk : k = key
      · exact (h ⟨v, by simp [hk]⟩).elim
      · simpa [hk] using ih hrest

/-- Removing a key deletes every matching entry. -/
theorem removeKey_lookup_none (entries : List (K × V)) (key : K) :
    lookup (removeKey entries key) key = none := by
  apply lookup_none_of_no_entry
  intro hex
  obtain ⟨value, hmem⟩ := hex
  rw [removeKey] at hmem
  rcases List.mem_filter.mp hmem with ⟨_, hkept⟩
  simp at hkept

/-- Membership in the filtered list retains exactly entries for other keys. -/
theorem removeKey_mem_iff (entries : List (K × V)) (entry : K × V)
    (key : K) :
    entry ∈ removeKey entries key ↔ entry ∈ entries ∧ entry.1 ≠ key := by
  simp [removeKey]

/-- Removing a key leaves lookups of every other key unchanged. -/
theorem lookup_removeKey (entries : List (K × V)) (removed : K) (key : K)
    (hne : key ≠ removed) :
    lookup (removeKey entries removed) key = lookup entries key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨k, v⟩ := entry
      simp only [removeKey, List.filter_cons]
      by_cases hk : k ≠ removed
      · simp [hk, lookup]
        by_cases hkey : k = key
        · simp [hkey]
        · simp [hkey]
          exact ih
      · simp [hk, lookup]
        by_cases hkey : k = key
        · exact (hk (hkey ▸ hne)).elim
        · simp [hkey]
          exact ih


-- Getting a missing key returns none.
/-- A miss leaves the cache unchanged. -/
theorem get_missing (cache : Cache K V) (key : K)
    (h : lookup cache.entries key = none) :
    get cache key = (none, cache) := by
  simp [get, h]

-- Getting an existing key returns its value.
/-- A hit returns the stored value and marks the key as most recently used. -/
theorem get_existing (cache : Cache K V) (key : K) (value : V)
    (h : lookup cache.entries key = some value) :
    get cache key =
      (some value, { cache with accessOrder := markUsed cache.accessOrder key }) := by
  simp [get, h]

-- Removing a key makes it absent.
/-- Removing a key deletes it from the resulting cache's entry list. -/
theorem remove_lookup_none (cache : Cache K V) (key : K) :
    lookup (remove cache key).2.entries key = none := by
  simp [remove, removeKey_lookup_none]

def cache0 : Cache Nat String :=
  empty 2

def cache1 := put cache0 1 "Alice"
def cache2 := put cache1 2 "Bob"

-- Cache contains:
-- 2 -> "Bob"   (most recently used)
-- 1 -> "Alice" (least recently used)

def cache3 := get cache2 1 |>.2

-- Accessing key 1 makes it most recently used.
-- Access order is now [1, 2]

def cache4 := put cache3 3 "Charlie"

-- Cache is full, so key 2 is evicted.
-- Entries now contain:
-- 3 -> "Charlie"
-- 1 -> "Alice"

#eval lookup cache4.entries 1
-- some "Alice"

#eval lookup cache4.entries 2
-- none

#eval lookup cache4.entries 3
-- some "Charlie"
