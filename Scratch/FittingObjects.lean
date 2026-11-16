import Mathlib

namespace aosd.object_fitting

/-!
# Fitting any 3D object into a space

Generalisation of the fridge example:

(Generalised from a simple, concrete example to a general, abstract one.)

* `Dims α`      : a triple (width, height, depth) of measurements of type `α`.
* `Object3D α`  : any object with a size and the clearance required on each side of each axis.
* `Space α`     : the room available.
* `canFit`      : works for ANY measurement type `α` that has `+` and `≤`
                  (ℕ, ℚ, ℝ, or the unit-tagged `Length U` below).
* `Length U`    : a length tagged with its unit `U`, so metres/inches/feet can't be
                  mixed by accident, with checked conversion between units.
-/

section Geometry

/-- A measurement along each of the three axes. -/
structure Dims (α : Type) where
  width : α
  height : α
  depth : α

namespace Dims
variable {α β : Type}

def map (f : α → β) (d : Dims α) : Dims β :=
  ⟨f d.width, f d.height, f d.depth⟩

instance [Add α] : Add (Dims α) :=
  ⟨fun a b => ⟨a.width + b.width, a.height + b.height, a.depth + b.depth⟩⟩

/-- Componentwise order: `a ≤ b` means `a` fits within `b` on every axis. -/
instance [LE α] : LE (Dims α) :=
  ⟨fun a b => a.width ≤ b.width ∧ a.height ≤ b.height ∧ a.depth ≤ b.depth⟩

theorem le_def [LE α] (a b : Dims α) :
    a ≤ b ↔ (a.width ≤ b.width ∧ a.height ≤ b.height ∧ a.depth ≤ b.depth) :=
  Iff.rfl

instance [LE α] [DecidableRel (fun a b : α => a ≤ b)] (a b : Dims α) : Decidable (a ≤ b) :=
  decidable_of_iff (a.width ≤ b.width ∧ a.height ≤ b.height ∧ a.depth ≤ b.depth)
    (le_def a b).symm

theorem le_trans' [Preorder α] {a b c : Dims α} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨_root_.le_trans h₁.1 h₂.1, _root_.le_trans h₁.2.1 h₂.2.1, _root_.le_trans h₁.2.2 h₂.2.2⟩

end Dims

/-- Any 3D object: its size plus the clearance needed on *each side* of each axis. -/
structure Object3D (α : Type) where
  size : Dims α
  padding : Dims α

/-- The space available for an object. -/
structure Space (α : Type) where
  available : Dims α

namespace Object3D
variable {α β : Type}

/-- Total room needed: size plus padding on both sides of every axis. -/
def required [Add α] (o : Object3D α) : Dims α :=
  o.size + (o.padding + o.padding)

def map (f : α → β) (o : Object3D α) : Object3D β :=
  ⟨o.size.map f, o.padding.map f⟩

end Object3D

def Space.map {α β : Type} (f : α → β) (s : Space α) : Space β :=
  ⟨s.available.map f⟩

/-- An object fits if its padded size is within the available space on every axis. -/
def canFit {α : Type} [Add α] [LE α] (o : Object3D α) (s : Space α) : Prop :=
  o.required ≤ s.available

instance {α : Type} [Add α] [LE α] [DecidableRel (fun a b : α => a ≤ b)]
    (o : Object3D α) (s : Space α) : Decidable (canFit o s) := by
  unfold canFit
  infer_instance

/-- Unfolded form, matching the original per-axis statement. -/
theorem canFit_iff {α : Type} [Add α] [LE α] (o : Object3D α) (s : Space α) :
    canFit o s ↔
      (o.size.width + (o.padding.width + o.padding.width) ≤ s.available.width) ∧
      (o.size.height + (o.padding.height + o.padding.height) ≤ s.available.height) ∧
      (o.size.depth + (o.padding.depth + o.padding.depth) ≤ s.available.depth) :=
  Iff.rfl

/-- A fit in a smaller space is a fit in any bigger space. -/
theorem canFit_mono {α : Type} [Add α] [Preorder α] {o : Object3D α} {s s' : Space α}
    (h : s.available ≤ s'.available) : canFit o s → canFit o s' :=
  fun hf => Dims.le_trans' hf h

end Geometry

section Units

/-- A unit of length, described by its size in metres (a positive rational). -/
class LengthUnit (U : Type) where
  metres : ℚ
  metres_pos : 0 < metres

/-- A length measured in unit `U`. The unit is a phantom type, so mixing units is a type error. -/
structure Length (U : Type) where
  value : ℚ

namespace Length
variable {U V : Type}

instance : Add (Length U) := ⟨fun a b => ⟨a.value + b.value⟩⟩
instance : LE (Length U) := ⟨fun a b => a.value ≤ b.value⟩
instance (a b : Length U) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.value ≤ b.value))

@[simp] theorem add_value (a b : Length U) : (a + b).value = a.value + b.value := rfl
theorem le_def (a b : Length U) : a ≤ b ↔ a.value ≤ b.value := Iff.rfl

/-- Convert between any two units, going via metres. -/
def convert [LengthUnit U] [LengthUnit V] (l : Length U) : Length V :=
  ⟨l.value * LengthUnit.metres U / LengthUnit.metres V⟩

@[simp] theorem convert_value [LengthUnit U] [LengthUnit V] (l : Length U) :
    (convert l : Length V).value = l.value * LengthUnit.metres U / LengthUnit.metres V := rfl

/-- Converting to the same unit changes nothing. -/
theorem convert_self [inst : LengthUnit U] (l : Length U) : (convert l : Length U) = l := by
  have h : LengthUnit.metres U ≠ 0 := ne_of_gt inst.metres_pos
  cases l with
  | mk v => simp [convert, h]

end Length

/-- Convert every measurement of an object to another unit. -/
def Object3D.convertUnits {U V : Type} [LengthUnit U] [LengthUnit V]
    (o : Object3D (Length U)) : Object3D (Length V) :=
  o.map Length.convert

/-- Convert every measurement of a space to another unit. -/
def Space.convertUnits {U V : Type} [LengthUnit U] [LengthUnit V]
    (s : Space (Length U)) : Space (Length V) :=
  s.map Length.convert

/-! ### Concrete units. Add more the same way (yards, millimetres, cubits, ...). -/

inductive Metre : Type
inductive Centimetre : Type
inductive Inch : Type
inductive Foot : Type

instance : LengthUnit Metre := ⟨1, by norm_num⟩
instance : LengthUnit Centimetre := ⟨1 / 100, by norm_num⟩
instance : LengthUnit Inch := ⟨127 / 5000, by norm_num⟩   -- exactly 0.0254 m
instance : LengthUnit Foot := ⟨381 / 1250, by norm_num⟩   -- exactly 0.3048 m

@[simp] theorem Metre.metres : LengthUnit.metres Metre = 1 := rfl
@[simp] theorem Centimetre.metres : LengthUnit.metres Centimetre = 1 / 100 := rfl
@[simp] theorem Inch.metres : LengthUnit.metres Inch = 127 / 5000 := rfl
@[simp] theorem Foot.metres : LengthUnit.metres Foot = 381 / 1250 := rfl

end Units

section Examples

/-! ### Example 1: the original fridge, with plain ℕ measurements. -/

def fridge : Object3D ℕ :=
  { size := ⟨30, 55, 30⟩, padding := ⟨2, 10, 2⟩ }

def kitchenGap : Space ℕ :=
  { available := ⟨35, 75, 35⟩ }

example : canFit fridge kitchenGap := by decide

/-! ### Example 2: any other object, e.g. a washing machine, in different units. -/

def fridgeCm : Object3D (Length Centimetre) :=
  { size := ⟨⟨30⟩, ⟨55⟩, ⟨30⟩⟩, padding := ⟨⟨2⟩, ⟨10⟩, ⟨2⟩⟩ }

/-- Space measured in inches: 14" x 30" x 14" (= 35.56 x 76.2 x 35.56 cm). -/
def gapInches : Space (Length Inch) :=
  { available := ⟨⟨14⟩, ⟨30⟩, ⟨14⟩⟩ }

example : canFit fridgeCm (gapInches.convertUnits : Space (Length Centimetre)) := by
  simp only [canFit_iff, Dims.map, Space.convertUnits, Space.map,
    fridgeCm, gapInches, Length.le_def, Length.add_value, Length.convert_value,
    Centimetre.metres, Inch.metres]
  norm_num

end Examples

end aosd.object_fitting
