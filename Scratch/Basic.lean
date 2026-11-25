import Mathlib

structure Thing where
  id : String
  deriving Repr

structure Agent extends Thing
  deriving Repr

structure Person extends Agent
  deriving Repr

structure Organisation extends Agent
  deriving Repr

class ToThing (α : Type) where
  toThing : α → Thing

instance : ToThing Thing where toThing x := x
instance : ToThing Agent where toThing x := x.toThing
instance : ToThing Person where toThing x := x.toThing
instance : ToThing Organisation where toThing x := x.toThing

structure Identifier (α : Type) where
  private mk ::
  id : String
  deriving Repr, DecidableEq

def Identifier.of {α : Type} [ToThing α] (x : α) : Identifier α :=
  ⟨(ToThing.toThing x).id⟩

def a : Person := { id := "person1" }
def b : Organisation := { id := "org1" }

def idA : Identifier Person := Identifier.of a
def idB : Identifier Organisation := Identifier.of b

#eval a
#eval b
#eval idA
#eval idB

-- Type error: expected `Identifier Person`, got `Identifier Organisation`
-- def wrong : Identifier Person := idB

-- Compile error: `Identifier.mk` is private, so you can't pass a bare String directly
-- def forged : Identifier Person := ⟨"person1"⟩
