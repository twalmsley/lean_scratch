import Mathlib

namespace aosd.led_circuit

/-!
# Simple LED light circuit

Series loop: battery → switch → resistor → LED → return wire.

* Wires are ideal for voltage drop (`R = 0`); they only contribute an ampacity limit.
* When the switch is open, current is `0`.
* When closed, `I = (V_battery - V_f) / R` (amperes, with V in volts and R in ohms).
* Runtime (hours) ≈ capacity (mAh) / (I in mA) = `capacitymAh / (I * 1000)`.
-/

section Components

/-- LED: forward voltage (V), nominal operating current (A), absolute max current (A). -/
structure LED where
  forwardVoltage : ℚ
  nominalCurrent : ℚ
  maxCurrent : ℚ
  deriving Repr

/-- Discrete resistor: resistance (Ω) and power rating (W). -/
structure Resistor where
  resistance : ℚ
  powerRating : ℚ
  deriving Repr

/-- Battery: fixed voltage (V), capacity (mAh), max discharge current (A). -/
structure Battery where
  voltage : ℚ
  capacitymAh : ℚ
  maxCurrent : ℚ
  deriving Repr

/-- Connecting wire: max current / ampacity (A). Resistance neglected. -/
structure Wire where
  maxCurrent : ℚ
  deriving Repr

/-- Switch: closed ⇒ circuit conducting. -/
structure Switch where
  closed : Bool
  deriving Repr

/-- Full circuit plus a minimum on-duration requirement (hours). -/
structure Circuit where
  led : LED
  resistor : Resistor
  battery : Battery
  wire : Wire
  switch : Switch
  minDurationHours : ℚ
  deriving Repr

end Components

section Derived

/-- Instantaneous series current (A). -/
def Circuit.current (c : Circuit) : ℚ :=
  if c.switch.closed then
    (c.battery.voltage - c.led.forwardVoltage) / c.resistor.resistance
  else
    0

/-- Instantaneous resistor dissipation (W): `I²R`. -/
def Circuit.resistorPower (c : Circuit) : ℚ :=
  let I := c.current
  I * I * c.resistor.resistance

/-- Estimated runtime (h) at the present current. `0` if not conducting. -/
def Circuit.runtimeHours (c : Circuit) : ℚ :=
  if c.current = 0 then 0
  else c.battery.capacitymAh / (c.current * 1000)

end Derived

section Constraints

/-- Voltages/resistances make the closed-circuit formula well-defined and sensible. -/
def Circuit.wellFormed (c : Circuit) : Prop :=
  0 < c.resistor.resistance ∧
  c.led.forwardVoltage < c.battery.voltage ∧
  0 < c.led.nominalCurrent ∧
  c.led.nominalCurrent ≤ c.led.maxCurrent ∧
  0 < c.battery.capacitymAh ∧
  0 < c.minDurationHours

/-- Current is in the LED's nominal…max window (required intensity without overstress). -/
def Circuit.ledCurrentOk (c : Circuit) : Prop :=
  c.led.nominalCurrent ≤ c.current ∧ c.current ≤ c.led.maxCurrent

def Circuit.resistorOk (c : Circuit) : Prop :=
  c.resistorPower ≤ c.resistor.powerRating

def Circuit.batteryCurrentOk (c : Circuit) : Prop :=
  c.current ≤ c.battery.maxCurrent

def Circuit.wireOk (c : Circuit) : Prop :=
  c.current ≤ c.wire.maxCurrent

def Circuit.durationOk (c : Circuit) : Prop :=
  c.minDurationHours ≤ c.runtimeHours

/-- All operating constraints hold with the switch closed. -/
def Circuit.satisfiesWhenOn (c : Circuit) : Prop :=
  c.switch.closed = true ∧
  c.wellFormed ∧
  c.ledCurrentOk ∧
  c.resistorOk ∧
  c.batteryCurrentOk ∧
  c.wireOk ∧
  c.durationOk

instance (c : Circuit) : Decidable c.wellFormed := by
  unfold Circuit.wellFormed; infer_instance

instance (c : Circuit) : Decidable c.ledCurrentOk := by
  unfold Circuit.ledCurrentOk; infer_instance

instance (c : Circuit) : Decidable c.resistorOk := by
  unfold Circuit.resistorOk; infer_instance

instance (c : Circuit) : Decidable c.batteryCurrentOk := by
  unfold Circuit.batteryCurrentOk; infer_instance

instance (c : Circuit) : Decidable c.wireOk := by
  unfold Circuit.wireOk; infer_instance

instance (c : Circuit) : Decidable c.durationOk := by
  unfold Circuit.durationOk; infer_instance

instance (c : Circuit) : Decidable c.satisfiesWhenOn := by
  unfold Circuit.satisfiesWhenOn; infer_instance

end Constraints

section Instance

/-!
## Concrete bill of materials

* Battery 5 V, 2000 mAh, max 500 mA
* LED Vf 2 V, nom 20 mA, max 30 mA
* Resistor 150 Ω, ¼ W → I = (5−2)/150 = 20 mA, P = 0.06 W
* Wire ampacity 100 mA
* Min duration 50 h (capacity gives 100 h at 20 mA)
-/

def demoLED : LED :=
  { forwardVoltage := 2, nominalCurrent := 20 / 1000, maxCurrent := 30 / 1000 }

def demoResistor : Resistor :=
  { resistance := 150, powerRating := 1 / 4 }

def demoBattery : Battery :=
  { voltage := 5, capacitymAh := 2000, maxCurrent := 500 / 1000 }

def demoWire : Wire :=
  { maxCurrent := 100 / 1000 }

def demoCircuit : Circuit :=
  { led := demoLED
    resistor := demoResistor
    battery := demoBattery
    wire := demoWire
    switch := { closed := true }
    minDurationHours := 20 }


#eval demoCircuit.current
#eval demoCircuit.runtimeHours
#eval demoCircuit.resistorPower

def demoCircuitOpen : Circuit :=
  { demoCircuit with switch := { closed := false } }

end Instance

section Proofs

example : demoCircuit.current ≤ demoLED.maxCurrent := by
  decide_cbv

example : demoCircuit.current ≥ demoLED.nominalCurrent := by
  decide_cbv

example : demoCircuit.resistorPower ≤ demoResistor.powerRating := by
  decide_cbv

example : demoCircuit.runtimeHours ≥ 10 := by
  decide_cbv

example : demoCircuit.satisfiesWhenOn := by
  decide_cbv

example : demoCircuitOpen.current = 0 := by
  decide_cbv

example : ¬demoCircuitOpen.satisfiesWhenOn := by
  decide_cbv

end Proofs

end aosd.led_circuit
