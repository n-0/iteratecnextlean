import Std.Data.HashMap.Basic
import Init.Prelude
import Init.Data.Nat.Basic
import Init.Data.Random
import Lean.Data.HashSet
import Mathlib.Init.Set



open Nat

def randomNumberGenerator := mkStdGen

-- Energy is generated on a scale from 1 to 10 (POWER!!!)
-- and it's cost as well

inductive EnergyGeneratorKind where
  | Solar
  | Wind
  | Coal
  | Hydro
  | Nuclear
  | Oil
  | PerpetumMobile
deriving BEq, Hashable, Repr

inductive VoltageLevel where
 | HV -- Ultra high voltage (Used around generators)
 | MV -- Medium Voltage (Used for industrial facilities and distribution network operators)
 | LV -- Low Voltage (residential area)
deriving BEq, Hashable, Repr

def limit_generators: Nat := 20

structure Money where
  units: Nat
deriving BEq, Hashable, Repr

structure EnergyGenerator where
  (id : Nat)
  (capacity : Nat)
  (cost : Money)
  (kind : EnergyGeneratorKind)
  (status : Bool)
deriving BEq, Hashable, Repr

namespace EnergyGenerator

def start (gen : EnergyGenerator) : EnergyGenerator :=
  { gen with status := true }

def stop (gen : EnergyGenerator) : EnergyGenerator :=
  { gen with status := false }

def getOutputPower (gen : EnergyGenerator) : Nat :=
  if gen.status then gen.capacity else 0

def randomEnergyGeneratorKind : Unit → EnergyGeneratorKind := fun _ =>
  match (randNat randomNumberGenerator 0 5).fst with
  | 0 => EnergyGeneratorKind.Solar
  | 1 => EnergyGeneratorKind.Wind
  | 2 => EnergyGeneratorKind.Coal
  | 3 => EnergyGeneratorKind.Hydro
  | 4 => EnergyGeneratorKind.Nuclear
  | 5 => EnergyGeneratorKind.Oil
  | _ => EnergyGeneratorKind.PerpetumMobile



def random : Unit → EnergyGenerator := fun _ =>
  {
    id := (randNat randomNumberGenerator 1 limit_generators).fst
    capacity := (randNat randomNumberGenerator 1 10).fst
    cost := { units := (randNat randomNumberGenerator 1 10).fst }
    kind := randomEnergyGeneratorKind ()
    status := false
  }

end EnergyGenerator

def gg: EnergyGenerator := EnergyGenerator.random ()

#eval gg


-- Someone who consumes energy
structure EnergyLoad where
  (id : Nat)
  (powerDemand : Nat)
  (acceptedVoltageLevel : VoltageLevel)
  (status : Bool)
deriving BEq, Hashable, Repr

namespace EnergyLoad

def turnOn (load : EnergyLoad) : EnergyLoad :=
  { load with status := true }

def turnOff (load : EnergyLoad) : EnergyLoad :=
  { load with status := false }

def getPowerDemand (load : EnergyLoad) : Nat :=
  if load.status then load.powerDemand else 0

end EnergyLoad


-- We assume lossless conversion, although in reality
-- we can expect around 1 - 10 % loss
structure EnergyTransformer where
  (id : Nat)
  (inputVoltage : VoltageLevel)
  (outputVoltage : VoltageLevel)
  (status : Bool)
deriving BEq, Hashable, Repr

namespace EnergyTransformer

def setStatus (trans : EnergyTransformer) (status : Bool) : EnergyTransformer :=
  { trans with status := status }

end EnergyTransformer


structure EnergyStorageSystem where
  (id : Nat)
  (capacity : Nat)
  (chargeLevel : Nat)
deriving BEq, Hashable, Repr

namespace EnergyStorageSystem

def charge (storage : EnergyStorageSystem) (amount : Nat) : EnergyStorageSystem :=
  { storage with chargeLevel := min (storage.chargeLevel + amount) storage.capacity }

def discharge (storage : EnergyStorageSystem) (amount : Nat) : EnergyStorageSystem :=
  { storage with chargeLevel := max (storage.chargeLevel - amount) 0 }

def getChargeLevel (storage : EnergyStorageSystem) : Nat :=
  storage.chargeLevel

end EnergyStorageSystem


structure EnergyTransmissionLine where
  (id : Nat)
  (capacity : Nat)
  (status : Bool)
deriving BEq, Hashable, Repr

namespace EnergyTransmissionLine

def setStatus (line : EnergyTransmissionLine) (status : Bool) : EnergyTransmissionLine :=
  { line with status := status }

def isAvailable (line : EnergyTransmissionLine) : Bool :=
  line.status

def getCapacity (line : EnergyTransmissionLine) : Nat :=
  line.capacity

end EnergyTransmissionLine

def users : Std.HashMap String String :=
  Std.HashMap.empty

inductive EnergyNode where
  | Generator : EnergyGenerator → EnergyNode
  | Storage: EnergyStorage → EnergyNode 
  | Load: EnergyLoad → EnergyNode 
  | Transformer: EnergyTransformer → EnergyNode 

structure EnergyNetwork where
  (generators: List EnergyGenerator)
  (storages: Lean.HashSet EnergyStorageSystem)
  (loads: Lean.HashSet EnergyLoad)
  (transmissionLines: Lean.HashSet EnergyTransmissionLine)
  (transformers: Lean.HashSet EnergyTransformer)
  (connections: Lean.HashMap EnergyTransmissionLine EnergyNode) 
  (currentTime: Nat)


def deriveNetDemand (loads: Lean.HashSet EnergyLoad) : Nat := loads.fold (fun (acc: Nat) (load: EnergyLoad) => acc + load.powerDemand) 0


def oneGeneratorIsEnough (network: EnergyNetwork) : Prop := ∃ generator : EnergyGenerator, 
    generator ∈ network.generators ∧ deriveNetDemand network.loads ≤ generator.capacity

def pregenerators: Lean.HashSet EnergyGenerator := Lean.HashSet.empty
def mygenerators := pregenerators.insert gg

def basicNetwork: EnergyNetwork := ⟨ [gg], Lean.HashSet.empty, Lean.HashSet.empty, Lean.HashSet.empty, Lean.HashSet.empty, Lean.HashMap.empty, 0⟩

#eval repr basicNetwork

def proofOfBasicNetwork: oneGeneratorIsEnough basicNetwork := by
  unfold oneGeneratorIsEnough
  simp
  constructor
  case w =>
    exact gg
  case h =>
    constructor
    case left =>

    case right =>
      sorry
      



--  constructor


def node1 := EnergyNode.Generator gg

def getBackGenerator (node: EnergyNode): Option EnergyGenerator := match node with
  | EnergyNode.Generator g => Option.some g
  | _ => Option.none

#eval getBackGenerator node1


def someEnergyTransmissionLine: EnergyTransmissionLine := { id := 1, capacity := 2, status := false }
def updatedEnergyTransmissionLine := someEnergyTransmissionLine.setStatus false
def make_things_simple := "Simple"
