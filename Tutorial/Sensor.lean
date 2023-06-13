import Mathlib.Init.Algebra.Order
import Mathlib.Data.Int.Order.Basic


structure WeatherEnvironment where
  temperature: Int
deriving Repr

class ActiveComponent where
  active: Bool
deriving Repr

structure Sensor extends ActiveComponent where
  sense : WeatherEnvironment → (Except String Int)
    
namespace SensorSpace

-- We proceed with the actual creme de la creme
-- formal verification. 
-- Let's start with something simple
def activateSensor (sensor: Sensor) : Sensor :=
  { sensor with active := true }

-- We define our specification
class ActivationSpec where
  verified: ∀ (sensor: Sensor), (activateSensor sensor).active = true

-- And then show that there is an instance
-- that fullfills that specification 
-- (one could also directly show it without class and instance,
-- but this is a good pattern if one wants to group related
-- requirements for a system)
instance : ActivationSpec where
  verified := by
    intro s 
    -- The target (sensor here) of a universal quantifier (∀) can be introduced like argument 
    -- the goal is then to prove that the constraint of the target holds.
    rfl -- this is true by definition so we instruct lean to reflect on what it got
  
-- EXERCISE: Write a specification and prove a specification for the opposite action 
def shutdownSensor (sensor: Sensor) : Sensor :=
  { sensor with active := false }


-- Let's level up our game. Our sensor 
-- shouldn't succeed in measuring temperature above or below
-- it's working range that we were told. Hence it should always
-- fail if such a value is encountered.
def tooCold := "Too cold 🥶"
def tooHot := "Too hot 🥵"
def workingSensorCriteria (t: Int): Except String Int :=
    if 100 < t then Except.error tooHot 
    else
      if t < -100 then Except.error tooCold 
      else
        Except.ok t

def workingSensor: Sensor := {
  sense := fun weather => workingSensorCriteria weather.temperature,
  active := true
}
/-
  Why didn't we include the body of workingSensorCriteria directly in workingSensor?
  Because
  1. Nested Expressions like Except.toBool (if ... then ...)
  can be hard to prove as goal and it's simpler to argue about
  Except.toBool (someFunX)
  2. Readability, breaking up methods (especially in the functional paradigm)
  makes our intend easier to understand.
  This may seem obvious as a coding pattern, but has a special dimension in 
  in lean, as it influences lean's ability to simplify and reduce expressions.
  3. Performance, lean also has an easier time to compile your code and cache previous
  results from other definitions.

  To sum up, it's really helpful to keep everything short and separate. 
  Take a look into the Mathlib source code and you will
  notice that most proofs are not longer than 5 lines.
-/

-- Let's verify that our sensor is realistic and there are situations where it fails.
class TooColdSpec where
  sensor: Sensor
  verified: ∃ w: WeatherEnvironment, sensor.sense w = Except.error tooCold

instance : TooColdSpec where
  sensor := workingSensor
  verified := by
  /-
    the existential quantifier type has constructor
    consisting of the hypothesis and an instance
    that fullfills the hypothesis
  -/
    constructor 
    case w =>
      exact { temperature := -101 }
    case h =>
      unfold Sensor.sense
      unfold workingSensor 
      simp
      unfold workingSensorCriteria
      simp
      done


-- EXERCISE:  Proof the following specification
class TooHotSpec where
  sensor: Sensor
  verified: ∃ w: WeatherEnvironment, sensor.sense w = Except.error tooHot

instance : TooHotSpec where
  sensor := workingSensor
  verified := by sorry



-- Let's make the specification even stronger, and show that the sensors
-- fails exactly outside the specified range.
class SensorSpec where
  sensor: Sensor
  workingSensor: ∀ (weather : WeatherEnvironment), 
    weather.temperature > 100 ∨ weather.temperature < -100 → (sensor.sense weather).toBool = false


instance : SensorSpec where
  sensor := workingSensor
  workingSensor := by
    intro w hw
    unfold workingSensor
    simp
    cases hw
    case inr h =>
      -- notice that this local hypothesis wouldn't have been possible
      -- without refactoring workingSensorCriteria` body out of workingSensor
      have hh: workingSensorCriteria w.temperature = Except.error tooCold := by
        unfold workingSensorCriteria
        simp [h] -- simplify using hypthesis h
        have h100: -100 < 100 := by simp_arith -- automatically prove simple inequalities
        simp [h, h100]
        have hhh : (100 < w.temperature ) ↔ False := by
          simp
          have hhhh: w.temperature < 100 := by apply Int.lt_trans h h100
          apply Int.le_of_lt hhhh
          done
        rw [hhh]
        trivial -- works on trivial things like ((True = False) ↔ False), or False → False
      rw [hh]
      simp
    case inl h =>
      have hh: workingSensorCriteria w.temperature = Except.error tooHot := by
        unfold workingSensorCriteria
        simp [h] -- simplify using hypthesis h
        done -- only for readability
      /- 
        rw aka rewrite, is a tactic
        to rewrite any appearance of
        the expression in [hh, ...] in the current
        goal. It works iff, hh is an equality of equivalence (↔)
        Meaning you can't just substitue something, from which ~~you~~ know
        it's the definition. You still need a prop with = or ↔
      -/
      rw [hh] 
      simp -- execute Except.toBool

-- Nice, we did our first formal verifications!
-- Now this code could (may)be used in some artic or tropic laboratory 
-- to measure temperature.

/- How is this different from a test?
-- In software tests we would apply Boundary Value Analysis
-- to recognize that we should test for 101, -101
-- and something like 100, -100 to make sure everythings works.
-- Still it might be that something goes wrong at -500 
-- and our sensor throws tooHot (instead of tooCold). For a
-- computer it is infeasable to check all values in [(100, ∞), (-∞, -100,)],
-- while our proof can. Albeit this example is short enough,
-- s.t. we are simply convinced looking at code, but in more
-- complex situations, we are more hesitant too judge 
-- and want more guarantees.
-/  

-- EXERCISE: Use it to simplify the previous proof with the following
-- The previous example could be shortened by a great deal,
-- we could prove the following 
-- (actually Lean automatically prove such things for Nat, but Int is another matter)

-- Notice the use of {a, b, c: Int} instead of (a, b, c: Int) for the first arguments, that means that lean
-- will try to automatically infer the correct values of the variables. You can force
-- to supply them explictly by calling it like this 
-- transIntContradiction (α := v)
-- let v := 1
def transIntContradiction {a b c : ℤ} {h: a < b} (h₂: b < c) : c < a ↔ False := by
  have hh: a < c := by apply Int.lt_trans h h₂
  simp
  apply Int.le_of_lt hh
  done



--- ADDITIONAL EXERCISE: (Only if you already finished all others (not only in this file))
-- Actually we missed something in our specification 
-- namely that the temperature is measured if its in range
-- Comment out the following class and find a suitable
-- type for workingInRange and prove it for the existing `workingSensor`
/-
class SensorInRangeSpec where
  sensor: Sensor
  workingInRange: ?
-/


--- ADDITIONAL EXERCISE: (Only if you already finished all others (not only in this file))
/-
  Update `workingSensor` such that `Except.error "Inactive 🛑"`
  is returned if `sensor.active = False`, update the proves accordingly
  with  the assumption that the sensor (h₃: `sensor.active = True`)
  and create a Specification with instance proving that an inactive sensor
  doesn't not return something of type Exception.ok Int.
-/ 
end SensorSpace