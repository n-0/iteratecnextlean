import Tutorial.Sensor
import Aesop

/-
  Our next step is will be to prove then n+1 step.
  Or less cryptic, we will use induction to prove
  theorems that involve loops or recursion.
-/
structure WeatherStation extends ActiveComponent where
  sensors: List Sensor
  temperatureHistory: List Int


/-
  Suppose we wanted to find the hottest day
  that the weather station measured.
  This requires that there is actually a history, we could go through (hence the thesis h),
  then we can choose an arbitrary initial value from the list and go through all elements
  and update our hottest temperature if needed. 
-/
def findMaxTemperatureRec (history: List Int) (currentMax: Int) : Int :=
  match history with
  | [] => currentMax
  | t::ts => max currentMax (findMaxTemperatureRec ts t)

def findMaxTemperature (s: WeatherStation) (h: s.temperatureHistory ≠ []): Int :=
   (findMaxTemperatureRec s.temperatureHistory.tail (s.temperatureHistory.head h))


/-
  We verify it's correctness by showing that
  all elements are less or equal than the result
  of findMaxTemperature. For technical reasons
  we require in the spec, that they're not the initial element.
  (Don't worry `findMaxTIncr` verifies this case).
  We prove two helping theorems (also called lemma's)
  for the final spec.
-/
class MaxTemperatureSpec where 
  verified : ∀ t: Int, t ∈ s.temperatureHistory ∧ (t ∈ List.tail s.temperatureHistory) → t ≤ (findMaxTemperature s h)

/-
 So called attributes in Lean, are macros that allow for different optimizations
 @[simp] means that Lean can use this theorem during the simp tactic.
 `findMaxTIncr` proves that the result of our recursion is always equal
  or larger than the initial value.
-/  
@[simp] 
lemma findMaxTIncr : ∀ t: Int, t ≤ findMaxTemperatureRec history t := by
    induction history with -- Our first induction, which introduces two goals
    | nil =>  -- one goal is the base case, here the empty list
        unfold findMaxTemperatureRec
        simp
    | cons x xs xs_ih => 
      -- and the other a list x:xs with the induction hypothesis that xs already fullfills our theorem
      unfold findMaxTemperatureRec
      simp

/-
  We leverage `findMaxTIncr` to show that regardless of the initial value
  the maximum property holds for all elements in our list.
  For complexities sake, the proof is shortened by the use of aesop
  (Automated Extensible Search for Obvious Proofs) a little angel that saves our lives/proofs 
  from time to time. A similar trick is the library_search tactic which looks through
  all theorems and tries to find one that matches your goal. If you want to
  see what is happening under the hood use #print findMaxTIncrArbit .
  You will find that it uses `findMaxTIncr` aliased as `Tutorial.WeatherStation._auxLemma.1`
  as well as the induction hypothesis `tail_ih`.
-/ 
lemma findMaxTIncrArbit : ∀ x t: Int, t ∈ history → t ≤ (findMaxTemperatureRec history x):= by
    induction history with
    | nil => 
        unfold findMaxTemperatureRec
        simp
    | cons head tail tail_ih =>
      intro x t th
      unfold findMaxTemperatureRec
      simp
      apply Or.inr
      aesop 


-- We conclude our proof with the specfication.
instance : MaxTemperatureSpec where
  verified := by
    intro s x t ⟨ht, htt⟩ 
    unfold findMaxTemperature
    apply findMaxTIncrArbit
    case a => exact htt

/-
  Wait a minute, how did Lean realize
  that our recursions come to an end?
  Isn't that the famous Halting-Problem,
  for which Turing himself proved, 
  that this can't be solved generally by a program?

  The answer is a suprising YES! 
  The magic trick of lean is to check if our recursion
  is a well founded relation that decreases on every call.
  The exact meaning of this, is outside the scope of this tutorial 
  (Refer to [1] and [2], if you're curious).
  Lean can often auto infer, if that's the case, but as the Halting-Problem
  suggests not always (even though the program halts), requiring
  help from humans.

  For example we have a function that compares the data of two
  weather stations to check if they have consistent results.

  We can explictly tell Lean for which arguments it should check
  that they're decreasing in the termination_by clause.
-/
def eqList (ts : List Int) (ts2 : List Int) : Bool :=
  match ts, ts2 with
  | [], [] => true 
  | _, [] => false 
  | [], _ => false 
  | t::tss, t2::tss2 => t = t2 ∧ eqList tss tss2
termination_by eqList ts ts2 => (ts, ts2)

/-
  Now it's your turn to do a little induction.
  The following exercises don't require you to use
  the induction hypothesis, and may seem a bit artifical,
  because I struggled to come up with instructive and
  at the same time, short examples.
-/ 

-- EXERCISE: Prove the following specification
class EqListSpec where 
  verified: ∀ ts : List Int, eqList ts [] = false ∨ ts = [] 

instance : EqListSpec where
  verified := by sorry


def hasActiveSensor (sensors: List Sensor) : Bool :=
  match sensors with
  | [] => true
  | s::xs => s.active ∨ hasActiveSensor xs

def activeSensor: Sensor := { active := true, sense := fun x => Except.ok x.temperature }

-- EXERCISE: Prove the following specification
class BrokenSensorSpec where
  verified : ∀ n: Nat, hasActiveSensor (List.replicate n activeSensor) = true

-- HINT: unfold List.replicate and simp in the n+1 step
instance : BrokenSensorSpec where
  verified := by sorry


-- [1] https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html
-- [2] https://en.wikipedia.org/wiki/Well-founded_relation