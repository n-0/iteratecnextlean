import Tutorial.DataTypesIntro
--def x: Scientist := { name := "Emmy Noether", scientificDomain := ScientificDomain.Physics }

/-
  Just as an appetizer of what is to come, 
  I provide here a very short proof of something well known.
-/
theorem reallyPowerfulFact : 1 + 1 = 2 := by
  rfl
  done

/-
  Yes this little line of code is indeed enough to show
  the desired result. 
  Proofs in lean are often started with
  the by keyword. Hover over it and check
  the Lean Infoview with the tactic state.

  At each line, where you write so called `tactics`
  (commands (like `rfl`) that have special abilities in lean and are more
  than mere functions)
  you will see the current progress of the proof, 
  what is currently available in terms of assumptions,
  or already shown theorems and what is still left to do (so called Goals).

  If the prove is finished the last line should end with `No goals`
  Alternatively one can apply the tactic `done` to check if that's the case. 
  Try it yourself by adding a new line with it to the proof!
-/ 

def company := "iteratec"
def hello := "world"

/-
  How to proceed with this tutorial?
  For the first 3, I'd recommend that, you don't actually try to solve
  the exercises at first, but rather note yourself, how you
  would solve them (maybe as a comment) and rather continue to take in a little
  more of lean's syntax and pecularities. 
  You can start with
  1. TypeTheoryIntro.lean
  2. DataTypesIntro.lean
  3. BasicLogic.lean
  After those you can actually start solving the exercises
  you're most interested in.
  Afterwards take a really joyful ride
  with leans macro/dsl capabilities in
  4. Game.lean
  and then go on with the somewhat more serious (basics of formal verification)
  5. Sensor.lean 
  and the final (more advanced formal verification, especially induction)
  6. WeatherStation.lean
-/