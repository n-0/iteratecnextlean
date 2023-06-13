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
