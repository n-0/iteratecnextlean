open Nat -- imports from other files is done via open keyword
-- in lean assignments are done with `:=`
-- `=` is reserved for Equality in the usual programming sense (`==` has also a meaning, namely bitwise equality)
-- `def` is like `var` or `let` in other languages
-- as you've guessed by now `--` is for line comments `/- -/` for multiline comments

def magic_number : Nat := 7
-- `:` is for helping the compiler to figure out, your intended type

-- Lean is strongly typed, but is quiet smart in inferring your intended types,
-- here it recognizes that the free variable x is of type Nat
def double_down := fun x => 2*x 

-- Use eval to try out the result of a computation,
-- while coding, instead of fully building your project
#eval double_down 2
-- to relate to λ-calculus language, we just bound the variable x to the value 2

/- 
If you want to state a fact, you use the
lowest type in the hierarchy Prop or a Proposition
-/
def false_is_the_lowest_level: (Sort 0) := False
def true_is_a_proposition : Prop := True
def still_a_proposition: Prop := True ∧ False

-- Lean is camelCase for `defs` and CamelCase for types

-- To get the type of a term use the check mackro (# prefixes macros)
#check 2


-- EXERCISE:
-- Everything is a type, so what is the type of double_down?
-- HINT: prefix function names with `@` to get more details from the #check macro

--

-- You can also write functions like this

def my_personal_function (name: String) := s!"Hello {name}"

-- s! is lean's macro for interpolating strings

-- Let's do some currying
def curry_to_dinner (meal: String) : Unit → String := fun _ => s!"{meal} with curry is tasty 😋"
#eval curry_to_dinner ("french_fries") ()

-- Unit is Lean's null type and is stated explictly as ()
-- _ is a place holder, use it when you're not sure what to put here and maybe lean can figure it out

-- EXERCISE:
-- Explain how the concepts of lambda abstraction and application where used in curry_to_dinner

-- Noice let's do some programming

-- uncomment the code below (find_even_numbers_wrong) and try to understand the meaning of the error messages
/--
def find_even_numbers_wrong (numbers: List Nat): List Nat := 
  let counter = 0
  let indices = []
  for (number : numbers)
    if number % 2 == 0 then indices.append counter
    counter = counter + 1
  return indices
--/


-- Correct version
def find_even_numbers_rec (numbers: List Nat) (indices: List Nat) (index: Nat): List Nat :=
  match numbers with
  | [] => indices
  | start :: rest => if (start % 2) = 0 then 
      find_even_numbers_rec rest (indices.append [index]) (index + 1)
    else
      find_even_numbers_rec rest (indices.append [index]) (index + 1)

def find_even_numbers (numbers: List Nat): List Nat :=
  find_even_numbers_rec numbers [] 0

-- Hm a lot of nesting and recursion, okay...
-- In a similar fashion
def nested_adding := (fun x => (fun y => x + y) 1) 2
-- so that means I need to nest function calls like this 


-- If you have some experience with functional programming languages you might know this as a common
-- feature, but maybe you're familiar with the solution to this problem too. 
-- Monads, Functors, applicatives and a bunch of Category Theory.
-- A subject that induces both fear and awe alike in programmers, though they tend to get overstated,
-- as they're often practical solutions to ("I can write this easily in another language, how can I do this here?") 
-- This is the reason why they seem to be everywhere. They're just translations of classical programming patterns into the
-- functional paradigm. Nevertheless they outside the scope of this tutorial.

-- Lean can actually sugar coat such logic and allows us to write sequential logic without much fuzz,
-- if we're using the right keywords to fire up the power of Monads.
def find_even_numbers_comfy (numbers: List Nat): List Nat := Id.run do
  let mut counter := 0
  let mut indices := []
  for number in numbers do
    if number % 2 = 0 then
      indices := indices ++ [counter] 
  return indices

#eval (find_even_numbers_comfy [1, 2, 3, 4]) = (find_even_numbers_comfy [1, 2, 3, 4])

-- Some further notes. LEAN version 4 is still under development
-- meaning that sometimes weird things happen, (e.g. I often encounter compiler errors 
-- if my file contains commented code at the end of the file), so sometimes
-- behavior can be a bit weird or slow. Usually this resolves itself if
-- you help the compiler with annotating types (and checking if you got the syntax correct),
-- or restarting the lean plugin/server.
-- But if nothing helps and you're 110% sure that it is LEAN's fault (happens only 0.0001% of the time), 
-- try out version 3 as it stable and doesn't have any shanigans (though the syntax is slightly different)
