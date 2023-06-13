-- Let's continue with the creme dela creme
-- the treasure you came for
-- Proofs

/-
  According to the Curry-Howard Isomorphism
  every program is a proof and every proof is
  a program. Well now we only need to know the precise translation
  done by the isomorphism.

  The basic idea is, that the result of a program is a type.
  As said before Lean has the special type called Proposition, which
  means a logical statement; precisely what a proof tries to show. 

  Now we add another trick, which is called the univalence principle.
  In this context it means that regardless of the underyling program
  two programs are equivalent (ignoring inputs for now, that's another matter)
  if they produce the same type. In the same spirit: proofs are `univalent`
  if they result in identical theorems.

  There is a little gotcha attached to this. A logical statement
  is just a statement, could be True or False. Though if True and
  False are types and there would be some way to show the equivalence
  of one of our types to True, well then they're True! Hence nearly none 
  of Leans types are equivalent to False, otherwise the system wouldn't be  
  logical.
-/


/-
  Starting with a golden classic, the weather in boolean logic.
  We create a bunch of axioms, (things that are True by default).
-/
--variable ( Rain Sun Cloudy Frogs StreetWet: Prop )
axiom Rain: Prop
axiom Sun: Prop
axiom Cloudy: Prop
axiom Frogs: Prop
axiom StreetWet: Prop


/-
  Now we prove/(create/construct types) some basic concepts.
  The logical conjunction also known as And, can be created
  if we supply proofs/types for both of its arguments.
  It's constructor is also called And.intro.
  We assume with `h\1`, `h\2` the propositions
-/
example (h₁ : Rain) (h₂ : Cloudy): Rain ∧ Cloudy := by
  constructor -- call the constructor of the type in the goal
  -- work through each case of the arguments for the constructor
  case left =>
    -- provide the `exact` required type
    exact h₁
  case right =>
    exact h₂

/-
  Here another particular short proof 
-/
example (h₁ : Rain) (h₂ : Cloudy): Rain ∧ Cloudy := by
  apply And.intro h₁ h₂

-- in its simplest form apply `applies` a function
-- to the arguments afterwards and supplies the proof with
-- the resulting type. Many types related to boolean logic
-- have due to historical reasons an additional function called intro,
-- for their constructors.


/-
  but it gets even shorter 
-/
example (h₁ : Rain) (h₂ : Cloudy): Rain ∧ Cloudy := ⟨h₁, h₂⟩
-- This works by calling the constructor directly, which
-- returns the type of `And`

-- EXERCISE: Prove the following
example (h₁ : Sun) (h₂ : Cloudy): Sun ∧ Cloudy := by
  sorry -- sorry is a trick, that makes the goal an axiom, thus it is already proven 

/-
  The logical disjunction also known as Or is a type,
  that can be created if supply any of it's two argument types.
  After all it's enough if only one of them is true.
-/
example (h₁ : Rain) : Rain ∨ Cloudy := by
  apply Or.inl h₁

example (h₁ : Cloudy) : Rain ∨ Cloudy := by
  apply Or.inr h₁


-- EXERCISE: Prove the following
example (h₁ : Rain) (h₂ : Cloudy): Rain ∨ Cloudy := by
  sorry


/-
  We used a little trick in the preceeding examples.
  Check the type of this
-/
def grayDay (h₁ : Rain) : Rain ∨ Cloudy := by
  apply Or.inl h₁

#check @grayDay

/-
  We used our propositions as hypothesis/assumptions before and
  hide away, that this were logical `implications`
  all along. Thus is should be clear that
  the following is the same as our grayDay definition.
-/
example : Rain → Rain ∨ Cloudy := by
  intro h₁ -- (makes assumptions in the goal available as bound named variables)
  apply Or.inl h₁

-- EXERCISE: Prove the following
example : Sun → Cloudy → Sun ∧ Cloudy := by
  sorry 

-- Lets introduce a well known fact
def wellKnownImplication : Prop := Rain → StreetWet
/- 
  This implication is often used to highlight
  that if streetWet this not necessarily means that
  it rains. After all there could be an all encompassing flood.
-/
example : StreetWet ∧ wellKnownImplication → (Rain ∨ ¬ Rain) := by
  -- helpful if we need the underlying definition (hence you'll see this very often for formal verification)
  unfold wellKnownImplication
  -- we can destructure (oppositive of constructor) hypothesis like 
  -- in other languages (e.g. JS let {x, y, z} = { x: 1, y: 2, z: 3 })
  intro ⟨h₁, h₂⟩
  -- but actually we don't require any of them
  -- since it doesn't matter for the fact that it rains or doesn't rain.
  -- That's always true! In general this is called the law of excluded middle 
  -- shortened to `em` in Lean.
  apply Classical.em

-- EXERCISE: prove the following
example : wellKnownImplication ∧ Rain → StreetWet := by
  sorry

/-
  Well done! You have now learned the nuts and bolts 
  of propositional logic. Chapeau I may say.
  We end this section with the If-and-only-If (short Iff)
  or logical equivalence operator.
  To prove a proposition containf `A ↔ B`, we need to
  show `A → B` and `B → A` hold.
-/
def yourStdWeatherForecast := Sun ∨ Cloudy 
def rainAndSunOrRain : (yourStdWeatherForecast ∧ Sun) ↔ Sun := by
  unfold yourStdWeatherForecast
  constructor
  case mp =>
    intro ⟨a, c⟩
    exact c
  case mpr =>
    intro hsun
    have SunAndCloudy: Sun ∨ Cloudy := Or.inl hsun
    apply (And.intro SunAndCloudy hsun)

-- EXERCISE: prove the following
def onAClearDay (h₁: ¬Rain ∧ ¬Cloudy ↔ Sun) (h₂: ¬StreetWet ∧ ¬Cloudy) : Sun := by
  sorry


/-
FURTHER NOTES:
You might had the initial urge to use an analytic tableaux
to prove the theorems here, by setting the propositions to True/False
and check if the right table comes out (e.g. (A = True) ∧ (B = False) : False).
Comment out the following verify that lean understands this too
-/ 
--#eval True ∧ False 
/-
The main reason we don't do this here, is that this becomes quickly
tedious and downright computational expensive for larger logical propositions
(the SAT-Problem is NP-Hard) and would undermine the reason why we use
interative theorem provers. They allow us to use symbolic reasoning
like humans do to derive results that take model checkers ages.
-/