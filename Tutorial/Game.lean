/-
  Lean has extensive Macro capabilites, which
  is one of the reasons for its usage in the 
  formalization of mathematics.
  You can write proofs that are very close 
  to the version you would write on paper.

  On a more general note DSL (Domain specific languages)
  often allow developers to express programs in a more natural 
  way without the syntax noise of a programming language or framework.

  Let's consider a DSL for Rock-Paper-Scissors.
-/

-- First we define the underlying data structures.
inductive Move where
  | Stone : Move    
  | Paper : Move
  | Scissors : Move 
deriving Repr

structure Player where
  name: Nat
  move: Move
deriving Repr

structure Game where
  p1: Player
  p2: Player 
deriving Repr

def noPlayer (move: Move) : Player :=  { name := 0, move := move }

-- Then a way to find the winner of a Rock-Paper-Scissors round
def determineWinner (g: Game) : Nat :=
  let win := match g.p1.move, g.p2.move with
  | Move.Paper, Move.Stone => g.p1
  | Move.Stone, Move.Paper => g.p2
  | Move.Stone, Move.Scissors => g.p1
  | Move.Scissors, Move.Stone => g.p2
  | Move.Scissors, Move.Paper => g.p1
  | Move.Paper, Move.Scissors  => g.p2
  | _, m => noPlayer m 
  win.name

-- Now writing a game may seem a bit dense

def denseGame: Game := {
  p1 := {
    name := 7,
    move := Move.Paper
  },
  p2 := {
    name := 8,
    move := Move.Scissors
  }
}
-- Also the output of determineWinner is not exactly self explaining
#eval determineWinner denseGame

/-
  Lets give our code a cosmetic glow up!
  The simplest way of overloading symbols
  or defining syntax is the notation macro
  The :number term signalizes the compiler
  the priority for our syntax, meaning that
  `(2)` would become `(3)` with the following definition
  notation:63 "(" a:61 )" => a
  notation:64 "(" a:61 )" => a + 1
-/
notation:63 "🎮" a:62 "→" b:61 => (Player.mk a b)

notation:61 "✂️" => Move.Scissors
notation:62 "🪨️" => Move.Stone
notation:63 "📜" => Move.Paper

notation:53 "🏁" a:52 " vs " b:51 => (Game.mk a b)

/-
  Now we can players and games in a visual pleasing manner
-/
def me: Player := 🎮 1 →  ✂️
def you: Player := 🎮 2 → 📜
def gg := 🏁 me vs you

-- EXERCISE: Define another move `Move.Fountain` with the notation ⛲
-- and extend determineWinner accordingly

-- We define a proposition that asserts that some is the winner of the game
@[simp]
def isFirst (p: Player) (g: Game) : Prop := determineWinner g = p.name

/-
  Furthermore we tell Lean how it can compute, if the proposition is true.
  If a proposition has an instance of Decidable, that means that
  the answer can be computed or `decided`. This actually corresponds
  with the theoretical definition in complexity theory e.g. that the
  Halting-Problem is in general undecidable.
-/
@[default_instance]
instance {p: Player} {g: Game} : Decidable (isFirst p g) := by
  unfold isFirst
  -- In practice most often, we reduce our proposition 
  -- to another, from which we know it's decidable.
  -- In this case the Equality of natural numbers.
  apply instDecidableEqNat 

notation:61 "🥇" " of " b:54 " is " a:53 => isFirst a b

-- Now we can decide if the statement if a player is a winner of a game
-- in a playful way
#eval (Decidable.decide (🥇 of gg is me))

-- EXERCISE: Complete the definition of the following proposition
-- and make it decidable. Furthermore define a notation 
-- 🥈 of (Game) is (Player) to make it visually appealing.
-- HINT: instDecidableNot is the theorem that proves that
-- if a if p is decidable (¬ p) is decidable
@[simp]
def isSecond (p: Player) (g: Game) : Prop := sorry 

-- Let us proof some theorems about rock-paper-scissors
example (g: Game) (h: g.p1.move = Move.Scissors) (h2: g.p2.move = Move.Paper) : (🥇 of g is g.p1) := by
  simp
  unfold determineWinner
  rw [h, h2]
  done

-- If we want to prove this for other variations of the players moves
-- there won't be much change in the proofs structure. But copy and
-- pasting seems a bit inefficient. It's time to define our own tactic!

-- The definition reads rather archaic, but in a nutshell `syntax` works like `notation`
-- without the need of priorities. Also we can define the exact types we expect for the
-- arguments, we finally end ( `:` ) the definition with the resulting type 
-- for the new syntax (here tactic)
syntax "rockpaperscissors" Lean.Parser.Tactic.rwRule "," Lean.Parser.Tactic.rwRule : tactic
-- Next we define how lean should expand our macro. Like in python new lines can explictly 
-- stated with `;`.
macro_rules
  | `(tactic| rockpaperscissors $i, $j) => `(tactic| simp ; unfold determineWinner ; rw [$i, $j])

-- This is already much more compact
example (g: Game) (h: g.p1.move = Move.Paper) (h2: g.p2.move = Move.Stone) : (🥇 of g is g.p1) := by
  rockpaperscissors h, h2

-- EXERCISE: Define a custom tactic to prove that someone is the second place of a game
-- HINT: You require an additional hypothesis (h3: g.p2.name ≠ g.p1.name), otherwise
-- you have a first place that is also the second place.