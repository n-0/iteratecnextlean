import Tutorial 
import Mathlib.Data.Set.Basic
open Set

def main : IO Unit :=
  IO.println s!"Hello, {company} !"


def simpleTheorem {A: Prop} {B: Prop} {C: Prop} (ha: A) (hb: B) (h: A ∧ B → C) : C  := by
  have andb: A ∧ B := ⟨ha, hb⟩ 
  apply h andb

def some_set_a: Set Nat := {1, 2, 3}
def some_set_b: Set Nat := {3, 4, 5}
def three: Nat := 3
def three_a : three ∈ some_set_a := by
  unfold some_set_a
  unfold three
  simp at *