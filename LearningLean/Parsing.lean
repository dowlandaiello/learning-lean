import Mathlib.Logic.Basic

-- An individual parsing error located at a specific span
def Error := String

-- Any function that can combine multiple inputs of one type into an output of
-- another type, possibly failing
def Parser (α β : Type) := α -> Except Error β

-- Matches a specific element, and produces some output after parsing
def just {α : Type} [BEq α] [ToString α] : α -> Parser α α
  | a => fun e => if e == a then Except.ok e else Except.error s!"found {e}; expected {a}"

theorem just_matches_x_with_x { α : Type } [BEq α] [ToString α] (x : α) (h : x == x) : just x x = Except.ok x := by
  unfold just
  simp [eq_self]
  exact h

theorem just_does_not_match_a_with_b { α : Type } [BEq α] [LawfulBEq α] [ToString α] (a : α) (b : α) (h : a ≠ b) : just a b = Except.error s!"found {b}; expected {a}" := by
  unfold just
  simp [← ne_eq]
  symm
  exact h
