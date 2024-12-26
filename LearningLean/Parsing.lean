import Mathlib.Logic.Basic

-- An individual parsing error located at a specific span
def Error := String

-- Any function that can combine multiple inputs of one type into an output of
-- another type, possibly failing
def Parser (α β : Type) := α -> Except Error β

-- Matches a specific element, and produces some output after parsing
def just {α : Type} [BEq α] [ToString α] : α -> Parser α α
  | a => fun e => if e == a then pure e else Except.error s!"found {e}; expected {a}"

-- Matches some element that fits a predicate with a reason explaining why the predicate failed
def filterExpected {α : Type} [ToString α] : (α -> Bool) -> Option String -> Parser α α
  | f, expected => fun e => if f e then pure e else Except.error s!"predicate match failed: found {e}; expected {expected}"

-- Matches some element that fits a predicate
def filter {α : Type} [ToString α] : (α -> Bool) -> Parser α α := flip filterExpected none

-- Convert a parsed element into another element
def mapWith {α β γ : Type} : (β -> γ) -> Parser α β -> Parser α γ := (Function.comp) ∘ Functor.map

theorem just_matches_x_with_x {α : Type} [BEq α] [ReflBEq α] [ToString α] (x : α) : just x x = pure x := by
  unfold just
  simp [← BEq.refl]
  simp

theorem just_does_not_match_a_with_b {α : Type} [BEq α] [ToString α] (a : α) (b : α) (h : ¬(b == a)) : just a b = Except.error s!"found {b}; expected {a}" := by
  unfold just
  simp [h]

theorem filter_matches_in_with_success_f {α : Type} [ToString α] (a : α) (f : (α -> Bool)) (h : f a) : filterExpected f Nothing a = pure a := by
  unfold filterExpected
  simp
  simp [h]

theorem filter_does_not_match_in_with_bad_f {α : Type} [ToString α] (a : α) (f : (α -> Bool)) (h : ¬(f a)) : filterExpected f Nothing a = Except.error s!"predicate match failed: found {a}; expected {Nothing}" := by
  unfold filterExpected
  simp
  simp [h]
