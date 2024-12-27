import Mathlib.Logic.Basic
import Mathlib.Control.Functor
import Mathlib.Control.Lawful
import Mathlib.Order.Filter.Basic
import Init.Control.Lawful.Instances

-- An individual parsing error located at a specific span
def Error := String

-- Any function that can combine multiple inputs of one type into an output of
-- another type, possibly failing
def Parser (α β : Type) := α -> Except Error β

-- Matches a specific element, and produces some output after parsing
def just {α : Type} [BEq α] [ToString α] : α -> Parser α α
  | a => λ e => if e == a then pure e else Except.error s!"found {e}; expected {a}"

-- Matches some element that fits a predicate with a reason explaining why the predicate failed
def filterExpected {α : Type} [ToString α] : (α -> Bool) -> Option String -> Parser α α
  | f, expected => λ e => if f e then pure e else Except.error s!"predicate match failed: found {e}; expected {expected}"

-- Matches some element that fits a predicate
def filter {α : Type} [ToString α] : (α -> Bool) -> Parser α α := flip filterExpected none

-- Convert a parsed element into another element
def mapWith {α β γ : Type} : (β -> γ) -> Parser α β -> Parser α γ := (Function.comp) ∘ Functor.map

--- Fallible mapping from one parser to another
def tryMapWith {α β γ : Type} : Parser β γ -> Parser α β -> Parser α γ := Bind.kleisliLeft

-- Matches anything in the parser
def any {α : Type} : Parser α α := pure

-- Parser that discards its input, producing an error message
def failWith {α : Type} : String -> Parser α α
  | msg => λ _ => Except.error msg

-- Parse multiple occurrences of an element
def repeatedN {α β : Type} : ℕ -> Parser α β -> Parser (List α) (List β)
  | n, p => Monad.sequence ∘ List.map p ∘ List.take n

-- Parse infinite occurrences of an element until the parser fails
def repeated {α β : Type} : Parser α β -> Parser (List α) (List β)
  | p => let isOk := λ (x : Except Error β) =>
    match x with
    | Except.ok _    => true
    | Except.error _ => false
    Monad.sequence ∘ List.takeWhile isOk ∘ List.map p

-- Parse one element after another
def andThen {α β γ: Type} : Parser α γ -> Parser α β -> Parser (List α) (β × γ)
  | pB, pA => λ elems => match elems with
    | a :: b :: _ => do
      let resA <- pA a
      let resB <- pB b
      return (resA, resB)
    | otherwise => Except.error s!"found {List.length otherwise}; expected at least 2 elems"

-- Tries one parser on an input or another on failure
def orParse {α β : Type} : Parser α β -> Parser α β -> Parser α β
  | pB, pA => λ e => (pB e) <|> (pA e)

def choice {α β : Type} : List (Parser α β) -> Parser α β
  | parsers => let rec firstRight := λ x => match x with
    | (Except.ok x) :: _ => pure x
    | (Except.error e) :: xs => (Except.error e) <|> firstRight xs
    | _ => Except.error "exhausted all parsers"
    λ e => firstRight (List.map (λ p => p e) parsers)

theorem just_matches_x_with_x {α : Type} [BEq α] [ReflBEq α] [ToString α] (x : α) : just x x = pure x := by
  unfold just
  simp [BEq.refl]

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

theorem map_with_produces_new_output {α β : Type} [ToString α] [BEq α] [ReflBEq α] (a : α) (b : β) (f : (α -> β)) (h : (f a) = b) : mapWith f (just a) a = pure b := by
  unfold mapWith
  simp
  simp [just_matches_x_with_x]
  congr

theorem try_map_with_produces_new_output {α β : Type} [ToString α] [BEq α] [ReflBEq α] (a : α) (b : β) (f : Parser α β) (h : (f a) = pure b) : tryMapWith f (just a) a = pure b := by
  unfold tryMapWith
  unfold Bind.kleisliLeft
  unfold just
  simp
  exact h

theorem any_matches_anything {α : Type} (a : α) : any a = pure a := by
  unfold any
  rfl

lemma sequence_map_pure {m : Type -> Type} {α : Type} [Monad m] [LawfulMonad m] (xs : List α) : Monad.sequence (List.map pure xs) = (pure : List α -> m (List α)) xs := by
  induction xs with
  | nil => simp [Monad.sequence]
  | cons h xc ih => simp [Monad.sequence]; rw [ih]; rw [pure_bind]

theorem can_match_repeated {α : Type} (n : ℕ) (l : List α) (f : Parser α α) (h : f = any) : repeatedN n f l = pure (List.take n l) := by
  unfold repeatedN
  simp
  simp [h]
  induction n with
  | zero => simp [Monad.sequence, List.take]
  | succ n => induction l with
    | nil => simp [Monad.sequence, List.map]
    | cons x xs => simp [Monad.sequence, any]; rw [← List.map_take]; rw [sequence_map_pure]; simp [bind_pure]

theorem and_then_parses_multiple {α : Type} (a : α) (p : Parser α α) (h : p = any) :
  andThen p p [a, a]  = pure (Prod.mk a a) := by
    unfold andThen
    simp
    subst h
    unfold any
    simp [bind_pure]

theorem fail_with_produces_msg_always {α : Type} (a : α) (msg : String) : failWith msg a = Except.error msg := by
  unfold failWith
  rfl

theorem choice_does_fallback {α : Type} (a : α) (p1 : Parser α α) (p2 : Parser α α) (h1 : p1 = failWith "bruh") (h2 : p2 = any) : choice [p1, p2] a = pure a := by
  unfold choice
  unfold choice.firstRight
  simp
  simp [h1, h2]
  unfold failWith
  unfold any
  unfold HOrElse.hOrElse
  unfold choice.firstRight
  simp
  simp [Except.tryCatch, tryCatch, MonadExceptOf.tryCatch, tryCatchThe, tryCatch, MonadExcept.orElse, OrElse.orElse, instHOrElseOfOrElse, Except.pure, pure]
