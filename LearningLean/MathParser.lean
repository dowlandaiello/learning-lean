import LearningLean.Parsing

inductive Expr where
  | Num   : Nat  -> Expr
  | Plus  : Expr -> Expr -> Expr
  | Sub   : Expr -> Expr -> Expr
  | Mul   : Expr -> Expr -> Expr
  | Div   : Expr -> Expr -> Expr
deriving Repr

instance : ToString Expr :=
  ⟨let rec s
  | Expr.Num n    => s!"{n}"
  | Expr.Plus a b => s!"{s a} + {s b}"
  | Expr.Sub a b  => s!"{s a} - {s b}"
  | Expr.Mul a b  => s!"{s a} * {s b}"
  | Expr.Div a b  => s!"{s a} / {s b}"
  s⟩

inductive Token where
  | Digit : Nat -> Token
  | Plus  : Token
  | Sub   : Token
  | Mul   : Token
  | Div   : Token
deriving Repr

instance : ToString Token :=
  ⟨fun it => match it with
  | Token.Digit n => s!"{n}"
  | Token.Plus    => "+"
  | Token.Sub     => "-"
  | Token.Mul     => "*"
  | Token.Div     => "/"⟩

def lex : Parser (List Char) (List Token) :=
  let lDigit            := mapWith (pure ∘ Token.Digit) digit
  let lPlus             := mapWith (pure ∘ (λ _ => Token.Plus)) (just '+')
  let lSub              := mapWith (pure ∘ (λ _ => Token.Sub)) (just '-')
  let lMul              := mapWith (pure ∘ (λ _ => Token.Mul)) (just '*')
  let lDiv              := mapWith (pure ∘ (λ _ => Token.Div)) (just '/')
  let lIgnoreWhitespace := ignore whitespace
  mapWith (List.filterMap id) (repeated $ choice [lDigit, lPlus, lSub, lMul, lDiv, lIgnoreWhitespace])
