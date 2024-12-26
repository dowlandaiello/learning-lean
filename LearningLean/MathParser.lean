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

-- Combines tokens of similar type into larger numbers
def joinDigit : Nat -> (Prod Nat Nat) -> Nat
    | acc, (place, digit) => acc + (digit * (Nat.pow 10 place))

def joinNums (nums : List Nat) : Nat :=
    List.enum nums |> List.foldl joinDigit 0

instance : ToString Token :=
  ⟨fun it => match it with
  | Token.Digit n => s!"{n}"
  | Token.Plus    => "+"
  | Token.Sub     => "-"
  | Token.Mul     => "*"
  | Token.Div     => "/"⟩

-- A fallible function which converts some input to an output
def Parser (a b : Type) := a -> Option b

def RepParser (a b : Type) := Parser (List a) (List b)

-- Creates a new parser which consumes the input multiple
-- times with the given parser
def pRepeated : Parser a b -> RepParser a b
  | p =>
    let rec parseRep
    | [] => some []
    | x :: xs => (p x).map (fun x => x :: (Option.getD (parseRep xs) []))
    parseRep

def pNone {a b : Type} : Parser a b :=
    fun _ => none

def pOr : Parser a b -> Parser a b -> Parser a b
    | p1, p2 => fun src => p1 src |> Option.getD (p2 src)

def pChoice : List (Parser a b) -> Parser a b
    | [] => pNone
    | x :: xs => List.foldl (fun acc x => pOr acc x) x xs

def pDigit : Parser Char Nat
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | '8' => some 8
    | '9' => some 9
    | _ => none

def pOperator : Parser Char Token
    | '+' => some Token.Plus
    | '-' => some Token.Sub
    | '*' => some Token.Mul
    | '/' => some Token.Div
    | _ => none

def pMap {a b c : Type} (p1 : Parser a b) (f : b -> c) : Parser a c :=
    fun stream => (p1 stream).map f

def just {a : Type} [BEq a] (val : a) : Parser a a :=
    fun src : a => if src == val then some src else none

def adjacentDigits : 

def parseToken : RepParser Char Token :=
    let tokens := pChoice [pMap pDigit Token.Digit, pOperator] |> pRepeated
    

