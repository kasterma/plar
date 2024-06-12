inductive Expression where
   | Var : String -> Expression
   | Const : Int -> Expression
   | Add : Expression -> Expression -> Expression
   | Mul : Expression -> Expression -> Expression
deriving Repr

open Expression
def ex1 := Add (Const 1) (Const 2)
#check ex1
#print ex1

def ex2 := Add (Mul (Const 2) (Var "x")) (Var "y")
#print ex2

def ex3 := Add (Const 0) (Mul (Const 1) (Const 3))

def simplify1 (expr : Expression) : Expression :=
  match expr with
  | Expression.Add (Const n) (Const m) => Const (n + m)
  | Expression.Mul (Const n) (Const m) => Const (n * m)
  | Expression.Add (Const 0) x => x
  | Expression.Add x (Const 0) => x
  | Expression.Mul (Const 0) _ => Const 0
  | Expression.Mul _ (Const 0) => Const 0
  | Expression.Mul (Const 1) x => x
  | Expression.Mul x (Const 1) => x
  | e => e

def simplify (expr : Expression) : Expression :=
  match expr with
  | Expression.Add x y => simplify1 (Expression.Add (simplify x) (simplify y))
  | Expression.Mul x y => simplify1 (Expression.Mul (simplify x) (simplify y))
  | e => e

#eval (simplify ex3)
#eval ex3
#eval (simplify (Add (Mul (Add (Mul (Const 0) (Var "x")) (Const 1)) (Const 3)) (Const 12)))

#check ("hello".toList.any (fun x => x == 'z'))

def matcher (s: String) (c: Char) : Bool :=
  s.toList.any (fun x => x == c)

#eval matcher "hello" 'z'
#eval matcher "hello" 'l'
def space := matcher " \t\n\r"
def punctuation := matcher "()[]{},"
def symbolic := matcher "~`!@#$%^&*-+=|\\:;'<>,./?"
def numeric := matcher "0123456789"
def alphanumeric := matcher "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
#eval space ' '
#eval space '\t'
#eval space 'x'

def lexwhile (m: Char -> Bool) (s: (List Char)) : (List Char × List Char) :=
  (s.takeWhile m, s.dropWhile m)

#eval lexwhile alphanumeric "hello world".toList
#eval lexwhile numeric "123 world".toList
#eval (lexwhile numeric "123 world".toList).snd
#check "hello".toList

-- In the following function we don't use the function lexwhile b/c lean didn't
-- see through the function to see the termintion.  Hence we added that functionlity
-- into this function.  Now the termination is obvious from the structural recursion
-- on the first argument.
def lex_h (s: List Char) (acc: List String) (P: Char -> Bool) : List String :=
  match s with
  | [] => acc.reverse
  | c::cs => if space c then lex_h cs acc space -- reset P to space
    else
      if P c then match acc with
        | [] => lex_h cs [c.toString] P -- doesn't happen  TODO: make this fn simpler by making lean aware and removing the case
        | H::T => lex_h cs ((H ++ c.toString)::T) P
      else
        let P_new := if alphanumeric c then alphanumeric else
                if symbolic c then symbolic else
                fun _ => false
        lex_h cs (c.toString::acc) P_new


def lex (s: (List Char)) : List String := lex_h s [] space

#eval lex "hello world".toList
#eval lex "3 * 3 + 5".toList
#eval lex "2*((var_1 + x') + 11)".toList
#eval lex "23xxx * 34".toList
