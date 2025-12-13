import LeanJavaScripty.Syntax

def State := String -> Int

def State.update (s : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else s y

def evalExpr (e: Expr) (s: State) : Int := match e with
    | Expr.val (n) => n
    | Expr.var (x) => s x
    | Expr.add e1 e2 => (evalExpr e1 s) + (evalExpr e2 s)
    | Expr.sub e1 e2 => (evalExpr e1 s) - (evalExpr e2 s)
-- evalExpr ρ e1 >>= fun v1 => evalExpr ρ e2 >>= fun v2 => some (evalBop op v1 v2)


def evalBoolExpr (b: BoolExp) (s: State) : Bool :=
    match b with
    | BoolExp._true => true
    | BoolExp._false => false
    | BoolExp._eq e1 e2 => (evalExpr e1 s) = (evalExpr e2 s)
    | BoolExp._lt e1 e2 => (evalExpr e1 s) < (evalExpr e2 s)
    | BoolExp._gt e1 e2 => (evalExpr e1 s) > (evalExpr e2 s)
    | BoolExp._and b1 b2 => (evalBoolExpr b1 s) && (evalBoolExpr b2 s)
    | BoolExp._or b1 b2 => (evalBoolExpr b1 s) || (evalBoolExpr b2 s)
    | BoolExp._not b1 => !(evalBoolExpr b1 s)


inductive BigStep: Stmt -> State -> State -> Prop where
    | skip: ∀ s,
        BigStep Stmt._skip s s
    | assign: ∀ s x e,
        BigStep (Stmt._assign x e) s (s.update x (evalExpr e s))
    | seq: ∀ s1 s2 s3 S1 S2,
        BigStep S1 s1 s2 →
        BigStep S2 s2 s3 →
        BigStep (Stmt._seq S1 S2) s1 s3
    | if_true: ∀ s1 s2 b S1 S2,
        evalBoolExpr b s1 = true →
        BigStep S1 s1 s2 →
        BigStep (Stmt._if_else b S1 S2) s1 s2
    | if_false: ∀ s1 s2 b S1 S2,
        evalBoolExpr b s1 = false →
        BigStep S2 s1 s2 →
        BigStep (Stmt._if_else b S1 S2) s1 s2
    | while_true: ∀ s1 s2 s3 b S,
        evalBoolExpr b s1 = true →
        BigStep S s1 s2 →
        BigStep (Stmt._while b S) s2 s3 →
        BigStep (Stmt._while b S) s1 s3
    | while_false: ∀ s b S,
        evalBoolExpr b s = false →
        BigStep (Stmt._while b S) s s

