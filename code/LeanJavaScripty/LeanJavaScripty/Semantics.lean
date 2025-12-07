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


--  Tests

-- Helper: initial empty state (all variables are 0)
def emptyState : State := fun _ => 0

-- Test 1: Skip statement - state remains unchanged
theorem test_skip : BigStep Stmt._skip emptyState emptyState := by
  exact BigStep.skip emptyState

-- Test 2: Simple assignment - x := 5
theorem test_assign_simple : BigStep (Stmt._assign "x" (Expr.val 5)) emptyState (emptyState.update "x" 5) := by
  exact BigStep.assign emptyState "x" (Expr.val 5)

-- Test 3: Assignment with variable reference - y := x (where x = 10)
def stateWithX10 : State := emptyState.update "x" 10
theorem test_assign_var : BigStep (Stmt._assign "y" (Expr.var "x")) stateWithX10 (stateWithX10.update "y" 10) := by
  exact BigStep.assign stateWithX10 "y" (Expr.var "x")

-- Test 4: Assignment with addition - z := x + 5 (where x = 10)
theorem test_assign_add : BigStep (Stmt._assign "z" (Expr.add (Expr.var "x") (Expr.val 5))) stateWithX10 (stateWithX10.update "z" 15) := by
  exact BigStep.assign stateWithX10 "z" (Expr.add (Expr.var "x") (Expr.val 5))

-- Test 5: Assignment with subtraction - z := x - 3 (where x = 10)
theorem test_assign_sub : BigStep (Stmt._assign "z" (Expr.sub (Expr.var "x") (Expr.val 3))) stateWithX10 (stateWithX10.update "z" 7) := by
  exact BigStep.assign stateWithX10 "z" (Expr.sub (Expr.var "x") (Expr.val 3))

-- Test 6: Sequence - x := 5; y := 10
theorem test_seq : BigStep
    (Stmt._seq (Stmt._assign "x" (Expr.val 5)) (Stmt._assign "y" (Expr.val 10)))
    emptyState
    ((emptyState.update "x" 5).update "y" 10) := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 5)
  · exact BigStep.assign (emptyState.update "x" 5) "y" (Expr.val 10)

-- Test 7: If-true branch - if true then x := 1 else x := 2
theorem test_if_true : BigStep
    (Stmt._if_else BoolExp._true (Stmt._assign "x" (Expr.val 1)) (Stmt._assign "x" (Expr.val 2)))
    emptyState
    (emptyState.update "x" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign emptyState "x" (Expr.val 1)

-- Test 8: If-false branch - if false then x := 1 else x := 2
theorem test_if_false : BigStep
    (Stmt._if_else BoolExp._false (Stmt._assign "x" (Expr.val 1)) (Stmt._assign "x" (Expr.val 2)))
    emptyState
    (emptyState.update "x" 2) := by
  apply BigStep.if_false
  · rfl
  · exact BigStep.assign emptyState "x" (Expr.val 2)

-- Test 9: While-false (loop doesn't execute) - while false do x := 1
theorem test_while_false : BigStep
    (Stmt._while BoolExp._false (Stmt._assign "x" (Expr.val 1)))
    emptyState
    emptyState := by
  apply BigStep.while_false
  · rfl

-- Test 10: If with comparison - if x < 5 then y := 1 else y := 0 (where x = 3)
def stateWithX3 : State := emptyState.update "x" 3
theorem test_if_lt_true : BigStep
    (Stmt._if_else (BoolExp._lt (Expr.var "x") (Expr.val 5))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX3
    (stateWithX3.update "y" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign stateWithX3 "y" (Expr.val 1)

-- Test 11: If with equality comparison - if x == 10 then y := 1 else y := 0 (where x = 10)
theorem test_if_eq_true : BigStep
    (Stmt._if_else (BoolExp._eq (Expr.var "x") (Expr.val 10))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX10
    (stateWithX10.update "y" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign stateWithX10 "y" (Expr.val 1)

-- Test 12: If with greater-than comparison - if x > 5 then y := 1 else y := 0 (where x = 3)
theorem test_if_gt_false : BigStep
    (Stmt._if_else (BoolExp._gt (Expr.var "x") (Expr.val 5))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX3
    (stateWithX3.update "y" 0) := by
  apply BigStep.if_false
  · rfl
  · exact BigStep.assign stateWithX3 "y" (Expr.val 0)

-- Test 13: Nested sequence - x := 1; y := 2; z := 3
theorem test_nested_seq : BigStep
    (Stmt._seq (Stmt._assign "x" (Expr.val 1))
               (Stmt._seq (Stmt._assign "y" (Expr.val 2))
                          (Stmt._assign "z" (Expr.val 3))))
    emptyState
    (((emptyState.update "x" 1).update "y" 2).update "z" 3) := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 1)
  · apply BigStep.seq
    · exact BigStep.assign (emptyState.update "x" 1) "y" (Expr.val 2)
    · exact BigStep.assign ((emptyState.update "x" 1).update "y" 2) "z" (Expr.val 3)

-- Test 14: If with AND condition - if (x > 0) && (x < 10) then y := 1 else y := 0 (where x = 5)
def stateWithX5 : State := emptyState.update "x" 5
theorem test_if_and : BigStep
    (Stmt._if_else (BoolExp._and (BoolExp._gt (Expr.var "x") (Expr.val 0))
                                  (BoolExp._lt (Expr.var "x") (Expr.val 10)))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX5
    (stateWithX5.update "y" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign stateWithX5 "y" (Expr.val 1)

-- Test 15: If with OR condition - if (x < 0) || (x > 3) then y := 1 else y := 0 (where x = 5)
theorem test_if_or : BigStep
    (Stmt._if_else (BoolExp._or (BoolExp._lt (Expr.var "x") (Expr.val 0))
                                 (BoolExp._gt (Expr.var "x") (Expr.val 3)))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX5
    (stateWithX5.update "y" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign stateWithX5 "y" (Expr.val 1)

-- Test 16: If with NOT condition - if !(x == 0) then y := 1 else y := 0 (where x = 5)
theorem test_if_not : BigStep
    (Stmt._if_else (BoolExp._not (BoolExp._eq (Expr.var "x") (Expr.val 0)))
                   (Stmt._assign "y" (Expr.val 1))
                   (Stmt._assign "y" (Expr.val 0)))
    stateWithX5
    (stateWithX5.update "y" 1) := by
  apply BigStep.if_true
  · rfl
  · exact BigStep.assign stateWithX5 "y" (Expr.val 1)
