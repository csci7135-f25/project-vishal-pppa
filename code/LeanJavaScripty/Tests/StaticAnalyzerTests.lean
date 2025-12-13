import LeanJavaScripty.StaticAnalyzer

/-
  Tests for the Static Analyzer
  Each test includes:
  1. The original JavaScripty program (in comments)
  2. Concrete evaluation test using BigStep semantics
  3. Abstract interpretation test using the static analyzer
-/

-- ============================================================================
-- Test 1: Simple Assignment
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 5
  ```
  Expected: x = 5
-/

-- Concrete Test
def test1_stmt : Stmt := Stmt._assign "x" (Expr.val 5)

theorem test1_concrete : BigStep test1_stmt emptyState (emptyState.update "x" 5) := by
  exact BigStep.assign emptyState "x" (Expr.val 5)

-- Abstract Test
def test1_absState : AbsState := exec test1_stmt AbsState.empty
#eval test1_absState "x"  -- Should be: AbsVal.num (Interval.range (Bound.val 5) (Bound.val 5))


-- ============================================================================
-- Test 2: Sequence of Assignments
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 10;
  y := 20
  ```
  Expected: x = 10, y = 20
-/

def test2_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._assign "y" (Expr.val 20))

-- Concrete Test
theorem test2_concrete : BigStep test2_stmt emptyState ((emptyState.update "x" 10).update "y" 20) := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 10)
  · exact BigStep.assign (emptyState.update "x" 10) "y" (Expr.val 20)

-- Abstract Test
def test2_absState : AbsState := exec test2_stmt AbsState.empty
#eval test2_absState "x"  -- Should be: [10, 10]
#eval test2_absState "y"  -- Should be: [20, 20]


-- ============================================================================
-- Test 3: Addition Expression
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 5;
  y := 3;
  z := x + y
  ```
  Expected: x = 5, y = 3, z = 8
-/

def test3_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 5))
    (Stmt._seq
      (Stmt._assign "y" (Expr.val 3))
      (Stmt._assign "z" (Expr.add (Expr.var "x") (Expr.var "y"))))

-- Concrete Test
def test3_finalState : State := ((emptyState.update "x" 5).update "y" 3).update "z" 8

theorem test3_concrete : BigStep test3_stmt emptyState test3_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 5)
  · apply BigStep.seq
    · exact BigStep.assign (emptyState.update "x" 5) "y" (Expr.val 3)
    · exact BigStep.assign ((emptyState.update "x" 5).update "y" 3) "z"
        (Expr.add (Expr.var "x") (Expr.var "y"))

-- Abstract Test
def test3_absState : AbsState := exec test3_stmt AbsState.empty
#eval test3_absState "x"  -- Should be: [5, 5]
#eval test3_absState "y"  -- Should be: [3, 3]
#eval test3_absState "z"  -- Should be: [8, 8]


-- ============================================================================
-- Test 4: Subtraction Expression
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 10;
  y := 4;
  z := x - y
  ```
  Expected: x = 10, y = 4, z = 6
-/

def test4_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._seq
      (Stmt._assign "y" (Expr.val 4))
      (Stmt._assign "z" (Expr.sub (Expr.var "x") (Expr.var "y"))))

-- Concrete Test
def test4_finalState : State := ((emptyState.update "x" 10).update "y" 4).update "z" 6

theorem test4_concrete : BigStep test4_stmt emptyState test4_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 10)
  · apply BigStep.seq
    · exact BigStep.assign (emptyState.update "x" 10) "y" (Expr.val 4)
    · exact BigStep.assign ((emptyState.update "x" 10).update "y" 4) "z"
        (Expr.sub (Expr.var "x") (Expr.var "y"))

-- Abstract Test
def test4_absState : AbsState := exec test4_stmt AbsState.empty
#eval test4_absState "x"  -- Should be: [10, 10]
#eval test4_absState "y"  -- Should be: [4, 4]
#eval test4_absState "z"  -- Should be: [6, 6]


-- ============================================================================
-- Test 5: If-Else Statement (true branch)
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 5;
  if (x < 10) then
    y := 1
  else
    y := 0
  ```
  Concrete: x = 5, y = 1 (takes true branch)
  Abstract: x = [5,5], y = [0,1] (joins both branches)
-/

def test5_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 5))
    (Stmt._if_else
      (BoolExp._lt (Expr.var "x") (Expr.val 10))
      (Stmt._assign "y" (Expr.val 1))
      (Stmt._assign "y" (Expr.val 0)))

-- Concrete Test (takes the true branch since 5 < 10)
def test5_finalState : State := (emptyState.update "x" 5).update "y" 1

theorem test5_concrete : BigStep test5_stmt emptyState test5_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 5)
  · apply BigStep.if_true
    · rfl
    · exact BigStep.assign (emptyState.update "x" 5) "y" (Expr.val 1)

-- Abstract Test (joins both branches since we don't track conditions)
def test5_absState : AbsState := exec test5_stmt AbsState.empty
#eval test5_absState "x"  -- Should be: [5, 5]
#eval test5_absState "y"  -- Should be: join of [1,1] and [0,0] -> some interval containing both


-- ============================================================================
-- Test 6: If-Else Statement (false branch)
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 15;
  if (x < 10) then
    y := 1
  else
    y := 0
  ```
  Concrete: x = 15, y = 0 (takes false branch)
-/

def test6_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 15))
    (Stmt._if_else
      (BoolExp._lt (Expr.var "x") (Expr.val 10))
      (Stmt._assign "y" (Expr.val 1))
      (Stmt._assign "y" (Expr.val 0)))

-- Concrete Test (takes the false branch since 15 >= 10)
def test6_finalState : State := (emptyState.update "x" 15).update "y" 0

theorem test6_concrete : BigStep test6_stmt emptyState test6_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 15)
  · apply BigStep.if_false
    · rfl
    · exact BigStep.assign (emptyState.update "x" 15) "y" (Expr.val 0)

-- Abstract Test
def test6_absState : AbsState := exec test6_stmt AbsState.empty
#eval test6_absState "x"  -- Should be: [15, 15]
#eval test6_absState "y"  -- Should be: join of both branches


-- ============================================================================
-- Test 7: Skip Statement
-- ============================================================================
/-
  JavaScripty Program:
  ```
  skip
  ```
  Expected: state unchanged
-/

def test7_stmt : Stmt := Stmt._skip

-- Concrete Test
theorem test7_concrete : BigStep test7_stmt emptyState emptyState := by
  exact BigStep.skip emptyState

-- Abstract Test
def test7_absState : AbsState := exec test7_stmt AbsState.empty
#eval test7_absState "x"  -- Should be: bottom (undefined)


-- ============================================================================
-- Test 8: Complex Arithmetic
-- ============================================================================
/-
  JavaScripty Program:
  ```
  a := 100;
  b := 30;
  c := a - b;
  d := c + 5
  ```
  Expected: a = 100, b = 30, c = 70, d = 75
-/

def test8_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "a" (Expr.val 100))
    (Stmt._seq
      (Stmt._assign "b" (Expr.val 30))
      (Stmt._seq
        (Stmt._assign "c" (Expr.sub (Expr.var "a") (Expr.var "b")))
        (Stmt._assign "d" (Expr.add (Expr.var "c") (Expr.val 5)))))

-- Concrete Test
def test8_finalState : State :=
  (((emptyState.update "a" 100).update "b" 30).update "c" 70).update "d" 75

theorem test8_concrete : BigStep test8_stmt emptyState test8_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "a" (Expr.val 100)
  · apply BigStep.seq
    · exact BigStep.assign (emptyState.update "a" 100) "b" (Expr.val 30)
    · apply BigStep.seq
      · exact BigStep.assign ((emptyState.update "a" 100).update "b" 30) "c"
          (Expr.sub (Expr.var "a") (Expr.var "b"))
      · exact BigStep.assign (((emptyState.update "a" 100).update "b" 30).update "c" 70) "d"
          (Expr.add (Expr.var "c") (Expr.val 5))

-- Abstract Test
def test8_absState : AbsState := exec test8_stmt AbsState.empty
#eval test8_absState "a"  -- Should be: [100, 100]
#eval test8_absState "b"  -- Should be: [30, 30]
#eval test8_absState "c"  -- Should be: [70, 70]
#eval test8_absState "d"  -- Should be: [75, 75]


-- ============================================================================
-- Test 9: While Loop (simple increment)
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 0;
  while (x < 3) do
    x := x + 1
  ```
  Concrete: After loop, x = 3
  Abstract: x should widen to include values from iterations
-/

def test9_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._while
      (BoolExp._lt (Expr.var "x") (Expr.val 3))
      (Stmt._assign "x" (Expr.add (Expr.var "x") (Expr.val 1))))

-- Abstract Test (concrete proof for while loops is more complex)
def test9_absState : AbsState := exec test9_stmt AbsState.empty
#eval test9_absState "x"  -- Should show an interval from widening


-- ============================================================================
-- Test 10: Nested If-Else
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 5;
  if (x > 0) then
    if (x < 10) then
      y := 1
    else
      y := 2
  else
    y := 0
  ```
  Concrete: x = 5, y = 1
-/

def test10_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 5))
    (Stmt._if_else
      (BoolExp._gt (Expr.var "x") (Expr.val 0))
      (Stmt._if_else
        (BoolExp._lt (Expr.var "x") (Expr.val 10))
        (Stmt._assign "y" (Expr.val 1))
        (Stmt._assign "y" (Expr.val 2)))
      (Stmt._assign "y" (Expr.val 0)))

-- Concrete Test
def test10_finalState : State := (emptyState.update "x" 5).update "y" 1

theorem test10_concrete : BigStep test10_stmt emptyState test10_finalState := by
  apply BigStep.seq
  · exact BigStep.assign emptyState "x" (Expr.val 5)
  · apply BigStep.if_true
    · rfl
    · apply BigStep.if_true
      · rfl
      · exact BigStep.assign (emptyState.update "x" 5) "y" (Expr.val 1)

-- Abstract Test
def test10_absState : AbsState := exec test10_stmt AbsState.empty
#eval test10_absState "x"
#eval test10_absState "y"  
