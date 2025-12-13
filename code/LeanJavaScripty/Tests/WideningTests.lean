import LeanJavaScripty.StaticAnalyzer

/-
  Tests for Widening and False Positives in Static Analysis

  These tests demonstrate scenarios where:
  1. Widening is required to ensure termination (unbounded loops)
  2. The abstract interpreter produces false positives (over-approximations)
  3. Path sensitivity limitations cause imprecision

  A "false positive" in static analysis means the analyzer reports a possible
  value that cannot actually occur in any concrete execution.
-/

-- ============================================================================
-- Test W1: Widening Required - Unbounded Counter
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 0;
  while (x < 100) do
    x := x + 1
  ```

  Concrete Result: x = 100 (loop terminates when x reaches 100)

  Abstract Result WITHOUT Widening: Would not terminate (keeps computing
    [0,0] -> [0,1] -> [0,2] -> ... infinitely)

  Abstract Result WITH Widening: x = [0, +∞]
    This is a FALSE POSITIVE: x can never be > 100 in concrete execution,
    but the analyzer says x could be any non-negative value.
-/

def testW1_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._while
      (BoolExp._lt (Expr.var "x") (Expr.val 100))
      (Stmt._assign "x" (Expr.add (Expr.var "x") (Expr.val 1))))

def testW1_absState : AbsState := exec testW1_stmt AbsState.empty
#eval testW1_absState "x"
-- Expected: [0, +∞] - False positive! Concrete max is 100


-- ============================================================================
-- Test W2: Widening - Decrementing Counter
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 100;
  while (x > 0) do
    x := x - 1
  ```

  Concrete Result: x = 0

  Abstract Result: x = [-∞, 100] (widening on lower bound)
    FALSE POSITIVE: x can never be negative, but analyzer allows it.
-/

def testW2_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 100))
    (Stmt._while
      (BoolExp._gt (Expr.var "x") (Expr.val 0))
      (Stmt._assign "x" (Expr.sub (Expr.var "x") (Expr.val 1))))

def testW2_absState : AbsState := exec testW2_stmt AbsState.empty
#eval testW2_absState "x"
-- Expected: [-∞, 100] - False positive! Concrete min is 0


-- ============================================================================
-- Test W3: Path Insensitivity False Positive
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 10;
  if (x > 5) then
    y := 100
  else
    y := 0;
  z := y
  ```

  Concrete Result: y = 100, z = 100 (always takes true branch since x=10)

  Abstract Result: y = join([100,100], [0,0]), z = same
    FALSE POSITIVE: The analyzer doesn't know x=10 implies the true branch,
    so it joins both branches. z could never be 0 in reality.
-/

def testW3_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._seq
      (Stmt._if_else
        (BoolExp._gt (Expr.var "x") (Expr.val 5))
        (Stmt._assign "y" (Expr.val 100))
        (Stmt._assign "y" (Expr.val 0)))
      (Stmt._assign "z" (Expr.var "y")))

def testW3_absState : AbsState := exec testW3_stmt AbsState.empty
#eval testW3_absState "x"  -- [10, 10]
#eval testW3_absState "y"  -- Join of [100,100] and [0,0] - FALSE POSITIVE
#eval testW3_absState "z"  -- Same imprecision propagates


-- ============================================================================
-- Test W4: Correlation Loss - Two Related Variables
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 0;
  y := 0;
  if (x == 0) then
    x := 1;
    y := 1
  else
    skip;
  z := x - y
  ```

  Concrete Result: x=1, y=1, z=0 (always takes true branch)

  Abstract Result: x and y both get joined values, but correlation (x==y) is lost.
    z = x - y could be non-zero according to analyzer.
    FALSE POSITIVE: z is always 0 in concrete execution.
-/

def testW4_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._seq
      (Stmt._assign "y" (Expr.val 0))
      (Stmt._seq
        (Stmt._if_else
          (BoolExp._eq (Expr.var "x") (Expr.val 0))
          (Stmt._seq
            (Stmt._assign "x" (Expr.val 1))
            (Stmt._assign "y" (Expr.val 1)))
          Stmt._skip)
        (Stmt._assign "z" (Expr.sub (Expr.var "x") (Expr.var "y")))))

def testW4_absState : AbsState := exec testW4_stmt AbsState.empty
#eval testW4_absState "x"  -- Should include both 0 and 1
#eval testW4_absState "y"  -- Should include both 0 and 1
#eval testW4_absState "z"  -- FALSE POSITIVE: includes non-zero values


-- ============================================================================
-- Test W5: Nested Loops - Double Widening
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 0;
  y := 0;
  while (x < 10) do
    y := 0;
    while (y < 10) do
      y := y + 1;
    x := x + 1
  ```

  Concrete Result: x = 10, y = 10

  Abstract Result: Both x and y widen to [0, +∞]
    FALSE POSITIVE: Neither can exceed 10 in practice.
-/

def testW5_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._seq
      (Stmt._assign "y" (Expr.val 0))
      (Stmt._while
        (BoolExp._lt (Expr.var "x") (Expr.val 10))
        (Stmt._seq
          (Stmt._assign "y" (Expr.val 0))
          (Stmt._seq
            (Stmt._while
              (BoolExp._lt (Expr.var "y") (Expr.val 10))
              (Stmt._assign "y" (Expr.add (Expr.var "y") (Expr.val 1))))
            (Stmt._assign "x" (Expr.add (Expr.var "x") (Expr.val 1)))))))

def testW5_absState : AbsState := exec testW5_stmt AbsState.empty
#eval testW5_absState "x"  -- [0, +∞] - FALSE POSITIVE (max is 10)
#eval testW5_absState "y"  -- [0, +∞] - FALSE POSITIVE (max is 10)


-- ============================================================================
-- Test W6: Infeasible Path from Conditional
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 5;
  if (x > 10) then
    y := 1
  else
    y := 2;
  z := y
  ```

  Concrete Result: y = 2, z = 2 (false branch always taken since 5 <= 10)

  Abstract Result: y = join([1,1], [2,2])
    FALSE POSITIVE: y can never be 1, but analyzer includes it.
-/

def testW6_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 5))
    (Stmt._seq
      (Stmt._if_else
        (BoolExp._gt (Expr.var "x") (Expr.val 10))
        (Stmt._assign "y" (Expr.val 1))
        (Stmt._assign "y" (Expr.val 2)))
      (Stmt._assign "z" (Expr.var "y")))

def testW6_absState : AbsState := exec testW6_stmt AbsState.empty
#eval testW6_absState "y"  -- Includes 1 - FALSE POSITIVE
#eval testW6_absState "z"  -- Same imprecision


-- ============================================================================
-- Test W7: Loop with Conditional - Precision Loss
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 0;
  y := 0;
  while (x < 5) do
    if (x == 2) then
      y := 100
    else
      y := y + 1;
    x := x + 1
  ```

  Concrete Trace:
    x=0: y=1, x=1: y=2, x=2: y=100, x=3: y=101, x=4: y=102
  Final: x=5, y=102

  Abstract Result: x=[0,+∞], y=[0,+∞]
    FALSE POSITIVE: Loses all precision about the specific value of y.
-/

def testW7_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._seq
      (Stmt._assign "y" (Expr.val 0))
      (Stmt._while
        (BoolExp._lt (Expr.var "x") (Expr.val 5))
        (Stmt._seq
          (Stmt._if_else
            (BoolExp._eq (Expr.var "x") (Expr.val 2))
            (Stmt._assign "y" (Expr.val 100))
            (Stmt._assign "y" (Expr.add (Expr.var "y") (Expr.val 1))))
          (Stmt._assign "x" (Expr.add (Expr.var "x") (Expr.val 1))))))

def testW7_absState : AbsState := exec testW7_stmt AbsState.empty
#eval testW7_absState "x"  -- [0, +∞]
#eval testW7_absState "y"  -- Very imprecise - FALSE POSITIVE range


-- ============================================================================
-- Test W8: Allocation Site Style - Object Identity Loss
-- ============================================================================
/-
  JavaScripty Program (simulated with integers representing "object IDs"):
  ```
  -- Simulating: obj1 = new Object() at line 1
  -- Simulating: obj2 = new Object() at line 2
  obj1 := 1;  -- allocation site 1
  obj2 := 2;  -- allocation site 2
  if (condition) then
    x := obj1
  else
    x := obj2;
  y := x
  ```

  In a normal allocation-site based analyzer:
  - obj1 points to abstract location "alloc_1"
  - obj2 points to abstract location "alloc_2"
  - After the if-else, x could point to either alloc_1 or alloc_2
  - This is a FALSE POSITIVE if the condition is always true/false

  With integers (our simulation):
  - x = join([1,1], [2,2]) even if condition is deterministic
-/

def testW8_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "obj1" (Expr.val 1))
    (Stmt._seq
      (Stmt._assign "obj2" (Expr.val 2))
      (Stmt._seq
        (Stmt._if_else
          BoolExp._true  -- Condition is always true!
          (Stmt._assign "x" (Expr.var "obj1"))
          (Stmt._assign "x" (Expr.var "obj2")))
        (Stmt._assign "y" (Expr.var "x"))))

def testW8_absState : AbsState := exec testW8_stmt AbsState.empty
#eval testW8_absState "obj1"  -- [1, 1]
#eval testW8_absState "obj2"  -- [2, 2]
#eval testW8_absState "x"     -- FALSE POSITIVE: includes 2 even though unreachable
#eval testW8_absState "y"     -- Same imprecision


-- ============================================================================
-- Test W9: Fibonacci-like - Rapid Widening
-- ============================================================================
/-
  JavaScripty Program:
  ```
  a := 1;
  b := 1;
  i := 0;
  while (i < 10) do
    temp := b;
    b := a + b;
    a := temp;
    i := i + 1
  ```

  Concrete: Computes Fibonacci, final b = 89

  Abstract: Very quickly widens to [1, +∞] for both a and b
    FALSE POSITIVE: Loses all precision about Fibonacci sequence.
-/

def testW9_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "a" (Expr.val 1))
    (Stmt._seq
      (Stmt._assign "b" (Expr.val 1))
      (Stmt._seq
        (Stmt._assign "i" (Expr.val 0))
        (Stmt._while
          (BoolExp._lt (Expr.var "i") (Expr.val 10))
          (Stmt._seq
            (Stmt._assign "temp" (Expr.var "b"))
            (Stmt._seq
              (Stmt._assign "b" (Expr.add (Expr.var "a") (Expr.var "b")))
              (Stmt._seq
                (Stmt._assign "a" (Expr.var "temp"))
                (Stmt._assign "i" (Expr.add (Expr.var "i") (Expr.val 1)))))))))

def testW9_absState : AbsState := exec testW9_stmt AbsState.empty
#eval testW9_absState "a"  -- Widened - FALSE POSITIVE
#eval testW9_absState "b"  -- Widened - FALSE POSITIVE
#eval testW9_absState "i"  -- [0, +∞]


-- ============================================================================
-- Test W10: Dead Code - Unreachable Assignment
-- ============================================================================
/-
  JavaScripty Program:
  ```
  x := 10;
  if (false) then
    y := 999
  else
    y := 1;
  z := y
  ```

  Concrete Result: y = 1, z = 1 (true branch is dead code)

  Abstract Result: y = join([999,999], [1,1])
    FALSE POSITIVE: y can never be 999, that code is unreachable.
-/

def testW10_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._seq
      (Stmt._if_else
        BoolExp._false  -- Always false!
        (Stmt._assign "y" (Expr.val 999))
        (Stmt._assign "y" (Expr.val 1)))
      (Stmt._assign "z" (Expr.var "y")))

def testW10_absState : AbsState := exec testW10_stmt AbsState.empty
#eval testW10_absState "y"  -- FALSE POSITIVE: includes 999
#eval testW10_absState "z"  -- Same imprecision
