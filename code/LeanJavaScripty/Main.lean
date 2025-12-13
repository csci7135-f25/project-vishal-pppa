import LeanJavaScripty.StaticAnalyzer

-- ============================================================================
-- All Widening Test Cases
-- ============================================================================

-- W1: Unbounded Counter (x := 0; while x < 100 do x := x + 1)
def testW1_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 0))
    (Stmt._while
      (BoolExp._lt (Expr.var "x") (Expr.val 100))
      (Stmt._assign "x" (Expr.add (Expr.var "x") (Expr.val 1))))

-- W2: Decrementing Counter (x := 100; while x > 0 do x := x - 1)
def testW2_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 100))
    (Stmt._while
      (BoolExp._gt (Expr.var "x") (Expr.val 0))
      (Stmt._assign "x" (Expr.sub (Expr.var "x") (Expr.val 1))))

-- W3: Path Insensitivity (x := 10; if x > 5 then y := 100 else y := 0; z := y)
def testW3_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._seq
      (Stmt._if_else
        (BoolExp._gt (Expr.var "x") (Expr.val 5))
        (Stmt._assign "y" (Expr.val 100))
        (Stmt._assign "y" (Expr.val 0)))
      (Stmt._assign "z" (Expr.var "y")))

-- W4: Correlation Loss (x := 0; y := 0; if x == 0 then x := 1; y := 1 else skip; z := x - y)
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

-- W5: Nested Loops
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

-- W6: Infeasible Path (x := 5; if x > 10 then y := 1 else y := 2; z := y)
def testW6_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 5))
    (Stmt._seq
      (Stmt._if_else
        (BoolExp._gt (Expr.var "x") (Expr.val 10))
        (Stmt._assign "y" (Expr.val 1))
        (Stmt._assign "y" (Expr.val 2)))
      (Stmt._assign "z" (Expr.var "y")))

-- W7: Loop with Conditional
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

-- W8: Allocation Site Style
def testW8_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "obj1" (Expr.val 1))
    (Stmt._seq
      (Stmt._assign "obj2" (Expr.val 2))
      (Stmt._seq
        (Stmt._if_else
          BoolExp._true
          (Stmt._assign "x" (Expr.var "obj1"))
          (Stmt._assign "x" (Expr.var "obj2")))
        (Stmt._assign "y" (Expr.var "x"))))

-- W9: Fibonacci-like
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

-- W10: Dead Code
def testW10_stmt : Stmt :=
  Stmt._seq
    (Stmt._assign "x" (Expr.val 10))
    (Stmt._seq
      (Stmt._if_else
        BoolExp._false
        (Stmt._assign "y" (Expr.val 999))
        (Stmt._assign "y" (Expr.val 1)))
      (Stmt._assign "z" (Expr.var "y")))


def testW11_stmt : Stmt :=
  Stmt._seq
      -- MODULE A: Initialization
      (Stmt._assign "timeout" (Expr.val 1))
      (Stmt._seq
        (Stmt._assign "retries" (Expr.val 0))
        (Stmt._seq

          -- MODULE A: Exponential Backoff (The "Scary" Math)
          -- While timeout < 2000, double it.
          (Stmt._while
            (BoolExp._lt (Expr.var "timeout") (Expr.val 2000))
            (Stmt._assign "timeout" (Expr.add (Expr.var "timeout") (Expr.var "timeout")))
          )

          -- MODULE B: Simple Retry Counter (The Target)
          -- While retries < 5, increment.
          (Stmt._while
            (BoolExp._lt (Expr.var "retries") (Expr.val 5))
            (Stmt._assign "retries" (Expr.add (Expr.var "retries") (Expr.val 1)))
          )
        )
      )

-- ============================================================================
-- Test Runner
-- ============================================================================

structure TestCase where
  name : String
  description : String
  stmt : Stmt
  expectedBehavior : String

def allTests : List TestCase := [
  { name := "W1", description := "Unbounded Counter", stmt := testW1_stmt,
    expectedBehavior := "x should widen to [0, +inf] (concrete max is 100)" },
  { name := "W2", description := "Decrementing Counter", stmt := testW2_stmt,
    expectedBehavior := "x should widen to [-inf, 100] (concrete min is 0)" },
  { name := "W3", description := "Path Insensitivity", stmt := testW3_stmt,
    expectedBehavior := "y,z join both branches (concrete: always 100)" },
  { name := "W4", description := "Correlation Loss", stmt := testW4_stmt,
    expectedBehavior := "z could be non-zero (concrete: always 0)" },
  { name := "W5", description := "Nested Loops", stmt := testW5_stmt,
    expectedBehavior := "x,y widen to [0, +inf] (concrete max is 10)" },
  { name := "W6", description := "Infeasible Path", stmt := testW6_stmt,
    expectedBehavior := "y includes 1 (concrete: always 2)" },
  { name := "W7", description := "Loop with Conditional", stmt := testW7_stmt,
    expectedBehavior := "y very imprecise (concrete: 102)" },
  { name := "W8", description := "Allocation Site Style", stmt := testW8_stmt,
    expectedBehavior := "x includes 2 (concrete: always 1)" },
  { name := "W9", description := "Fibonacci-like", stmt := testW9_stmt,
    expectedBehavior := "a,b widen quickly (concrete: fib sequence)" },
  { name := "W10", description := "Dead Code", stmt := testW10_stmt,
    expectedBehavior := "y includes 999 (concrete: always 1)" },
  { name := "W11",
      description := "Context Pollution & Path Sensitivity",
      stmt := testW11_stmt,
      expectedBehavior := "throughput should be [20, 20] (Linear). debug_metric should be ignored." }
]

def printResult (ts : TrackedState) : IO Unit := do
  for p in ts.vars do
    IO.println s!"    {p.1} = {repr p.2}"

def runPureTest (tc : TestCase) : IO Unit := do
  IO.println s!"  Pure analyzer result:"
  let result := exec tc.stmt AbsState.empty
  let vars := (collectVars tc.stmt).dedup
  for v in vars do
    IO.println s!"    {v} = {repr (result v)}"

def runLLMTest (tc : TestCase) : IO Unit := do
  IO.println s!"  LLM-guided analyzer:"
  try
    let result ← analyzeWithLLM tc.stmt
    printResult result
  catch e =>
    IO.println s!"    Error: {e}"

def runSliceGuidedTest (tc : TestCase) (targetVars : List String) : IO Unit := do
  IO.println s!"  Slice-guided LLM analyzer (targets: {targetVars}):"
  try
    let result ← analyzeWithSliceLLM tc.stmt targetVars
    printResult result
  catch e =>
    IO.println s!"    Error: {e}"

def main : IO Unit := do
  IO.println "============================================================"
  IO.println "       LLM-Guided Static Analysis - Widening Tests"
  IO.println "============================================================"
  IO.println ""
  IO.println "(Make sure Ollama is running: ollama serve)"
  IO.println "(Model required: ollama pull llama3)"
  IO.println ""

  for tc in allTests do
    IO.println "------------------------------------------------------------"
    IO.println s!"Test {tc.name}: {tc.description}"
    IO.println s!"Expected: {tc.expectedBehavior}"
    IO.println ""

    -- Get all variables for this test
    let allVars := (collectVars tc.stmt).dedup

    runPureTest tc
    IO.println ""
    runLLMTest tc
    IO.println ""
    -- Run slice-guided test targeting all variables
    runSliceGuidedTest tc allVars

    IO.println ""

  IO.println "============================================================"
  IO.println "                    Tests Complete"
  IO.println "============================================================"
