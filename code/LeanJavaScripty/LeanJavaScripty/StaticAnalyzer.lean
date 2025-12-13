import LeanJavaScripty.Interval
import LeanJavaScripty.Semantics
import LeanJavaScripty.LLMGuide
import LeanJavaScripty.Slicer

-- Abstract state maps variables to abstract values
abbrev AbsState := String → AbsVal

-- Update abstract state with a new value for variable x
def AbsState.update (s : AbsState) (x : String) (v : AbsVal) : AbsState :=
    fun y => if y == x then v else s y

-- Empty abstract state (all variables map to bottom)
def AbsState.empty : AbsState := fun _ => AbsVal.bottom

-- evalAbs takes an expression and an abstract state and returns an abstract value
def evalAbs (ρ : AbsState) (e: Expr) : AbsVal := match e with
    | Expr.val n => .num (.range (.val n) (.val n))
    | Expr.var x => ρ x
    | Expr.add e1 e2 => match evalAbs ρ e1, evalAbs ρ e2 with
        | .num i1, .num i2 => .num (Interval.add i1 i2)
        | _, _ => .top  -- type mismatch
    | Expr.sub e1 e2 => match evalAbs ρ e1, evalAbs ρ e2 with
        | .num i1, .num i2 => .num (Interval.sub i1 i2)
        | _, _ => .top -- type mismatch

-- Pure widening: widen upper bound to +∞ if increasing, lower bound to -∞ if decreasing
def AbsVal.widen (old new : AbsVal) : AbsVal := match old, new with
    | .num i1, .num i2 => .num (Interval.widen i1 i2)
    | _, _ => .top

-- Check equality of two abstract states for a set of variables
def AbsState.eq_decidable (s1 s2 : AbsState) (vars : List String) : Bool :=
    vars.all (fun x => (s1 x).eq_decidable (s2 x))

-- Pure exec function with automatic widening (for traditional analysis)
partial def exec (stmt : Stmt) (s: AbsState) : AbsState := match stmt with
    | Stmt._skip => s
    | Stmt._assign x e =>
        let val := evalAbs s e
        s.update x val
    | Stmt._seq s1 s2 =>
        let s' := exec s1 s
        exec s2 s'
    | Stmt._if_else _b s1 s2 =>
        -- Join both branches (path insensitive)
        let s_true := exec s1 s
        let s_false := exec s2 s
        fun x => (s_true x).join (s_false x)
    | Stmt._while _b body =>
        let rec loop (oldState : AbsState) (fuel : Nat) : AbsState := match fuel with
        | 0 => oldState  -- Stop if out of fuel
        | Nat.succ fuel' =>
            let bodyState := exec body oldState
            -- Join with old state and apply widening
            let newState : AbsState := fun x =>
                let joined := (oldState x).join (bodyState x)
                (oldState x).widen joined
            -- Widening guarantees convergence in finite steps
            loop newState (fuel' - 1)
        loop s 5  -- 3 iterations is enough for widening to stabilize

-- Pure exec function WITHOUT automatic widening (for LLM-guided analysis)
-- Only pure joins (min/max), no widening - LLM decides what to widen
partial def execNoWiden (stmt : Stmt) (s: AbsState) : AbsState := match stmt with
    | Stmt._skip => s
    | Stmt._assign x e =>
        let val := evalAbs s e
        s.update x val
    | Stmt._seq s1 s2 =>
        let s' := execNoWiden s1 s
        execNoWiden s2 s'
    | Stmt._if_else _b s1 s2 =>
        -- Pure join both branches (path insensitive)
        let s_true := execNoWiden s1 s
        let s_false := execNoWiden s2 s
        fun x => (s_true x).pureJoin (s_false x)
    | Stmt._while _b body =>
        -- Get the variables modified in this loop for fixpoint checking
        let loopVars := getModifiedVars body
        -- Iterate until fixpoint or fuel exhausted
        let rec loop (oldState : AbsState) (fuel : Nat) : AbsState := match fuel with
        | 0 => oldState
        | Nat.succ fuel' =>
            let bodyState := execNoWiden body oldState
            -- Only pure join (min/max), NO widening
            let newState : AbsState := fun x => (oldState x).pureJoin (bodyState x)
            -- Check fixpoint on loop-modified variables
            -- Debug: print oldState and newState (for loopVars) before deciding fixpoint
            let showState (st : AbsState) : String :=
                loopVars.foldl (fun acc x =>
                    let vStr := (repr (st x) |> toString)
                    if acc.isEmpty then s!"{x}: {vStr}" else s!"{acc}, {x}: {vStr}"
                ) ""
            let oldStr := showState oldState
            let newStr := showState newState
            -- Use unsafeRun to print from pure code for debugging
            let _ := (IO.println s!"[FixpointCheck] oldState: {oldStr}")
            let _ := (IO.println s!"[FixpointCheck] newState: {newStr}")

            if AbsState.eq_decidable newState oldState loopVars then
                newState  -- Reached fixpoint
            else
                loop newState (fuel' - 1)
        loop s 5

-- ============================================================================
-- LLM-Guided Analysis (IO wrapper for exec)
-- ============================================================================

-- Track variables and their values for LLM prompt
structure TrackedState where
    vars : List (String × AbsVal)
deriving Repr

def TrackedState.empty : TrackedState := ⟨[]⟩

def TrackedState.update (ts : TrackedState) (x : String) (v : AbsVal) : TrackedState :=
    ⟨(x, v) :: ts.vars.filter (fun p => p.1 != x)⟩

def TrackedState.toAbsState (ts : TrackedState) : AbsState :=
    fun x => match ts.vars.find? (fun p => p.1 == x) with
        | some (_, v) => v
        | none => AbsVal.bottom

def AbsState.toTracked (s : AbsState) (vars : List String) : TrackedState :=
    ⟨vars.map (fun x => (x, s x))⟩

-- Format tracked state as JSON-like string for LLM prompt
def TrackedState.toJson (ts : TrackedState) : String :=
    let inner := ts.vars.foldl (fun acc (x, v) =>
        let valStr := match v with
            | .num (.range lo hi) =>
                let loStr := match lo with | .ninf => "-inf" | .pinf => "+inf" | .val n => toString n
                let hiStr := match hi with | .ninf => "-inf" | .pinf => "+inf" | .val n => toString n
                s!"[{loStr}, {hiStr}]"
            | .bottom => "bottom"
            | .top => "top"
            | _ => repr v |> toString
        if acc.isEmpty then s!"\"{x}\": {valStr}" else s!"{acc}, \"{x}\": {valStr}"
    ) ""
    s!"\{{inner}}"

-- Get list of variable names
def TrackedState.varNames (ts : TrackedState) : List String :=
    ts.vars.map (fun p => p.1)

-- Build prompt for LLM (matching paper Appendix B)
def buildPrompt (ts : TrackedState) (code : String) : String :=
    let varNames := ts.varNames
    let varNamesStr := String.intercalate ", " varNames
    s!"You are part of a static analyzer, where you are responsible for deciding which variables need to be abstracted and which ones can be kept concrete. Your goal is to abstract the necessary variables so that the analysis can converge to a fixpoint, but not to lose too much information through the abstractions. You are only allowed to abstract variable names, not fields. Here are some basic heuristics for when to abstract a variable and when to keep it concrete:
- Abstract a variable if the precise value of the variable is not important for the analysis.
- Abstract a variable if re-executing the program infinitely will cause the variable to increase in size. If re-executing the program does not change the shape or values of the variable, keep it concrete.
- Keep a variable concrete if the current values provided above would not change by re-executing the program.
- Keep a variable concrete if it is used frequently in control flow decisions.
- Whenever possible and if you are unsure, keep variables concrete and do not abstract. We can always abstract later if needed.

I will provide the code and the current state of the variables.
The code is:
```
{code}
```

The variables you can abstract are: {varNamesStr}. The values for the variables in JSON form so far are:
```json
{ts.toJson}
```

What variables should be abstracted? The program will converge when the variables do not change between executions. Please perform enough abstractions for the program to converge but do not abstract too much information. We are about to re-execute the code I provided above with the variables initialized to the values above with no destructive updates to the variables.

Please respond with variable names to abstract, one per line in the format, do not include any extra text, :
ABSTRACT varname upper
ABSTRACT varname lower
or NONE if no abstraction needed.

I repeat - only respond with the variable names to abstract, one per line in the format above, do not include any extra text."

-- Check if string indicates upper/positive infinity widening
def isUpperWiden (s : String) : Bool :=
    s == "upper" || s == "∞" || s == "+∞" || s == "pinf" || s == "+inf" || s == "inf"

-- Check if string indicates lower/negative infinity widening
def isLowerWiden (s : String) : Bool :=
    s == "lower" || s == "-∞" || s == "ninf" || s == "-inf"

-- Parse LLM response and apply widening/abstraction (flexible parsing)
def parseAndApplyWideningWithDebug (response : String) (ts : TrackedState) : TrackedState × List String :=
    let lines := response.splitOn "\n"
    lines.foldl (fun (acc, logs) line =>
        let parts := line.trim.splitOn " "
        match parts with
        -- Accept both WIDEN and ABSTRACT keywords
        | [cmd, var, dir] =>
            if cmd == "WIDEN" || cmd == "ABSTRACT" then
                if isUpperWiden dir then
                    match acc.vars.find? (fun p => p.1 == var) with
                    | some (_, .num (.range lo _)) =>
                        (acc.update var (.num (.range lo .pinf)), logs ++ [s!"  -> Widening {var} upper bound to +inf"])
                    | _ => (acc, logs ++ [s!"  -> Variable {var} not found or not numeric"])
                else if isLowerWiden dir then
                    match acc.vars.find? (fun p => p.1 == var) with
                    | some (_, .num (.range _ hi)) =>
                        (acc.update var (.num (.range .ninf hi)), logs ++ [s!"  -> Widening {var} lower bound to -inf"])
                    | _ => (acc, logs ++ [s!"  -> Variable {var} not found or not numeric"])
                else (acc, logs ++ [s!"  -> Unknown direction '{dir}' for {var}"])
            else (acc, logs)
        -- Also accept just "ABSTRACT varname" (widen both bounds)
        | [cmd, var] =>
            if cmd == "WIDEN" || cmd == "ABSTRACT" then
                match acc.vars.find? (fun p => p.1 == var) with
                | some (_, .num _) =>
                    (acc.update var (.num (.range .ninf .pinf)), logs ++ [s!"  -> Widening {var} both bounds"])
                | _ => (acc, logs ++ [s!"  -> Variable {var} not found or not numeric"])
            else (acc, logs)
        | _ => (acc, logs)
    ) (ts, [])

def parseAndApplyWidening (response : String) (ts : TrackedState) : TrackedState :=
    (parseAndApplyWideningWithDebug response ts).1

-- IO version that can call LLM for guidance
partial def execWithLLM (stmt : Stmt) (ts : TrackedState) (knownVars : List String) : IO TrackedState := do
    match stmt with
    | Stmt._skip => return ts
    | Stmt._assign x e =>
        let s := ts.toAbsState
        let val := evalAbs s e
        return ts.update x val
    | Stmt._seq s1 s2 =>
        let ts' ← execWithLLM s1 ts knownVars
        execWithLLM s2 ts' knownVars
    | Stmt._if_else _b s1 s2 =>
        let ts_true ← execWithLLM s1 ts knownVars
        let ts_false ← execWithLLM s2 ts knownVars
        -- Pure join the two states (no widening)
        let joinedVars := knownVars.map (fun x =>
            let v1 := (ts_true.toAbsState) x
            let v2 := (ts_false.toAbsState) x
            (x, v1.pureJoin v2))
        return ⟨joinedVars⟩
    | Stmt._while _b body =>
        -- Ask LLM for widening guidance
        let prompt := buildPrompt ts (toString (repr body))
        IO.println s!"[LLM-Guide] Analyzing loop..."
        IO.println s!"[LLM-Guide] Current state: {ts.toJson}"
        -- IO.println s!"[LLM-Guide] Prompt:\n{prompt}"

        let response ← callOllama prompt
        IO.println s!"[LLM-Guide] Response:\n{response}"

        -- Apply LLM-suggested widening with debug
        let (widenedTs, logs) := parseAndApplyWideningWithDebug response ts
        for log in logs do
            IO.println log
        IO.println s!"[LLM-Guide] After widening: {widenedTs.toJson}"

        -- Run WITHOUT automatic widening - only LLM-suggested widening is applied
        let finalState := execNoWiden stmt (widenedTs.toAbsState)
        return finalState.toTracked knownVars

-- Collect all variable names from a statement
def collectVars : Stmt → List String
    | Stmt._skip => []
    | Stmt._assign x _ => [x]
    | Stmt._seq s1 s2 => (collectVars s1) ++ (collectVars s2)
    | Stmt._if_else _ s1 s2 => (collectVars s1) ++ (collectVars s2)
    | Stmt._while _ body => collectVars body

-- Remove duplicates from a list
def List.dedup [DecidableEq α] : List α → List α
    | [] => []
    | x :: xs => if xs.contains x then List.dedup xs else x :: List.dedup xs

-- Convenience function to run LLM-guided analysis
def analyzeWithLLM (stmt : Stmt) : IO TrackedState := do
    let vars := (collectVars stmt).dedup
    IO.println s!"[LLM-Guide] Tracking variables: {vars}"
    execWithLLM stmt TrackedState.empty vars

-- ============================================================================
-- Pretty Printer for Stmt (for cleaner LLM prompts)
-- ============================================================================

def Expr.pretty : Expr → String
    | .val n => toString n
    | .var x => x
    | .add e1 e2 => s!"{e1.pretty} + {e2.pretty}"
    | .sub e1 e2 => s!"{e1.pretty} - {e2.pretty}"

def BoolExp.pretty : BoolExp → String
    | ._true => "true"
    | ._false => "false"
    | ._eq e1 e2 => s!"{e1.pretty} == {e2.pretty}"
    | ._lt e1 e2 => s!"{e1.pretty} < {e2.pretty}"
    | ._gt e1 e2 => s!"{e1.pretty} > {e2.pretty}"
    | ._and b1 b2 => s!"{b1.pretty} && {b2.pretty}"
    | ._or b1 b2 => s!"{b1.pretty} || {b2.pretty}"
    | ._not b => s!"!{b.pretty}"

partial def Stmt.pretty (indent : Nat := 0) : Stmt → String
    | ._skip => "  ".pushn ' ' indent ++ "skip"
    | ._assign x e => "  ".pushn ' ' indent ++ s!"{x} := {e.pretty}"
    | ._seq s1 s2 => s!"{s1.pretty indent};\n{s2.pretty indent}"
    | ._if_else b s1 s2 =>
        let ind := "  ".pushn ' ' indent
        s!"{ind}if {b.pretty} then\n{s1.pretty (indent + 2)}\n{ind}else\n{s2.pretty (indent + 2)}"
    | ._while b body =>
        let ind := "  ".pushn ' ' indent
        s!"{ind}while {b.pretty} do\n{body.pretty (indent + 2)}"

-- ============================================================================
-- Slice-Guided LLM Analysis
-- ============================================================================

-- Project TrackedState to only include specific variables
def TrackedState.project (ts : TrackedState) (vars : List String) : TrackedState :=
    ⟨ts.vars.filter (fun p => vars.contains p.1)⟩

-- Build prompt for slice-guided LLM (uses sliced code and projected state)
def buildSliceGuidedPrompt (ts : TrackedState) (slicedCode : Stmt) (targetVars : List String) : String :=
    let varNamesStr := String.intercalate ", " targetVars
    let codeStr := slicedCode.pretty
    s!"You are a precise static analysis oracle. We have performed program slicing to isolate the code relevant to these variables: {varNamesStr}.

The SLICED code (containing ONLY statements that mathematically affect the targets):
```
{codeStr}
```

The current abstract state for these variables:
```json
{ts.toJson}
```

TASK: Identify variables that are diverging (growing indefinitely) inside this loop and require widening to ensure termination.

OUTPUT RULES:

Respond ONLY with a list of directives. Do not include explanations, markdown formatting, or extra text.

Use EXACTLY one of the following formats per line: ABSTRACT <varname> upper ABSTRACT <varname> lower ABSTRACT <varname> both NONE

STRICT CONSTRAINTS:

Do NOT use the word 'infinity'. Use 'upper' or 'lower'.

Do NOT suggest widening variables that are constant or bounded (e.g. retries < 5).

If no variables need widening, output NONE.

Examples:

If x grows towards positive infinity: ABSTRACT x upper

If z fluctuates both ways: ABSTRACT z both"

-- Slice-guided LLM execution for while loops
-- fullProgram: The original top-level program, used for global slicing to capture initialization context
partial def execWithSliceLLM (stmt : Stmt) (ts : TrackedState) (targetVars : List String) (fullProgram : Stmt) : IO TrackedState := do
    match stmt with
    | Stmt._skip => return ts
    | Stmt._assign x e =>
        let s := ts.toAbsState
        let val := evalAbs s e
        return ts.update x val
    | Stmt._seq s1 s2 =>
        -- Pass fullProgram unchanged to child calls
        let ts' ← execWithSliceLLM s1 ts targetVars fullProgram
        execWithSliceLLM s2 ts' targetVars fullProgram
    | Stmt._if_else _b s1 s2 =>
        -- Pass fullProgram unchanged to child calls
        let ts_true ← execWithSliceLLM s1 ts targetVars fullProgram
        let ts_false ← execWithSliceLLM s2 ts targetVars fullProgram
        let joinedVars := targetVars.map (fun x =>
            let v1 := (ts_true.toAbsState) x
            let v2 := (ts_false.toAbsState) x
            (x, v1.pureJoin v2))
        return ⟨joinedVars⟩
    | Stmt._while _b body =>
        -- LOCAL TARGETING FIX: Only target variables that are MODIFIED in this loop
        -- This prevents "context pollution" from unrelated loops
        let loopModifiedVars := getModifiedVars body
        let localTargets := targetVars.filter (fun v => loopModifiedVars.contains v)

        IO.println s!"[Slice-LLM] ---- Loop Analysis ----"
        IO.println s!"[Slice-LLM] Global targets: {targetVars}"
        IO.println s!"[Slice-LLM] Variables modified in this loop: {loopModifiedVars}"
        IO.println s!"[Slice-LLM] Local targets (intersection): {localTargets}"

        -- If no target variables are modified in this loop, just execute without LLM
        if localTargets.isEmpty then
            IO.println s!"[Slice-LLM] No target vars modified in this loop - skipping LLM, using pure exec"
            let finalState := execNoWiden stmt (ts.toAbsState)
            return finalState.toTracked targetVars
        else
            -- GLOBAL SLICING FIX: Slice the FULL PROGRAM for local targets
            -- This captures initialization context (e.g., i := 0) that happens before the loop
            let (slicedFullProgram, deps) := programSlicer fullProgram localTargets
            IO.println s!"[Slice-LLM] Dependencies from global slice: {deps}"
            IO.println s!"[Slice-LLM] Globally sliced program (includes init context):\n{slicedFullProgram.pretty 2}"

            -- Step 2: Project the state to only relevant variables (local targets + deps)
            let relevantVars := (localTargets ++ deps).foldl (fun acc x =>
                if acc.contains x then acc else x :: acc) []
            let projectedTs := ts.project relevantVars
            IO.println s!"[Slice-LLM] Projected state: {projectedTs.toJson}"

            -- Step 3: Build prompt with GLOBALLY sliced code (not just loop body)
            let prompt := buildSliceGuidedPrompt projectedTs slicedFullProgram relevantVars
            IO.println s!"[Slice-LLM] Calling LLM for guidance..."

            let response ← callOllama prompt
            IO.println s!"[Slice-LLM] LLM Response:\n{response}"

            -- Step 4: Apply widening
            let (widenedTs, logs) := parseAndApplyWideningWithDebug response ts
            for log in logs do
                IO.println log
            IO.println s!"[Slice-LLM] After widening: {widenedTs.toJson}"

            -- Step 5: Execute without automatic widening
            let finalState := execNoWiden stmt (widenedTs.toAbsState)
            return finalState.toTracked targetVars

-- Convenience function to run slice-guided LLM analysis
def analyzeWithSliceLLM (stmt : Stmt) (targetVars : List String) : IO TrackedState := do
    -- Compute all variables and dependencies upfront
    let (_, allDeps) := programSlicer stmt targetVars
    let relevantVars := (targetVars ++ allDeps).foldl (fun acc x =>
        if acc.contains x then acc else x :: acc) []

    IO.println s!"[Slice-LLM] =========================================="
    IO.println s!"[Slice-LLM] Target variables: {targetVars}"
    IO.println s!"[Slice-LLM] All dependencies: {allDeps}"
    IO.println s!"[Slice-LLM] Relevant variables: {relevantVars}"
    IO.println s!"[Slice-LLM] Full program preserved for global slicing"
    IO.println s!"[Slice-LLM] =========================================="

    -- Pass the ORIGINAL stmt as fullProgram for global slicing
    -- Each loop will slice fullProgram with its LOCAL targets to get init context
    execWithSliceLLM stmt TrackedState.empty relevantVars stmt
