import LeanJavaScripty.Semantics
import LeanJavaScripty.Syntax

import Lean.Data.PersistentHashSet

abbrev VarSet := List String

def VarSet.union (s1 s2 : VarSet) : VarSet :=
  (s1 ++ s2).foldl (fun acc x => if x ∈ acc then acc else x :: acc) []

def VarSet.remove (s : VarSet) (v : String) : VarSet :=
  s.filter (fun x => x ≠ v)

def getExprUsesVar (e : Expr) : VarSet := match e with
  | .val _ => []
  | .var x => [x]
  | .add e1 e2 => (getExprUsesVar e1).union (getExprUsesVar e2)
  | .sub e1 e2 => (getExprUsesVar e1).union (getExprUsesVar e2)


def getBoolExpUsesVar (b : BoolExp) : VarSet := match b with
  | ._true => []
  | ._false => []
  | ._eq e1 e2 => (getExprUsesVar e1).union (getExprUsesVar e2)
  | ._lt e1 e2 => (getExprUsesVar e1).union (getExprUsesVar e2)
  | ._gt e1 e2 => (getExprUsesVar e1).union (getExprUsesVar e2)
  | ._and b1 b2 => (getBoolExpUsesVar b1).union (getBoolExpUsesVar b2)
  | ._or b1 b2 => (getBoolExpUsesVar b1).union (getBoolExpUsesVar b2)
  | ._not b1 => getBoolExpUsesVar b1

-- Helper: Find all variables MODIFIED by a statement (LHS of assignments)
-- This is used for "local targeting" - only summarize vars that change in a loop
def getModifiedVars (stmt : Stmt) : VarSet := match stmt with
  | Stmt._skip => []
  | Stmt._assign x _ => [x]
  | Stmt._seq s1 s2 => (getModifiedVars s1).union (getModifiedVars s2)
  | Stmt._if_else _ s1 s2 => (getModifiedVars s1).union (getModifiedVars s2)
  | Stmt._while _ body => getModifiedVars body

-- Intersection of two VarSets
def VarSet.intersect (s1 s2 : VarSet) : VarSet :=
  s1.filter (fun x => s2.contains x)

partial def programSlicer (stmt : Stmt) (rv : VarSet) : (Stmt × VarSet) := match stmt with
  | Stmt._skip => (Stmt._skip, rv)

  -- Data Dependency
  | Stmt._assign x e =>
      if x ∈ rv then
        let newRv := (getExprUsesVar e).union (rv.remove x)
        (stmt, newRv)
      else
        (Stmt._skip, rv)
  | Stmt._seq s1 s2 =>
      let (s2', rv2) := programSlicer s2 rv
      let (s1', rv1) := programSlicer s1 rv2

      if s1' = Stmt._skip then
        (s2', rv1)
      else if s2' = Stmt._skip then
        (s1', rv1)
      else
        (Stmt._seq s1' s2', rv1)

  -- Control Dependency
  | Stmt._if_else b s1 s2 =>
      let (s1', rv1) := programSlicer s1 rv
      let (s2', rv2) := programSlicer s2 rv

      if s1' = Stmt._skip && s2' = Stmt._skip then
        (Stmt._skip, rv)
      else
        let newRv := (getBoolExpUsesVar b).union (rv1.union rv2)
        (Stmt._if_else b s1' s2', newRv)

  | Stmt._while b body =>

      let rec fixpoint (rv: VarSet) (fuel: Nat): (Stmt × VarSet) := match fuel with
        | 0 => (stmt, rv)
        | n + 1 =>
            let (body', rvBody) := programSlicer body rv

            if body' = Stmt._skip then
              (Stmt._skip, rv)
            else
              let newRv := (getBoolExpUsesVar b).union rvBody
              if newRv = rv then
                (Stmt._while b body', newRv)
              else
                fixpoint newRv n
      fixpoint rv 10



-- Couple of Test Cases
def testProgram : Stmt :=
  Stmt._seq
    (Stmt._assign "sum" (Expr.val 0))
    (Stmt._seq
       (Stmt._assign "i" (Expr.val 0))
       (Stmt._seq
          -- Irrelevant assignment
          (Stmt._assign "debug_log" (Expr.val 999))
          (Stmt._while (BoolExp._lt (Expr.var "i") (Expr.val 10))
             (Stmt._seq
                (Stmt._assign "sum" (Expr.add (Expr.var "sum") (Expr.var "i")))
                (Stmt._assign "i" (Expr.add (Expr.var "i") (Expr.val 1)))
             )
          )
       )
    )

-- We only care about "sum" at the end
def targetVars : VarSet := ["sum"]

-- Test function for slicer (not main to avoid conflicts)
def testSlicer : IO Unit := do
  let (slicedCode, finalDeps) := programSlicer testProgram targetVars
  IO.println s!"Original Relevant Vars: {targetVars}"
  IO.println s!"Final Dependencies: {finalDeps}"
  IO.println s!"Sliced Code: {repr slicedCode}"

-- EXPECTED OUTPUT:
-- The assignment `debug_log := 999` should be replaced by `_skip`.
-- `sum`, `i` should be kept.
