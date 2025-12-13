import Lean
import Std

abbrev Var := String

-- using Int for simplicity; can be, and will be,  extended to other types
abbrev Val := Int

inductive Expr where
  | val : Val → Expr
  | var : Var → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
deriving Repr, DecidableEq

inductive BoolExp where
  | _true : BoolExp
  | _false : BoolExp
  | _eq : Expr → Expr → BoolExp
  | _lt : Expr → Expr → BoolExp
  | _gt : Expr → Expr → BoolExp
  | _and : BoolExp → BoolExp → BoolExp
  | _or : BoolExp → BoolExp → BoolExp
  | _not : BoolExp → BoolExp
deriving Repr, DecidableEq

inductive Stmt where
  | _skip: Stmt
  | _assign: Var → Expr → Stmt
  | _seq: Stmt → Stmt → Stmt
  | _if_else: BoolExp → Stmt → Stmt → Stmt
  | _while: BoolExp → Stmt → Stmt
deriving Repr, DecidableEq
