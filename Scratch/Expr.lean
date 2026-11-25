import Mathlib

inductive Expr  where
  | Const : ℝ → Expr
  | Plus : Expr → Expr → Expr
  | Mult : Expr → Expr → Expr
  | Inc : Expr → Expr

open Expr

def evalExpr (e:Expr) : ℝ :=
  match e with
    | Const n => n
    | Plus e1 e2 => evalExpr e1 + evalExpr e2
    | Mult e1 e2 => evalExpr e1 * evalExpr e2
    | Inc e1 => 1 + evalExpr e1

def e1 : Expr := Const 2
def e2 : Expr := Const 3
def e3 : Expr := Plus (Inc e1) (Plus (Inc e1) (Inc e2))
def e4 : Expr := Mult e1 e2

theorem const_works : ∀ (n : ℝ), evalExpr (Const n) = n := by
  simp [evalExpr]

theorem plus_works :
  ∀ (x y : ℕ), evalExpr (Plus (Const x) (Const y)) = x + y := by
  simp [evalExpr]

theorem mult_works :
  ∀ (x y : ℕ), evalExpr (Mult (Const x) (Const y)) = x * y := by
  simp [evalExpr]

theorem inc_works_all (e : Expr) :
    evalExpr (Inc e) = evalExpr e + 1 := by
  simp [evalExpr, add_comm]

theorem plus_comm_all (a b : Expr) :
    evalExpr (Plus a b) = evalExpr (Plus b a) := by
  simp [evalExpr, add_comm]

theorem evalExpr_terminates (e : Expr) : ∃ q : ℝ, evalExpr e = q := by
  simp
