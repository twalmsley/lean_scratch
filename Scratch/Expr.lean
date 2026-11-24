import Mathlib

inductive Expr  where
  | Const : ℚ → Expr
  | Plus : Expr → Expr → Expr
  | Inc : Expr → Expr

open Expr

def evalExpr (e:Expr) : ℚ :=
  match e with
    | Const n => n
    | Plus e1 e2 => evalExpr e1 + evalExpr e2
    | Inc e1 => 1 + evalExpr e1

def e1 : Expr := Const 2
def e2 : Expr := Const 3
def e3 : Expr := Plus (Inc e1) (Plus (Inc e1) (Inc e2))

#eval evalExpr e3

theorem const_works : ∀ (n : ℚ), evalExpr (Const n) = n := by
  unfold evalExpr
  simp

theorem plus_works :
  ∀ (x y : ℚ ), evalExpr (Plus (Const x) (Const y)) = x + y := by
  simp [evalExpr]

theorem inc_works :
  ∀ (x : ℚ), evalExpr (Inc (Const x)) = x + 1 := by
  simp [evalExpr]
  apply add_comm
