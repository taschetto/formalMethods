theory Expressions
imports Main
begin

primrec "add"::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add x 0 = x" |
  "add x (Suc y) = Suc (add x y)"

primrec "mult"::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult x 0 = 0" |
  "mult x (Suc y) = add x (mult x y)"

definition "addi"::"int \<Rightarrow> int \<Rightarrow> int" where
  "addi x y = x + y"

definition "multi"::"int \<Rightarrow> int \<Rightarrow> int" where
  "multi x y = x * y"

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

datatype 'a Exp = Const 'a
                | Var nat
                | App "'a binop" "'a Exp" "'a Exp"

term "Var 0"
term "Const (1::int)"
term "Const (1::nat)"
term "App (add) (Var 0) (Const (1::nat))"
term "App (mult) (Var 0) (Const (1::nat))"

primrec eval :: "'a Exp \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
    "eval (Const b) env = b" |
    "eval (Var x) env = env x" |
    "eval (App f e1 e2) env = (f (eval e1 env) (eval e2 env))"

value "eval (App add (Var 0) (Const 1)) (%x::nat. 2)"
value "eval (App mult (Var 0) (Const 3)) (%x::nat. 2)"
value "eval (App addi (Var 0) (Const 1)) (%x::nat. 2)"
value "eval (App multi (Var 0) (Const 3)) (%x::nat. 2)"

value "eval (App multi (App addi (Var 0) (Const 2)) (Const 3)) (%x::nat. 2)"

datatype 'a Instr = IConst 'a
                  | ILoad nat
                  | IApp "'a binop"

primrec compile :: "'a Exp \<Rightarrow> 'a Instr list" where
  "compile (Const b) = [IConst b]" |
  "compile (Var x) = [ILoad x]" |
  "compile (App f e1 e2) = (compile e2) @ (compile e1 ) @ [IApp f]"

primrec exec :: "'a Instr list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "exec [] env vs = vs" |
  "exec (i # is) env vs = (case i of
      IConst v \<Rightarrow> exec is env (v # vs)
    | ILoad x  \<Rightarrow> exec is env ((env x)#vs) 
    | IApp f   \<Rightarrow> exec is env ((f (hd vs) (hd (tl vs)))#(tl(tl vs))))"

(*
  Devo provar que o compilador funciona, ou seja:
  exec (compile e) env [] = [eval e env]
*)

theorem "\<forall>s. exec (compile exp) env s = (eval exp env) # s"
proof (induct exp)
  fix v
  show "\<forall>s. exec (compile (Const v)) env s = (eval (Const v) env) # s" by simp
next
  fix x
  show "\<forall>s. exec (compile (Var x)) env s = (eval (Var x) env) # s" by simp
next
  fix f e1 e2
  
