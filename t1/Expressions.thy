theory Expressions
imports Main
begin

(* Definição de algumas primitivas binárias sobre naturais e inteiros *)
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

(* Definição de um tipo indutivo para expressões sobre um tipo genérico *)
datatype 'a Exp = Const 'a
                | Var nat
                | App "'a \<Rightarrow> 'a \<Rightarrow> 'a" "'a Exp" "'a Exp"

(* Alguns termos da linguagem de expressões *)
term "Var 0"
term "Const (1::int)"
term "Const (1::nat)"
term "App add (Var 0) (Const (1::nat))"
term "App mult (Var 0) (Const (1::nat))"
term "App addi (Var 0) (App multi (Const (1::int)) (Var 1))"

(* Primitiva recursiva que efetua a valoração de uma expressão *)
primrec eval :: "'a Exp \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
    "eval (Const b) env = b" |
    "eval (Var x) env = env x" |
    "eval (App f e1 e2) env = (f (eval e1 env) (eval e2 env))"

value "eval (App add (Var 0) (Const 1)) (%x::nat. 2)"
value "eval (App mult (Var 0) (Const (1::nat))) (%x::nat. 2)"
value "eval (App addi (Var 0) (App multi (Const (1::int)) (Const (4::int)))) (%x::nat. 2)"
value "eval (App multi (App addi (Var 0) (Const 2)) (Const 3)) (%x::nat. 2)"

(* Definição de um tipo indutivo para instruções em uma pilha *)
datatype 'a Instr = IConst 'a
                  | ILoad nat
                  | IApp "'a \<Rightarrow> 'a \<Rightarrow> 'a"

(* Definição de uma primitiva recursiva que compila uma expressão em uma lista de instruções *)
primrec compile :: "'a Exp \<Rightarrow> 'a Instr list" where
  "compile (Const b) = [IConst b]" |
  "compile (Var x) = [ILoad x]" |
  "compile (App f e1 e2) = (compile e2) @ (compile e1 ) @ [IApp f]"

value "compile (App add (Var 0) (Const 1))"
value "compile (App multi (Var 0) (Const (1::int)))"
value "compile (App addi (Var 0) (App multi (Const (1::int)) (Const (4::int))))"

(* Primitiva recursiva que executa uma lista de instruções *)
primrec exec :: "'a Instr list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "exec [] env vs = vs" |
  "exec (i # is) env vs = (case i of
      IConst v \<Rightarrow> exec is env (v # vs)
    | ILoad x  \<Rightarrow> exec is env ((env x) # vs) 
    | IApp f   \<Rightarrow> exec is env ((f (hd vs) (hd (tl vs))) # (tl (tl vs))))"

value "exec [] (%x::nat. 1) []"
value "exec (compile (App add (Var 0) (Const 1))) (%x::nat. 1) []"
value "exec (compile (App multi (Var 0) (Const (1::int)))) (%x::nat. 1) []"
value "exec (compile (App addi (Var 0) (App multi (Const (1::int)) (Const (4::int))))) (%x::nat. 1) []"

(* Prova da correture do compilador *)
(* Extraída de "Practical Theorem Proving with Isabelle/Isar Lecture Notes", por Jeremy Siek *)

(* Lema auxiliar  *)
lemma exec_app [rule_format]:
  "\<forall>vs. exec (xs@ys) s vs = exec ys s (exec xs s vs)"
  apply(induct xs, simp, auto)
  apply(case_tac a, auto) done

(* Prova do teorema *)
theorem "\<forall>vs. exec (compile e) env vs = (eval e env) # vs"
  proof (induct e)
    fix v
    show "\<forall>vs. exec (compile (Const v)) env vs = (eval (Const v) env) # vs" by simp
    next
      fix x
      show "\<forall>vs. exec (compile (Var x)) env vs = eval (Var x) env # vs" by simp
      next
        fix f e1 e2
          assume IH1: "\<forall>vs. exec (compile e1) env vs = eval e1 env # vs"
          and IH2: "\<forall>vs. exec (compile e2) env vs = eval e2 env # vs"
          show "\<forall>vs. exec (compile (App f e1 e2)) env vs = eval (App f e1 e2) env # vs"
          proof
            fix vs
              have "exec (compile (App f e1 e2)) env vs = exec ((compile e2) @ (compile e1) @ [IApp f ]) env vs" by simp also
              have "\<dots> = exec ((compile e1) @ [IApp f ]) env (exec (compile e2) env vs)" using exec_app by blast also
              have "\<dots> = exec [IApp f] env (exec (compile e1) env (exec (compile e2) env vs))" using exec_app by blast also
              have "\<dots> = exec [IApp f ] env (exec (compile e1) env (eval e2 env # vs))"  using IH2 by simp also
              have "\<dots> = exec [IApp f ] env ((eval e1 env) # (eval e2 env # vs))" using IH1 by simp also
              have "\<dots> = (f (eval e1 env) (eval e2 env))#vs" by simp also
              have "\<dots> = eval (App f e1 e2) env # vs" by simp
              finally
                show "exec (compile (App f e1 e2)) env vs = eval (App f e1 e2) env # vs" by blast
          qed
  qed
