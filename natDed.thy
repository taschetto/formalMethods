theory natDed imports Main
begin
text{* Regras de Dedução Natural no Isabelle. A seta dupla separa
       premissas da conclusão. *}

text{* Premissas \<turnstile> Conclusão (Premissas \<Longrightarrow> Conclusão) *}

thm conjI (* introdução da conjunção *)
thm conjunct1 (* eliminação da conjunção *)
thm conjunct2 (* eliminação da conjunção *)
thm disjI1 (* introdução da disjunção *)
thm disjI2 (* introdução da disjunção *)
thm disjE (* eliminação da disjunção *)
thm impI (* introdução da implicação *)
thm mp (* eliminação da implicação - modus ponens *)
thm notI (* introdução da negação *)
thm notE (* eliminação da negação *)
thm FalseE (* elimnação do Falso - bottom *)
thm ccontr (* contra-clássica - redução ao absurdo *)
thm allI (* introdução do quantificador universal *)
thm spec (* eliminação do quantificador universal *)
thm allE (* eliminação do quantificador universal *)
thm exI (* introdução do quantificador existencial *)
thm exE (* eliminação do quantificador existencial *)
thm refl (* introdução da igualdade - reflexividade *)
thm subst (* eliminação da igualdade *)
thm ssubst (* eliminação da igualdade *)
thm sym (* simetria da igualdade *)
thm trans (* transitividade da igualdade *)

text{* Hello World *}

theorem helloisar01:
assumes prem: "A \<and> B"
shows "B \<and> A"
  proof -
    from prem have d: "A" by (rule conjunct1)
    from prem have    "B" by (rule conjunct2)
    from this and d show "B \<and> A" by (rule conjI)
  qed

theorem helloisar02:
assumes prem: "A \<and> B"
shows "B \<and> A"
  proof (rule conjI)
    from prem show "B" by (rule conjunct2)
    from prem show "A" by (rule conjunct1) 
  qed

text{* Exercício 1 *}

theorem ex1:
assumes prem: "(\<forall>x. F x) \<or> (\<forall>x. G x)"
shows "\<forall>x. F x \<or> G x"
  proof (rule allI) (* \<forall>I *)
    fix x0 (* hyp *)
    show "F x0 \<or> G x0"
      proof (rule disjE[OF prem]) (* \<or>E *)
        assume h1: "\<forall>x. F x"
          from h1 have "F x0" by (rule spec) (* \<forall>E *)
          from this show "F x0 \<or> G x0" by (rule disjI1) (* \<or>I1 *)
        next
        assume h1: "\<forall>x. G x"
          from h1 have "G x0" by (rule spec) (* \<forall>E *)
          from this show "F x0 \<or> G x0" by (rule disjI2) (* \<or>I2 *)
      qed
  qed

text{* Exercício 2 *}
text{* Exercício 3 *}
text{* Exercício 4 *}
text{* Exercício 5 *}

end
