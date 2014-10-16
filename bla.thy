theory bla
imports Main
begin

(*
  min : read \<Rightarrow> real \<Rightarrow> real
    pre: true
    post: (min x y = x \<or> min x y = y) \<and> (min x y \<le> x \<and> min x y \<le> y)

Questões:

  1) Qual o problema de assumir como pós-condição...

    a) somente (min x y = x \<or> min x y = y)
    b) somente (min x y \<le> x \<and> min x y \<le> y)
    c) para cada caso, escreva programas que satisfazem as respectivas pós-condições
       e não fazem o esperado


Exemplo: um programa que calcula a raiz 4\<ordfeminine> de um número \<RR>. Assume-se a existência da função auxiliar:

  sqrt x : real \<Rightarrow> real
    pre: x \<ge> 0
    post: (sqrt x)^2 = x

      ---

      fourthRoot x : real \<Rightarrow> real
        pre: x \<ge> 0
        post: (fourthRoot x)^4 = x

        fourthRoot x : real \<Rightarrow> real, onde
          let y = sqrt x
          in
            if y \<ge> 0
            then sqrt y
            else sqrt (-y)

  Proposição:

    \<forall>x:real. (x \<ge> 0 \<longrightarrow> sqrt x \<ge> 0) \<longrightarrow> (\<forall>x:real. (fourthRoot x)^4 == x)
*)
end
