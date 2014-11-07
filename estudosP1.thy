theory estudosP1
imports Main
begin
(* Conjunto Indutivo \<nat>

                                    x0:Nat
                                    P(x0)     hI
    \<dots>                              \<dots>
    \<dots>                              \<dots>
    \<dots>                              \<dots>
    P(zero)                         P(suc x0)
    ------------------------------------------------- Ind Nat
                         \<forall>n:Nat. P(n)
*)

datatype Nat = Z | suc Nat

(* Primitiva Recursiva add: \<nat> \<Rightarrow> \<nat> \<Rightarrow> \<nat>

  add: \<nat> \<Rightarrow> \<nat> \<Rightarrow> \<nat>, onde
    add x 0 = x                    (add01)
    add x (suc y) = suc (add x y)  (add02)
*)

primrec add::"Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  add01: "add x Z = x" |
  add02: "add x (suc y) = suc (add x y)"

value "add Z (suc (suc Z))"
value "add (suc Z) (suc (suc (suc Z)))"

(* Provas por Indução Estrutural

  add 0 (suc (suc 0)) = suc (add 0 (suc 0))   (by add02, [x:=0, y:=suc 0])
                      = suc (suc (add 0 0))   (by add02, [x:=0, y:=0])
                      = suc (suc 0)           (by add01, [x:=0])
                      = 2                     (por definição de suc)

  add (suc 0) (suc (suc (suc 0))) = suc (add (suc 0) (suc (suc 0)))  (by add02, [x:=suc 0, y:=suc (suc 0)])
                                  = suc (suc (add (suc 0) (suc 0)))  (by add02, [x:=suc 0, y:=suc 0])
                                  = suc (suc (suc (add (suc 0) 0)))  (by add02, [x:=suc 0, y:=0])
                                  = suc (suc (suc (suc 0)))          (by add01, [x:=suc 0])
                                  = 4                                (por definição de suc)
*)

(*
  Provar os teoremas:

    Th-add-01: \<forall>x:\<nat>. \<forall>y:\<nat>. \<forall>z:\<nat>. add x (add y z) = add (add x y) z
    Th-add-02: \<forall>x:\<nat>. \<forall>y:\<nat>. add x y = add y x
    Th-add-03: \<forall>x:\<nat>. add 0 x = x
    Th-add-04: \<forall>x:\<nat>. \<forall>y:\<nat>. add x (suc y) = add (suc x) y
    Th-add-05: \<forall>x:\<nat>. \<forall>y:\<nat>. add (suc x) y = suc (add x y)
*)

(*
1) Provando Th-add-01 (associatividade da função add)
  1.1) Formalização da propriedade

    P \<triangleq> \<forall>x:\<nat>. \<forall>y:\<nat>. \<forall>z:\<nat>. add x (add y z) = add (add x y) z

  1.2) Escolha da variável indutiva

    P(n) \<triangleq> \<forall>x:\<nat>. \<forall>y:\<nat>. add x (add y n) = add (add x y) n

    Logo, temos que provar que \<forall>n:\<nat>. P(n).

  1.2.1) Prova do caso base P(0)
  
    Temos que mostrar que:
      \<forall>x:\<nat>. \<forall>y:\<nat>. add x (add y 0) = add (add x y) 0
  
    Sejam x0 e y0 valores arbitrários em \<nat>, então é suficiente mostrar que:
      add x0 (add y0 0) = add (add x0 y0) 0
  
    Agora, veja que:
  
      add x0 (add y0 0)
        = add x0 y0           (by add01, [x:=y0])
        = add (add x0 y0) 0   (by add01, [x:=add x0 y0])
  
        q.e.d.
  
  1.2.2) Prova do caso indutivo P(x0) \<longrightarrow> P(suc x0)
  
    Seja x0 um valor arbitrário em \<nat>, assumimos como hipótese de indução:
      \<forall>x:\<nat>. \<forall>y:\<nat>. add x (add y x0) = add (add x y) x0
  
    Temos que mostrar que:
      \<forall>x:\<nat>. \<forall>y:\<nat>. add x (add y (suc x0)) = add (add x y) (suc x0)
  
    Sejam x1 e y1 valores arbitrários em \<nat>. Logo, é suficiente mostrar que:
      add x1 (add y1 (suc x0)) = add (add x1 y1) (suc x0)
  
    Agora, veja que:
  
      add x1 (add y1 (suc x0))
        = add x1 (suc (add y1 x0))        (by add02, [x:=y1, y:=suc x0])
        = suc (add x1 (add y1 x0))        (by add02, [x:=x1, y:=add y1 x0])
        = suc (add (add x1 y1) x0)        (by HI, [x:=x1, y:=y1])
        = add (add x1 y1) (suc x0)        (by add02, [x:=(add x1 y1), y:=x0])
  
        q.e.d
*)

theorem thadd01: "\<forall>x. \<forall>y. add x (add y n) = add (add x y) n"
  proof (induction n)
    show "\<forall>x. \<forall>y. add x (add y Z) = add (add x y) Z"
      proof (rule allI, rule allI)
        fix x0::Nat and y0::Nat
          have "add x0 (add y0 Z) = add x0 y0" by (simp only:add01)
          also have "add x0 y0 = add (add x0 y0) Z" by (simp only:add01)
          finally show "add x0 (add y0 Z) = add (add x0 y0) Z" by this
      qed
      next
        fix x0::Nat
        assume IH:"\<forall>x. \<forall>y. add x (add y x0) = add (add x y) x0"
        show "\<forall>x. \<forall>y. add x (add y (suc x0)) = add (add x y) (suc x0)"
        proof (rule allI, rule allI)
          fix x1::Nat and y1::Nat
          have "add x1 (add y1 (suc x0)) = add x1 (suc (add y1 x0))" by (simp only:add02)
          also have "add x1 (suc (add y1 x0)) = suc (add x1 (add y1 x0))" by (simp only:add02)
          also have "suc (add x1 (add y1 x0)) = suc (add (add x1 y1) x0)" by (simp only:IH)
          also have "suc (add (add x1 y1) x0) = add (add x1 y1) (suc x0)" by (simp only:add02)
          finally show "add x1 (add y1 (suc x0)) = add (add x1 y1) (suc x0)" by this
        qed
  qed

(*
2) Provando Th-add-03 (0 é neutro à esquerda)
  2.1) Formalização da propriedade

    P \<triangleq> \<forall>x:\<nat>. add 0 x = x

  2.2) Escolha da variável indutiva

    P(n) \<triangleq> add 0 n = n

    Logo, temos que provar que \<forall>n:\<nat>. P(n).

  2.2.1) Prova do caso base P(0)

    Temos que mostrar que:
      add 0 0 = 0

    Agora veja que:

      add 0 0
        = 0     (by add01, [x:=0])

        q.e.d.

  2.2.2) Prova do caso indutivo P(x0) \<longrightarrow> P(suc x0)
  
    Seja x0 um valor arbitrário em \<nat>, assumimos como hipótese de indução:
      add 0 x0 = x0

    Temos que mostrar que:
      add 0 (suc x0) = suc x0

    Agora, veja que:
      
      add 0 (suc x0)
        = suc (add 0 x0)            (by add02, [x:=0, y:=x0])
        = suc x0                    (by HI, [x0:=x0])

        q.e.d.
*)

theorem thadd03: "add Z n = n"
  proof (induction n)
    show "add Z Z = Z" by (simp only:add01)
    next
     fix x0::Nat
      assume IH:"add Z x0 = x0"
      show "add Z (suc x0) = suc x0"
      proof -
        have "add Z (suc x0) = suc (add Z x0)" by (simp only:add02) also
        have "suc (add Z x0) = suc x0" by (simp only:IH)
        finally show "add Z (suc x0) = suc x0" by this
      qed
  qed

(*
3) Provando Th-add-02 (comutatividade da função add)
  3.1) Formalização da propriedade

    P \<triangleq> \<forall>x:\<nat>. \<forall>y:\<nat>. add x y = add y x

  3.2) Escolha da variável indutiva

    P(n) \<triangleq> \<forall>x:\<nat>. add x n = add n x

    Logo, temos que provar que \<forall>n:\<nat>. P(n).

  3.2.1) Prova do caso base P(0)
  
    Temos que mostrar que:
      \<forall>x:\<nat>. add x 0 = add 0 x
  
    Seja x0 um valor arbitrário em \<nat>, então é suficiente mostrar que:
      add x0 0 = add 0 x0
  
    Agora, veja que:
  
      add x0 0
        = x0          (by add01, [x:=x0])
        = add 0 x0    (by Th-add-03, [x:=x0])
  
        q.e.d.

  3.2.2.) Prova do caso indutivo P(x0) \<longrightarrow> P(suc x0)

    Seja x0 um valor arbitrário em \<nat>, assumimos como hipótese de indução:
      \<forall>x:\<nat>. add x x0 = add x0 x

    Temos que mostrar que:
      \<forall>x:\<nat>. add x (suc x0) = add (suc x0) x

    Seja x1 um valor arbitrário em \<nat>, é suficiente provar que:
      add x1 (suc x0) = add (suc x0) x1

    Agora, veja que:
      
      add x1 (suc x0)
        = add (suc x0) x1           (by HI, x:=x1, x0=x0])

      add x1 (suc x0) 
      = suc (add x1 x0).   (by add02, x:=x1, y:=x0)
      = suc (add x0 x1).   (by IH, allE)
      = add (x0 (suc x1))  (by add02, x:=x0, y:=x1)
      = add (suc x0) x1.   (by Th-add04, allE, x:=x0, y:=x1

        q.e.d.
*)

theorem thadd02: "\<forall>x. add x n = add n x"
  proof (induction n)
    show "\<forall>x. add x Z = add Z x"
      proof (rule allI)
        fix x0::Nat
        have "add x0 Z = x0" by (simp only:add01) also
        have "x0 = add Z x0" by (simp only:thadd03)
        finally show "add x0 Z = add Z x0" by this
      qed
      next
        fix x0::Nat
        assume IH:"\<forall>x. add x x0 = add x0 x"
        show "\<forall>x. add x (suc x0) = add (suc x0) x"
        proof (rule allI)
          fix x1::Nat
          have "add x1 (suc x0) = suc (add x1 x0)" by (simp only:add02) also
          have "suc (add x1 x0) = suc (add x0 x1)" by (simp only:IH) also
          have "suc (add x0 x1) = add (suc x0) x1" by (simp only:thadd05)
          finally show "add x1 (suc x0) = add (suc x0) x1" by this
        qed
  qed

(*
4) Provando Th-add-04
  4.1) Formalização da propriedade

    P \<triangleq> \<forall>x:\<nat>. \<forall>y:\<nat>. add x (suc y) = add (suc x) y

  4.2) Escolha da variável indutiva

    P(n) \<triangleq> \<forall>x:\<nat>. add x (suc n) = add (suc x) n

    Logo, temos que provar que \<forall>n:\<nat>. P(n).

  4.2.1) Prova do caso base P(0)
  
    Temos que mostrar que:
      P(0) \<triangleq> \<forall>x:\<nat>. add x (suc 0) = add (suc x) 0
  
    Seja x0 um valor arbitrário em \<nat>, então é suficiente mostrar que:
      add x0 (suc 0) = add (suc x0) 0
  
    Agora, veja que:
  
      add x0 (suc 0)
        = suc (add x0 0)          (by add02, [x:=x0, y:=0])
        = suc (add 0 x0)          (by th-add-02, [x:=x0, y:=0])
        = add 0 (suc x0)          (by add02, [x:=0, y:=x0])
        = add (suc x0) 0          (by th-add-02, [x:=suc x0, y:=0])
  
        q.e.d.

  4.2.2.) Prova do caso indutivo P(x0) \<longrightarrow> P(suc x0)

    Seja x0 um valor arbitrário em \<nat>, assumimos como hipótese de indução:
      P(x0) \<triangleq> \<forall>x:\<nat>. add x (suc x0) = add (suc x) x0

    Temos que mostrar que:
      P(suc x0) \<triangleq> \<forall>x:\<nat>. add x (suc (suc x0)) = add (suc x) (suc x0)

    Seja x1 um valor arbitrário em \<nat>, é suficiente provar que:
      add x1 (suc (suc x0)) = add (suc x1) (suc x0)

    Agora, veja que:
      
      add x1 (suc (suc x0))
        = suc (add x1 (suc x0))          (by add02, [x:=x1, y:=suc x0])
        = suc (add (suc x1) x0)          (by HI, [x:=x1, x0:=x0])
        = add (suc x1) (suc x0)          (by add02, [x:=suc x1, y:=x0])

        q.e.d.
*)

theorem thadd04: "\<forall>x. add x (suc n) = add (suc x) n"
  proof (induction n)
    show "\<forall>x. add x (suc Z) = add (suc x) Z"
      proof (rule allI)
        fix x0::Nat
        have "add x0 (suc Z) = suc (add x0 Z)" by (simp only:add02)
        also have "suc (add x0 Z) = suc (add Z x0)" by (simp only:thadd02)
        also have "suc (add Z x0) = add Z (suc x0)" by (simp only:add02)
        also have "add Z (suc x0) = add (suc x0) Z" by (simp only:thadd02)
        finally show "add x0 (suc Z) = add (suc x0) Z" by this
      qed
      next
        fix x0::Nat
        assume IH:"\<forall>x. add x (suc x0) = add (suc x) x0"
        show "\<forall>x. add x (suc (suc x0)) = add (suc x) (suc x0)"
        proof (rule allI)
          fix x1::Nat
          have "add x1 (suc (suc x0)) = suc (add x1 (suc x0))" by (simp only:add02) also
          have "suc (add x1 (suc x0)) = suc (add (suc x1) x0)" by (simp only:IH) also 
          have "suc (add (suc x1) x0) = add (suc x1) (suc x0)" by (simp only:add02)
          finally show "add x1 (suc (suc x0)) = add (suc x1) (suc x0)" by this
        qed
  qed

(*
5) Provando Th-add-05
  5.1) Formalização da propriedade

    P \<triangleq> \<forall>x:\<nat>. \<forall>y:\<nat>. add (suc x) y = suc (add x y)

  5.2) Escolha da variável indutiva

    P(n) \<triangleq> \<forall>x:\<nat>. add (suc x) n = suc (add x n)

    Logo, temos que provar que \<forall>n:\<nat>. P(n).

  5.2.1) Prova do caso base P(0)
  
    Temos que mostrar que:
      P(0) \<triangleq> \<forall>x:\<nat>. add (suc x) 0 = suc (add x 0)
  
    Seja x0 um valor arbitrário em \<nat>, então é suficiente mostrar que:
      add (suc x0) 0 = suc (add x0 0)
  
    Agora, veja que:
  
      add (suc x0) 0
        = add 0 (suc x0)          (by th-add-02, [x:=suc x0, y:=0])
        = suc (add 0 x0)          (by add02, [x:=0, y:=x0])
        = suc (add x0 0)          (by th-add-02, [x:=x0, y:=0]
  
        q.e.d.

  5.2.2.) Prova do caso indutivo P(x0) \<longrightarrow> P(suc x0)

    Seja x0 um valor arbitrário em \<nat>, assumimos como hipótese de indução:
      P(x0) \<triangleq> \<forall>x:\<nat>. add (suc x) x0 = suc (add x x0)

    Temos que mostrar que:
      P(suc x0) \<triangleq> \<forall>x:\<nat>. add (suc x) (suc x0) = suc (add x (suc x0))

    Seja x1 um valor arbitrário em \<nat>, é suficiente provar que:
      add (suc x1) (suc x0) = suc (add x1 (suc x0))

    Agora, veja que:
      
      add (suc x1) (suc x0)
        = suc (add (suc x1) x0)          (by add02, [x:=suc x1, y:=x0])
        = suc (add x1 (suc x0))          (by th-add-04, [x:=x1, y:=x0])

        q.e.d.
*)

theorem thadd05: "\<forall>x. add (suc x) n = suc (add x n)"
  proof (induction n)
    show "\<forall>x. add (suc x) Z = suc (add x Z)"
    proof (rule allI)
      fix x0::Nat
      have "add (suc x0) Z = add Z (suc x0)" by (simp only:thadd02) also
      have "add Z (suc x0) = suc (add Z x0)" by (simp only:add02) also
      have "suc (add Z x0) = suc (add x0 Z)" by (simp only:thadd02)
      finally show "add (suc x0) Z = suc (add x0 Z)" by this
    qed
    next
      fix x0::Nat
      assume IH: "\<forall>x. add (suc x) x0 = suc (add x x0)"
      show "\<forall>x. add (suc x) (suc x0) = suc (add x (suc x0))"
      proof (rule allI)
        fix x1::Nat
        have "add (suc x1) (suc x0) = suc (add (suc x1) x0)" by (simp only:add02) also
        have "suc (add (suc x1) x0) = suc (add x1 (suc x0))" by (simp only:thadd04)
        finally show "add (suc x1) (suc x0) = suc (add x1 (suc x0))" by this
      qed
  qed

primrec mult::"Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  mult01: "mult x Z = Z" |
  mult02: "mult x (suc y) = add x (mult x y)"

value "mult Z (suc (suc Z))"
value "mult (suc Z) (suc Z)"
value "mult (suc (suc Z)) (suc (suc (suc Z)))"

(*
  Th-mult-01:   \<forall>x:\<nat>. \<forall>y:\<nat>. \<forall>z:\<nat>. mult x (mult y z) = mult (mult x y) z
  Th-mult-02:   \<forall>x:\<nat>. \<forall>y:\<nat>. mult x y = mult y z
  Th-mult-03:   \<forall>x:\<nat>. \<forall>y:\<nat>. \<forall>z:\<nat>. mult x (add y z) = add (mult x y) (mult x z)
*)

theorem thmult01: "\<forall>x. \<forall>y. mult x (mult y n) = mult (mult x y) n"
  proof (induction n)
    show "\<forall>x. \<forall>y. mult x (mult y Z) = mult (mult x y) Z"
    proof (rule allI, rule allI)
      fix x0::Nat and y0::Nat
      have "mult x0 (mult y0 Z) = mult x0 Z" by (simp only:mult01) also
      have "mult x0 Z = mult (mult x0 y0) Z" by (simp only:mult01)
      finally show "mult x0 (mult y0 Z) = mult (mult x0 y0) Z" by this
    qed
    next
      fix x0::Nat
      assume IH: "\<forall>x. \<forall>y. mult x (mult y x0) = mult (mult x y) x0"
      show "\<forall>x. \<forall>y. mult x (mult y (suc x0)) = mult (mult x y) (suc x0)"
      proof (rule allI, rule allI)
        fix x1::Nat and y1::Nat
        have "mult x1 (mult y1 (suc x0)) = mult x1 (add y1 (mult y1 x0))" by (simp only:mult02) also
        have "mult x1 (add y1 (mult y1 x0)) = mult x1 (add (mult y1 x0) y1)" by (simp only:thadd02) also
        finally show "mult x1 (mult y1 (suc x0)) = mult (mult x1 y1) (suc x0)" by this
      qed
  qed
