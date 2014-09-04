(*
  1) Prova da associatividade da função "add"

    P \<triangleq>  \<forall>x:Nat. \<forall>y:Nat. \<forall>z:Nat.
      add (add x y) z = add x (add y z)

    A prova de uma primitiva recursiva é feita através de uma INDUÇÃO NATURAL.

                                    xo:Nat
                                    P(xo)     hI
                                    ...
                                    ...
                                    ...
    P zero                          P(suc xo)
    ------------------------------------------------- IND NAT
                         \<forall>n:Nat. P n

    P(n) \<triangleq> \<forall>x. \<forall>y. add (add x y) n = add x (add y n)

  2.1) Prova Caso Base: P zero

    Temos que mostrar que:
      \<forall>x. \<forall>y. add (add x y) zero = add x (add y zero)

    Sejam x0, y0 valores arbitrários em Nat. Então, é suficiente mostrar que:
      add (add xo yo) zero = add xo (add yo) zero

    Agora veja que:
      add (add xo yo) zero
        = add xo yo             (por add01, x := add xo yo)
        = add xo (add yo zero)  (por add01, x := yo)

        q. e. d.

  2.2) Prova Caso Indutivo: P xo \<longrightarrow> P suc xo

    Seja x0 um valor arbitrário em Nat. Assumindo como hipótese de indução:
      \<forall>x. \<forall>y. add (add x y) xo = add x (add x y) xo

    Temos que mostrar que:
      \<forall>x. \<forall>y. add (add x y) (suc xo) = add x (add y (suc xo))

    Sejam k e l valores arbitrários em Nat. Logo, é suficiente mostrar que:

      add (add k l) (suc xo) = add k (add l (suc xo))

    Agora veja que:

      add (add k l) (suc xo)
        = suc (add (add k l) xo)    (por add02, x := add k l, y := xo)
        = suc (add k (add l xo))    (por hI, \<forall>E, x := k, y := l)
        = add k (suc (add l xo))    (por add02, x := k, y := add l xo)
        = add m (add l (suc xo))    (por add02, x := l, y := xo)

        q. e. d.

MOSTRAR QUE O CAT É ASSOCIATIVO.
     
*)
