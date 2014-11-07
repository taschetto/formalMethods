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

        primrec cat::'a List \<Longrightarrow> 'a List \<Longrightarrow> 'a List
          where
            cat01: cat Empty l = l |
            cat02: cat (cons h t) l = cons h (cat t l)
  
            P = \<triangleq> \<forall>l1. \<forall>l2. \<forall>l3. cat l1 (cat l2 l3) = cat (cat l1 l2) l3

            P(l) \<triangleq> \<forall>l2. \<forall>l3. cat l (cat l2 l3) = cat (cat l l2) l3

  2.1) Prova caso base: P Empty

    Temos que provar que:
      \<forall>l2. \<forall>l3. cat Empty (cat l2 l3) = cat (cat Empty l2) l3

    Sejam k, l duas listas arbitrárias. Então, é suficiente mostrar que:

      cat Empty (cat k l) = cat (cat Empty k) l

    Agora veja que:
      cat Empty (cat k l)
        = cat k l                 (por cat01, l := cat k l)
        = cons (cat empty k) l    (por cat01, l := k)

        q. e. d.

  2.2) Prova Caso Indutivo: P(l0) \<longrightarrow> P(cons e0 l0)

    Sejam e0 e l0 elementos arbitrários. Assumindo como hipótese de indução:
      P(l0) \<triangleq> \<forall>l2. \<forall>l3. cat l0 (cat l2 l3) = cat (cat l0 l2) l3       (HI)

    Temos que mostrar que:
      \<forall>l2. \<forall>l3. cat (cons e0 l0) (cat l2 l3) = cat (cat (cons e0 l0) l2) l3

    Sejam k e p duas listas arbitrários. Logo, é suficiente mostrar que:

      cat (cons e0 l0) (cat k p) = cat (cat (cons e0 l0) k) p

    Agora veja que:

      cat (cons e0 l0) (cat k p)
        = cons e0 (cat l0 (cat k p))    (by cat02, l := (cat k p)

....
        q. e. d.
*)
