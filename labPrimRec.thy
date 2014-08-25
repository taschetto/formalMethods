theory labPrimRec
imports Main
begin

text{* Exercício 01 *}
text{* Exercício 02 *}
text{* ... *}

datatype Nat = Z | suc Nat

term "Z"
term "z"
term "suc (suc Z)"
term "Suc (Suc 0)"

primrec add::"Nat => Nat => Nat" where
  "add x Z = x" |
  "add x (suc y) = suc (add x y)"

value "add (suc (suc Z)) (suc (suc Z))"
value "add (suc (suc Z)) (suc Z)"

primrec Nat2int::"Nat => int" where
  "Nat2int Z = 0" |
  "Nat2int (suc x) = 1 + Nat2int x"

value "Nat2int Z"
value "Nat2int (suc (suc (suc (suc Z))))"
value "Nat2int (suc (suc Z)) * Nat2int (suc (suc (suc Z)))"

datatype 'a List = nil | cons 'a "'a List"

term "nil"
term "cons (10::int) (cons 3 (cons -2 nil))"
value "cons (10::int) (cons 3 (cons -2 nil))"
term "cons ''a'' (cons ''1'' (cons ''f'' nil))"
term "cons (suc Z) (cons Z nil)"

primrec len::"'a List => Nat" where
  "len nil = Z" |
  "len (cons h t) = add (suc Z) (len t)"

value "len nil"
value "len (cons (10::int) (cons 3 nil))"
value "Nat2int(len (cons ''a'' (cons ''1'' (cons ''f'' nil))))"

primrec cat::"'a List => 'a List => 'a List" where
  "cat nil l = l" |
  "cat (cons h t) l = cons h (cat t l)"

value "cat nil nil"
value "cat nil (cons (10::int) (cons 3 nil))"
value "cat (cons (10::int) (cons 3 nil)) (cons 2 (cons 4 nil))"

datatype 'a btree = leaf | br 'a "'a btree" "'a btree"

term "leaf"
term "br (1::nat) leaf leaf"
term "br (1::int) (br 2 leaf leaf) (br 3 leaf leaf)"

primrec numLeaf::"'a btree => int" where
  "numLeaf leaf = 1" |
  "numLeaf (br data right left) = numLeaf right + numLeaf left"

value "numLeaf leaf"
value "numLeaf (br (1::nat) leaf leaf)"
value "numLeaf (br (1::int) (br 2 leaf leaf) (br 3 leaf leaf))"

primrec numNode::"'a btree => int" where
  "numNode leaf = 0" |
  "numNode (br data right left) = 1 + (numNode right) + (numNode left)"

value "numNode leaf"
value "numNode (br (1::nat) leaf leaf)"
value "numNode (br (1::int) (br 2 leaf leaf) (br 3 leaf leaf))"

value "max (17::int) 53"

primrec depth::"'a btree => int" where
  "depth leaf = 1" |
  "depth (br data right left) = 1 + max (depth right) (depth left)"

value "depth leaf"
value "depth (br (1::nat) leaf leaf)"
value "depth (br (1::int) (br 2 (br 4 (br 5 leaf leaf) leaf) leaf) (br 3 leaf (br 4 (br 5 leaf leaf) leaf)))"
value "depth (br (1::int) (br 2 (br 4 (br 5 (br 6 leaf leaf) leaf) leaf) leaf) (br 3 leaf (br 4 (br 5 leaf leaf) leaf)))"

end
