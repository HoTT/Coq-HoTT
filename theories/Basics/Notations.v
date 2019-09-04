(** To reserve this notation, we must first bootstrap, and preserve the underlying [forall] notation *)
Notation "'forall'  x .. y , P" := (forall x , .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity).

(** Work around bug 5569, https://coq.inria.fr/bugs/show_bug.cgi?id=5569, Warning skip-spaces-curly,parsing seems bogus *)
Local Set Warnings Append "-skip-spaces-curly".
Reserved Infix "@*" (at level 30).
Reserved Infix "-|" (at level 60, right associativity).
Reserved Infix "<~=~>" (at level 70, no associativity).
Reserved Infix "==*" (at level 70, no associativity).
Reserved Infix "<~>*" (at level 85).
Reserved Infix "->*" (at level 99).
Reserved Infix "=n" (at level 70, no associativity).
Reserved Infix "o*" (at level 40).
Reserved Infix "oL" (at level 40, left associativity).
Reserved Infix "oR" (at level 40, left associativity).
Reserved Notation "-1" (at level 0).
Reserved Notation "-2" (at level 0).
Reserved Notation "~~ A" (at level 75, right associativity, only parsing).
Reserved Notation "A <~> B" (at level 85).
Reserved Notation "a // 'CAT'" (at level 40, left associativity).
Reserved Notation "a \\ 'CAT'" (at level 40, left associativity).
Reserved Notation "a \ C" (at level 40, left associativity).
Reserved Notation "a <=_{ x } b" (at level 70, no associativity).
Reserved Notation "'CAT' // a" (at level 40, left associativity).
Reserved Notation "'CAT' \\ a" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 3, format "C '^op'").
Reserved Notation "D1 ~d~ D2" (at level 65).
Reserved Notation "D '_f' g" (at level 10).
Reserved Notation "F '_0' x" (at level 10, no associativity).
Reserved Notation "F '_0' x" (at level 10, no associativity, only parsing).
Reserved Notation "f ^-1" (at level 3, format "f '^-1'").
Reserved Notation "f ^-1*" (at level 3, format "f '^-1*'").
Reserved Notation "F '_1' m" (at level 10, no associativity).
Reserved Notation "f ^*" (at level 20).
Reserved Notation "f *E g" (at level 40, no associativity).
Reserved Notation "f +E g" (at level 50, left associativity).
Reserved Notation "f == g" (at level 70, no associativity).
Reserved Notation "F ^op" (at level 3, format "F ^op").
Reserved Notation "'forall'  x .. y , P" (at level 200, x binder, y binder, right associativity).
Reserved Notation "g ^*'" (at level 20).
Reserved Notation "g 'oD' f" (at level 40, left associativity).
Reserved Notation "g 'oE' f" (at level 40, left associativity).
Reserved Notation "g o*E f" (at level 40, left associativity).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "m ^-1" (at level 3, format "m '^-1'").
Reserved Notation "m +2+ n" (at level 50, left associativity).
Reserved Notation "m <= n" (at level 70, no associativity).
Reserved Notation "n .+1" (at level 2, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 2, left associativity, format "n .+2").
Reserved Notation "n .+3" (at level 2, left associativity, format "n .+3").
Reserved Notation "n .+4" (at level 2, left associativity, format "n .+4").
Reserved Notation "n .+5" (at level 2, left associativity, format "n .+5").
Reserved Notation "n -Type" (at level 1).
Reserved Notation "p ..1" (at level 3).
Reserved Notation "p ..2" (at level 3).
Reserved Notation "p ^" (at level 3, format "p '^'").
Reserved Notation "!! P" (at level 75, right associativity).
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "p @' q" (at level 21, left associativity, format "'[v' p '/' '@''  q ']'").
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p # x" (right associativity, at level 65, only parsing).
Reserved Notation "T ^op" (at level 3, format "T ^op").
Reserved Notation "[ u ]" (at level 9).
Reserved Notation "u ~~ v" (at level 30).
Reserved Notation " [ u , v ] " (at level 9).
Reserved Notation "x .1" (at level 3, format "x '.1'").
Reserved Notation "x .2" (at level 3, format "x '.2'").
Reserved Notation "! x" (at level 3, format "'!' x").
Reserved Notation "x \\ F" (at level 40, left associativity).
Reserved Notation "x // F" (at level 40, left associativity).
Reserved Notation "{ { xL | xR // xcut } }" (at level 0, xR at level 39, format "{ {  xL  |  xR  //  xcut  } }").
Reserved Notation "x \ F" (at level 40, left associativity).
Reserved Notation "x / F" (at level 40, left associativity).
Reserved Notation "x <> y" (at level 70, no associativity).
Reserved Notation "x ->> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x -|-> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x --> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x (-> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <> y  :>  T" (at level 70, y at next level, no associativity).
Reserved Notation "Z ** W" (at level 30, right associativity).
