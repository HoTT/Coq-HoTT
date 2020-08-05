(** To reserve this notation, we must first bootstrap, and preserve the underlying [forall] notation *)
Notation "'forall'  x .. y , P" := (forall x , .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity).

(** Work around bug 5569, https://coq.inria.fr/bugs/show_bug.cgi?id=5569, Warning skip-spaces-curly,parsing seems bogus *)
Local Set Warnings Append "-skip-spaces-curly".

(** Numeric *)
Reserved Notation "n .+1" (at level 2, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 2, left associativity, format "n .+2").
Reserved Notation "n .+3" (at level 2, left associativity, format "n .+3").
Reserved Notation "n .+4" (at level 2, left associativity, format "n .+4").
Reserved Notation "n .+5" (at level 2, left associativity, format "n .+5").
Reserved Notation "n '.-1'" (at level 2, left associativity, format "n .-1").
Reserved Notation "n '.-2'" (at level 2, left associativity, format "n .-2").
Reserved Notation "m +2+ n" (at level 50, left associativity).

(** Pointed *)
Reserved Infix "@*" (at level 30).
Reserved Infix "@@*" (at level 30).
Reserved Infix "<~>*" (at level 85).
Reserved Infix "->*" (at level 99).
Reserved Infix "->**" (at level 99).
Reserved Infix "o*" (at level 40).
Reserved Infix "==*" (at level 70, no associativity).
Reserved Notation "g ^*'" (at level 20).
Reserved Notation "f ^*" (at level 3, format "f '^*'").
Reserved Notation "f ^-1*" (at level 3, format "f '^-1*'").
Reserved Notation "p ^" (at level 3, format "p '^'").
Reserved Notation "g o*E f" (at level 40, left associativity).
Reserved Infix "$@h" (at level 35).
Reserved Infix "$@v" (at level 35).
Reserved Infix "$@hR" (at level 34).
Reserved Infix "$@hL" (at level 34).
Reserved Infix "$@vR" (at level 34).
Reserved Infix "$@vL" (at level 34).
Reserved Notation "s ^h$" (at level 20).
Reserved Notation "s ^v$" (at level 20).

(** Sigma type *)
Reserved Notation "x .1" (at level 3, format "x '.1'").
Reserved Notation "x .2" (at level 3, format "x '.2'").

(** Paths *)
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "p @' q" (at level 21, left associativity, format "'[v' p '/' '@''  q ']'").
Reserved Notation "f == g" (at level 70, no associativity).

(** Equivalences *)
Reserved Notation "A <~> B" (at level 85).
Reserved Notation "f ^-1" (at level 3, format "f '^-1'").
Reserved Notation "m ^-1" (at level 3, format "m '^-1'").
Reserved Notation "g 'oE' f" (at level 40, left associativity).
Reserved Notation "f *E g" (at level 40, no associativity).
Reserved Notation "f +E g" (at level 50, left associativity).

(** Categories *)
Reserved Infix "-|" (at level 60, right associativity).
Reserved Infix "<~=~>" (at level 70, no associativity).
Reserved Notation "a // 'CAT'" (at level 40, left associativity).
Reserved Notation "a \\ 'CAT'" (at level 40, left associativity).
Reserved Notation "'CAT' // a" (at level 40, left associativity).
Reserved Notation "'CAT' \\ a" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 3, format "C '^op'").

(** Natural numbers *)
Reserved Infix "=n" (at level 70, no associativity).

(** Wild cat *)
Reserved Infix "$->" (at level 99).
Reserved Infix "$<~>" (at level 85).
Reserved Infix "$o" (at level 40).
Reserved Infix "$oE" (at level 40).
Reserved Infix "$==" (at level 70).
Reserved Infix "$o@" (at level 30).
Reserved Infix "$@" (at level 30).
Reserved Infix "$@L" (at level 30).
Reserved Infix "$@R" (at level 30).
Reserved Infix "$=>" (at level 99).
Reserved Notation "T ^op" (at level 3, format "T ^op").
Reserved Notation "f ^-1$" (at level 3, format "f '^-1$'").
Reserved Notation "f ^$" (at level 3, format "f '^$'").

(** Cubical *)
Reserved Infix "@@h" (at level 30).
Reserved Infix "@@v" (at level 30).
Reserved Infix "@lr" (at level 30).

(** Other / Not sorted yet *)

Reserved Infix "oL" (at level 40, left associativity).
Reserved Infix "oR" (at level 40, left associativity).

Reserved Notation "~~ A" (at level 35, right associativity).
Reserved Notation "a \ C" (at level 40, left associativity).
Reserved Notation "a <=_{ x } b" (at level 70, no associativity).
Reserved Notation "D1 ~d~ D2" (at level 65).
Reserved Notation "D '_f' g" (at level 10).
Reserved Notation "F '_0' x" (at level 10, no associativity).
Reserved Notation "F '_0' x" (at level 10, no associativity).
Reserved Notation "F '_1' m" (at level 10, no associativity).
Reserved Notation "F ^op" (at level 3, format "F ^op").
Reserved Notation "'forall'  x .. y , P" (at level 200, x binder, y binder, right associativity).
Reserved Notation "g 'oD' f" (at level 40, left associativity).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "m <= n" (at level 70, no associativity).
Reserved Notation "n -Type" (at level 1).
Reserved Notation "p ..1" (at level 3).
Reserved Notation "p ..2" (at level 3).
Reserved Notation "!! P" (at level 35, right associativity).
Reserved Notation "[ u ]" (at level 9).
Reserved Notation "u ~~ v" (at level 30).
Reserved Notation " [ u , v ] " (at level 9).
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
