(** [type_scope] must be declared and bound early on so that later reserved notations register correctly. *)
Declare Scope type_scope.
Bind Scope type_scope with Sortclass.

(** To reserve this notation, we must first bootstrap, and preserve the underlying [forall] notation *)
Notation "'forall'  x .. y , P" := (forall x , .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity).
Reserved Notation "'exists' x .. y , p"
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'").


(** Work around bug 5569, https://coq.inria.fr/bugs/show_bug.cgi?id=5569, Warning skip-spaces-curly,parsing seems bogus *)
Local Set Warnings "-skip-spaces-curly".

(** These are the notations whose level and associativity are imposed by Coq *)

(** Notations for propositional connectives *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "(->)" (at level 0).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "x |_| y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 35, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, no associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "/ x" (at level 35, right associativity).

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )" (at level 0).

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level as "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).


(** Numeric *)
Reserved Notation "n .+1" (at level 1, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 1, left associativity, format "n .+2").
Reserved Notation "n .+3" (at level 1, left associativity, format "n .+3").
Reserved Notation "n .+4" (at level 1, left associativity, format "n .+4").
Reserved Notation "n .+5" (at level 1, left associativity, format "n .+5").
Reserved Notation "n '.-1'" (at level 1, left associativity, format "n .-1").
Reserved Notation "n '.-2'" (at level 1, left associativity, format "n .-2").
Reserved Notation "m +2+ n" (at level 50, left associativity).
Reserved Infix "mod" (at level 40, no associativity).
Reserved Notation "p ~ 1" (at level 1, left associativity, format "p '~' '1'").
Reserved Notation "p ~ 0" (at level 1, left associativity, format "p '~' '0'").

(** Pointed *)
Reserved Infix "@*" (at level 30).
Reserved Infix "@@*" (at level 30).
Reserved Infix "<~>*" (at level 85).
Reserved Infix "->*" (at level 99).
Reserved Infix "->**" (at level 99).
Reserved Infix "o*" (at level 40, left associativity).
Reserved Infix "==*" (at level 70, no associativity).
Reserved Notation "g ^*'" (at level 1).
Reserved Notation "f ^*" (at level 1, format "f '^*'").
Reserved Notation "f ^-1*" (at level 1, format "f '^-1*'").
Reserved Notation "g o*E f" (at level 40, left associativity).
Reserved Notation "'ppforall'  x .. y , P"
     (at level 200, x binder, y binder, right associativity).

(** Sigma type *)
Reserved Notation "x .1" (at level 1, format "x '.1'").
Reserved Notation "x .2" (at level 1, format "x '.2'").

(** Paths *)
Reserved Notation "p ^" (at level 1, format "p '^'").
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "p @' q" (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'").
Reserved Notation "f == g" (at level 70, no associativity).

(** Equivalences *)
Reserved Notation "A <~> B" (at level 85).
Reserved Notation "f ^-1" (at level 1, format "f '^-1'").
Reserved Notation "g 'oE' f" (at level 40, left associativity).
Reserved Notation "f *E g" (at level 40, left associativity).
Reserved Notation "f +E g" (at level 50, left associativity).

(** Categories *)
Reserved Infix "-|" (at level 60, right associativity).
Reserved Infix "<~=~>" (at level 70, no associativity).
#[warnings="-postfix-notation-not-level-1"]
Reserved Notation "a // 'CAT'" (at level 40, left associativity).
#[warnings="-postfix-notation-not-level-1"]
Reserved Notation "a \\ 'CAT'" (at level 40, left associativity).
Reserved Notation "'CAT' // a" (at level 40, left associativity).
Reserved Notation "'CAT' \\ a" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 1, format "C '^op'").

(** Universal algebra *)
Reserved Notation "u .# A" (at level 3, format "u '.#' A").

(** Natural numbers *)
Reserved Infix "=n" (at level 70, no associativity).

(** Wild cat *)
Reserved Infix "$->" (at level 99).
Reserved Infix "$<~>" (at level 85).
Reserved Infix "$o" (at level 40, left associativity).
Reserved Infix "$oE" (at level 40, left associativity).
Reserved Infix "$==" (at level 70).
Reserved Infix "$o@" (at level 30).
Reserved Infix "$@" (at level 30).
Reserved Infix "$@L" (at level 30).
Reserved Infix "$@R" (at level 30).
Reserved Infix "$@@" (at level 30).
Reserved Infix "$=>" (at level 99).
Reserved Notation "T ^op" (at level 1, format "T ^op").
Reserved Notation "f ^-1$" (at level 1, format "f '^-1$'").
Reserved Notation "f ^$" (at level 1, format "f '^$'").
Reserved Infix "$@h" (at level 35).
Reserved Infix "$@v" (at level 35).
Reserved Infix "$@hR" (at level 34).
Reserved Infix "$@hL" (at level 34).
Reserved Infix "$@vR" (at level 34).
Reserved Infix "$@vL" (at level 34).
Reserved Notation "s ^h$" (at level 1).
Reserved Notation "s ^v$" (at level 1).

(** Displayed wild cat *)
Reserved Infix "$o'" (at level 40, left associativity).
Reserved Infix "$@'" (at level 30).
Reserved Infix "$@L'" (at level 30).
Reserved Infix "$@R'" (at level 30).
Reserved Infix "$@@'" (at level 30).
Reserved Infix "$oE'" (at level 40, left associativity).
Reserved Notation "f ^$'" (at level 1, format "f '^$''").
Reserved Notation "f ^-1$'" (at level 1, format "f '^-1$''").

(** Cubical *)
Reserved Infix "@@h" (at level 30).
Reserved Infix "@@v" (at level 30).
Reserved Infix "@lr" (at level 30).
Reserved Notation "x '@Dp' y"  (at level 20).
Reserved Notation "x '@Dr' y" (at level 20).
Reserved Notation "x '@Dl' y" (at level 20).
Reserved Notation "x '^D'" (at level 1).

(** Lists *)
Reserved Infix "::" (at level 60, right associativity).
Reserved Infix "++" (right associativity, at level 60).
Reserved Notation "[ u ]" (at level 0).
Reserved Notation " [ u , v ] " (at level 0).

(** Algebra *)
Reserved Infix "*L" (at level 40).
Reserved Infix "*R" (at level 40).

(** Type Family Extensions *)
Reserved Notation "P <| j" (at level 40).
Reserved Notation "P |> j" (at level 40).
Reserved Notation "P >=> R" (at level 55).

(** Other / Not sorted yet *)

Reserved Infix "<=>" (at level 70).
Reserved Infix "<<" (at level 70).
Reserved Infix "<<<" (at level 70).


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
Reserved Notation "F ^op" (at level 1, format "F ^op").
Reserved Notation "'forall'  x .. y , P" (at level 200, x binder, y binder, right associativity).
Reserved Notation "g 'oD' f" (at level 40, left associativity).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "m <= n" (at level 70, no associativity).
Reserved Notation "n -Type" (at level 1).
Reserved Notation "p ..1" (at level 1).
Reserved Notation "p ..2" (at level 1).
Reserved Notation "!! P" (at level 35, right associativity).
Reserved Notation "u ~~ v" (at level 30).
Reserved Notation "! x" (at level 3, format "'!' x").
Reserved Notation "x \\ F" (at level 40, left associativity).
Reserved Notation "x // F" (at level 40, left associativity).
Reserved Notation "{ { xL | xR // xcut } }" (at level 0, xR at level 39, format "{ {  xL  |  xR // xcut  } }").

Reserved Notation "x \ F" (at level 40, left associativity).
Reserved Notation "x <> y" (at level 70, no associativity).
Reserved Notation "x ->> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x -|-> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x --> y" (at level 55, right associativity, y at level 55).
Reserved Notation "x (-> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <> y  :>  T" (at level 70, y at next level, no associativity).
Reserved Notation "Z ** W" (at level 30, right associativity).

Reserved Notation "'+N'" (at level 0).
Reserved Notation "'+Z'" (at level 0).
Reserved Notation "'N3'" (at level 0).
Reserved Notation "'Z3'" (at level 0).

Reserved Notation "a ^+" (at level 1).
Reserved Notation "a ^+ k" (at level 1).
Reserved Notation "x ^++" (at level 1).
Reserved Notation "x ^++ k" (at level 1).
Reserved Notation "b ^+f" (at level 1).

(** Notations for the mathclasses library *)
Reserved Notation "' x" (at level 20).
Reserved Notation "// x" (at level 40, no associativity).
Reserved Infix "?=" (at level 70, no associativity).
Reserved Infix "=?" (at level 70, no associativity).
Reserved Infix "<?" (at level 70, no associativity).
Reserved Infix "<=?" (at level 70, no associativity).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Infix "=N=" (at level 70, no associativity).
Reserved Infix ":::" (at level 60, right associativity).

(** TODO: move? *)
(** ** Notation scopes *)

(** We define various scopes and open them in the order we expect to use them. *)
Declare Scope core_scope.
Declare Scope function_scope.
Declare Scope equiv_scope.
Declare Scope path_scope.
Declare Scope fibration_scope.
Declare Scope trunc_scope.
Declare Scope long_path_scope.

Delimit Scope core_scope with core.
Delimit Scope function_scope with function.
Delimit Scope type_scope with type.
Delimit Scope equiv_scope with equiv.
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Delimit Scope trunc_scope with trunc.

Global Open Scope trunc_scope.
Global Open Scope equiv_scope.
Global Open Scope path_scope.
Global Open Scope fibration_scope.
Global Open Scope function_scope.
Global Open Scope type_scope.
Global Open Scope core_scope.

Bind Scope function_scope with Funclass.
