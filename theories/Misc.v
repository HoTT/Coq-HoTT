(* -*- mode: coq; mode: visual-line -*- *)
(** * Misecllaneous material *)

(** If you have a lemma or group of lemmas that you can’t find a better home for, put them here.  However, big “Miscellaneous” files are sub-optimal to work with, so some caveats:

- do try to find a better home for things if possible!
- if there were any specific difficulties in placing your lemmas (eg dependency issues), please document that.
- generally, be extra-careful keeping this file well-organised and documented.
- any time you see a chance to move lemmas from this file to a better home, do so without hesitation! *)

(** Dependencies: we should allow this file to depend at least on files from the [types] directory; ipso facto, we should not put anything here that those files depend on.

Conversely, several files in [hit] now depend on this file; so we should probably avoid using HIT’s in this file. *)

Require Import Basics.
Require Import types.Sigma types.Paths types.Record types.Arrow types.Forall types.Bool.
Require Import HProp EquivalenceVarieties.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** ** Null homotopies of maps *)
Section NullHomotopy.

Context `{Funext}.

(** Geometrically, a nullhomotopy of a map [f : X -> Y] is an extension of [f] to a map [Cone X -> Y].  One might more simply call it e.g. [Constant f], but that is a little ambiguous: it could also reasonably mean e.g. a factorisation of [f] through [ Trunc -1 X ].  (Should the unique map [0 -> Y] be constant in one way, or in [Y]-many ways?) *)

(* These use [trunc_sigma], so depend on [types.Sigma]. *)
Definition NullHomotopy {X Y : Type} (f : X -> Y)
  := {y : Y & forall x:X, f x = y}.

Lemma istrunc_nullhomotopy {n : trunc_index}
  {X Y : Type} (f : X -> Y) `{IsTrunc n Y}
  : IsTrunc n (NullHomotopy f).
Proof.
  apply @trunc_sigma; auto.
  intros y. apply (@trunc_forall _).
  intros x. apply trunc_succ.
Defined.

End NullHomotopy.

(** ** [Bool <~> (Bool <~> Bool)]

    This should go in [types/Bool.v], but it depends on a lemma above. *)
Definition equiv_bool_equiv_bool_bool `{Funext} : Bool <~> (Bool <~> Bool)
  := @equiv_bool_equiv_bool_bool_helper _ (@path_equiv _ _ _).

(** ** Equivalences between contractible types *)
Section EquivContr.

(** Not at all sure where these naturally belong.  [Contr] is the obvious idea, but of course they depend on lots of subsequent material. *)

(* TODO: the name [equiv_contr_contr] is not great in conjunction with the existing, unrelated [contr_equiv_contr].  Consider alternative names? *)

Lemma equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B).
Proof.
  apply equiv_adjointify with (fun _ => center B) (fun _ => center A);
  intros ?; apply contr.
Defined.

Lemma contr_equiv_contr_contr `{Funext} {A B : Type} `{Contr A} `{Contr B}
  : Contr (A <~> B).
Proof.
  exists equiv_contr_contr.
  intros e. apply path_equiv, path_forall. intros ?; apply contr.
Defined.

End EquivContr.
