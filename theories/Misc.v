(* -*- mode: coq; mode: visual-line -*- *)
(** * Misecllaneous material *)

(** If you have a lemma or group of lemmas that you can’t find a better home for, put them here.  However, big “Miscellaneous” files are sub-optimal to work with, so some caveats:

- do try to find a better home for things if possible!
- if there were any specific difficulties in placing your lemmas (eg dependency issues), please document that.
- generally, be extra-careful keeping this file well-organised and documented.
- any time you see a chance to move lemmas from this file to a better home, do so without hesitation! *)

(** Dependencies: we should allow this file to depend at least on files from the [types] directory; ipso facto, we should not put anything here that those files depend on.

Conversely, several files in [hit] now depend on this file; so we should probably avoid using HIT’s in this file. *)

Require Import HoTT.Basics.
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
