(* -*- mode: coq; mode: visual-line -*-  *)
(** * Universes of truncated types. *)

Require Import Overture PathGroupoids Trunc Equivalences HProp EquivalenceVarieties types.Arrow types.Paths types.Sigma types.Universe types.Record.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** Some auxiliary lemmas, needed in this file but difficult to find better homes for, due to complicated dependencies.  TODO: keep trying to re-house. *)

Section Auxiliary.

Context `{Funext}.

Lemma equiv_path_equiv {A B : Type} (e1 e2 : A <~> B)
  : (e1 = e2 :> (A -> B)) <~> (e1 = e2 :> (A <~> B)).
Proof.
  equiv_via ((issig_equiv A B) ^-1 e1 = (issig_equiv A B) ^-1 e2).
    Focus 2. apply symmetry, equiv_ap; refine _.
  apply (equiv_compose' (equiv_path_sigma _ _ _)); simpl.
  apply symmetry, equiv_sigma_contr.
  intros ?. apply hprop_isequiv.
Defined.

Lemma istrunc_equiv {n : trunc_index} {A B : Type} `{IsTrunc (trunc_S n) B}
  : IsTrunc (trunc_S n) (A <~> B).
Proof.
  simpl. intros e1 e2.
  apply (@trunc_equiv _ _ (equiv_path_equiv e1 e2)).
    apply (@trunc_arrow _ A B (trunc_S n) _).
  apply equiv_isequiv.
Defined.

(* TODO: this name is terrible, especially in conjunction with [contr_equiv_contr].  Improve it?? *)
Lemma iscontr_equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : Contr (A <~> B).
Admitted.

End Auxiliary.

Section TruncType.

Context `{Univalence} `{Funext}.

Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type :> Type ;
  istrunc_trunctype_type : IsTrunc n trunctype_type
}.
(* Note: the naming of the second constructor is more than a little clunky.  However, the more obvious [istrunc_trunctype] is taken by the theorem below, that [IsTrunc (trunc_S n) (TruncType n)], which seems to have an even better claim to it. *)

Arguments BuildTruncType _ _ {_}.
Arguments trunctype_type [_] _.
Arguments istrunc_trunctype_type [_] _.

Existing Instance istrunc_trunctype_type.

Definition issig_trunctype {n : trunc_index}
  : { X : Type & IsTrunc n X } <~> TruncType n.
Proof.
  issig (@BuildTruncType n) (@trunctype_type n) (@istrunc_trunctype_type n).
Defined.

Definition equiv_path_trunctype {n : trunc_index} (A B : TruncType n)
  : (A <~> B) <~> (A = B :> TruncType n).
Proof.
  equiv_via (A = B :> Type).
    apply equiv_path_universe.
  equiv_via ((issig_trunctype ^-1 A) = (issig_trunctype ^-1 B)).
    Focus 2. apply symmetry, equiv_ap; refine _.
  simpl.
  apply (equiv_compose' (equiv_path_sigma _ _ _)); simpl.
  apply symmetry, equiv_sigma_contr.
  intros ?. apply hprop_trunc.
Defined.

Definition path_trunctype {n : trunc_index} {A B : TruncType n}
  : A <~> B -> (A = B :> TruncType n)
:= equiv_path_trunctype A B.

Instance istrunc_trunctype {n : trunc_index}
  : IsTrunc (trunc_S n) (TruncType n).
Proof.
  intros A B.
  apply (@trunc_equiv _ _ (equiv_path_trunctype A B)).
    Focus 2. apply equiv_isequiv. 
  case n as [ | n'].
    apply iscontr_equiv_contr_contr. (* The reason is different in this case. *)
  apply istrunc_equiv.
Defined.

End TruncType.