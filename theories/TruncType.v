(* -*- mode: coq; mode: visual-line -*-  *)
(** * Universes of truncated types. *)

Require Import Overture PathGroupoids Trunc Equivalences HProp EquivalenceVarieties Arrow Paths Sigma Universe Record Misc.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** ** [TruncType]: Universes of truncated types *)

(** It is convenient for some purposes to consider the universe of all n-truncated types (within a given universe of types).  In particular, this allows us to state the important fact that each such universe is itself (n+1)-truncated. *)

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

Global Existing Instance istrunc_trunctype_type.

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
    2: apply symmetry, equiv_ap; refine _.
  simpl. apply (equiv_path_sigma_hprop
    (trunctype_type A; istrunc_trunctype_type A)
    (trunctype_type B; istrunc_trunctype_type B)).
Defined.

Definition path_trunctype {n : trunc_index} {A B : TruncType n}
  : A <~> B -> (A = B :> TruncType n)
:= equiv_path_trunctype A B.

Global Instance istrunc_trunctype {n : trunc_index}
  : IsTrunc (trunc_S n) (TruncType n) | 0.
Proof.
  intros A B.
  apply (@trunc_equiv _ _ (equiv_path_trunctype A B)).
    2: apply equiv_isequiv.
  case n as [ | n'].
    apply contr_equiv_contr_contr. (* The reason is different in this case. *)
  apply istrunc_equiv.
Defined.

End TruncType.
