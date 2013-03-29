(* -*- mode: coq; mode: visual-line -*-  *)
(** * Universes of truncated types. *)

Require Import Overture PathGroupoids Trunc Equivalences HProp EquivalenceVarieties Arrow Paths Sigma Universe Record.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** ** Some auxiliary lemmas, needed in this file but difficult to find better homes for, due to complicated dependencies.  TODO: keep trying to re-house. *)

Section Auxiliary.

Context `{Funext}.

(** *** Sigmas of hprops. *)

(** The sigma of an hprop over a type can be viewed as a subtype. In particular, paths in the subtype are equivalent to paths in the original type. *)
Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
  {HP : forall a, IsHProp (P a)} (u v : sigT P)
: (u.1 = v.1) <~> (u = v).
Proof.
  apply (equiv_compose' (equiv_path_sigma _ _ _)); simpl.
  apply symmetry, equiv_sigma_contr.
  intros ?; apply HP.
Defined.

(** (This lemma seems to belong in [types.Sigma], but it depends on [EquivalenceVarieties] via [hprop_isequiv], which itself depends on [types.Sigma].) *)

(** *** Paths between equivalences *)

(** (These could fit in [EquivalenceVarieties], if the lemma [equiv_path_sigma_hprop] were given there with them. *)

Lemma equiv_path_equiv {A B : Type} (e1 e2 : A <~> B)
  : (e1 = e2 :> (A -> B)) <~> (e1 = e2 :> (A <~> B)).
Proof.
  equiv_via ((issig_equiv A B) ^-1 e1 = (issig_equiv A B) ^-1 e2).
    Focus 2. apply symmetry, equiv_ap; refine _.
(* TODO: why does this get the wrong type if [hprop_isequiv] is not supplied? *)
  exact (@equiv_path_sigma_hprop _ _ hprop_isequiv 
    ((issig_equiv A B) ^-1 e1) ((issig_equiv A B) ^-1 e2)).
Defined.

Lemma istrunc_equiv {n : trunc_index} {A B : Type} `{IsTrunc (trunc_S n) B}
  : IsTrunc (trunc_S n) (A <~> B).
Proof.
  simpl. intros e1 e2.
  apply (@trunc_equiv _ _ (equiv_path_equiv e1 e2)).
    apply (@trunc_arrow _ A B (trunc_S n) _).
  apply equiv_isequiv.
Defined.

(** *** Equivalences between contractible types *)

(** Not at all sure where these naturally belong.  [Contr] is the obvious idea, but of course they depend on lots of subsequent material. *)

(* TODO: the name [equiv_contr_contr] is not great in conjunction with the existing, unrelated [contr_equiv_contr].  Consider alternative names? *)

Lemma equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B).
Proof.
  apply equiv_adjointify with (fun _ => center B) (fun _ => center A);
  intros ?; apply contr.
Defined.

Lemma contr_equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : Contr (A <~> B).
Proof.
  exists equiv_contr_contr.
  intros e. apply equiv_path_equiv, path_forall. intros ?; apply contr.
Defined.

End Auxiliary.

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
  simpl. apply (equiv_path_sigma_hprop
    (trunctype_type A; istrunc_trunctype_type A)
    (trunctype_type B; istrunc_trunctype_type B)).
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
    apply contr_equiv_contr_contr. (* The reason is different in this case. *)
  apply istrunc_equiv.
Defined.

End TruncType.