Require Import HoTT.Basics HoTT.Types Fibrations FunextVarieties.

(** A nice method for proving characterizations of path-types of nested sigma-types, due to Rijke. *)

(** To show that the based path-type of [A] is equivalent to some specified family [P], it suffices to show that [P] is reflexive and its total space is contractible. This is part of Theorem 5.8.2, namely (iv) implies (iii). *)
Definition equiv_path_from_contr {A : Type} (a : A) (P : A -> Type)
           (Prefl : P a)
           (cp : Contr {y:A & P y} )
           (b : A)
  : P b <~> a = b.
Proof.
  apply equiv_inverse.
  srefine (Build_Equiv _ _ _ _).
  { intros []; apply Prefl. }
  revert b; apply isequiv_from_functor_sigma.
  (* For some reason, typeclass search can't find the Contr instances unless we give the types explicitly. *)
  refine (@isequiv_contr_contr {x:A & a=x} {x:A & P x} _ _ _).
Defined.

(** This is another result for characterizing the path type of [A] when given an equivalence [e : B <~> A], such as an [issig] lemma for [A]. It can help Coq to deduce the type family [P] if [revert] is used to move [a0] and [a1] into the goal, if needed. *)
Definition equiv_path_along_equiv {A B : Type} {P : A -> A -> Type}
           (e : B <~> A)
           (K : forall b0 b1 : B, P (e b0) (e b1) <~> b0 = b1)
  : forall a0 a1 : A, P a0 a1 <~> a0 = a1.
Proof.
  equiv_intros e b0 b1.
  refine (_ oE K b0 b1).
  apply equiv_ap'.
Defined.

(** This simply combines the two previous results, a common idiom. Again, it can help Coq to deduce the type family [P] if [revert] is used to move [a0] and [a1] into the goal, if needed. *)
Definition equiv_path_issig_contr {A B : Type} {P : A -> A -> Type}
           (e : B <~> A)
           (Prefl : forall b, P (e b) (e b))
           (cp : forall b1, Contr {b2 : B & P (e b1) (e b2)})
  : forall a0 a1 : A, P a0 a1 <~> a0 = a1.
Proof.
  apply (equiv_path_along_equiv e).
  intro a0.
  serapply equiv_path_from_contr.
  apply Prefl.
Defined.

(** After [equiv_path_issig_contr], we are left showing the contractibility of a sigma-type whose base and fibers are large nested sigma-types of the same depth.  Moreover, we expect that the types appearing in those two large nested sigma-types "pair up" to form contractible based "path-types".  The following lemma "peels off" the first such pair, whose contractibility can often be found with typeclass search.  The remaining contractibility goal is then simplified by substituting the center of contraction of that first based "path-type", or more precisely a *specific* center that may or may not be the one given by the contractibility instance; the latter freedom sometimes makes things faster and simpler. *)
Definition contr_sigma_sigma (A : Type) (B : A -> Type)
           (C : A -> Type) (D : forall a, B a -> C a -> Type)
           {cac : Contr {x:A & C x} }
           (a : A) (c : C a)
           {ccd : Contr {y:B a & D a y c } }
  : Contr {ab : {x:A & B x} & {y:C ab.1 & D ab.1 ab.2 y} }.
Proof.
  pose (d := (center {y:B a & D a y c}).2).
  set (b := (center {y:B a & D a y c}).1) in *.
  exists ((a;b);(c;d)).
  intros [[a' b'] [c' d']]; cbn in *.
  pose (ac' := (a';c')).
  pose (bd' := (b';d') : {y:B ac'.1 & D ac'.1 y ac'.2}).
  change (((a;b);(c;d)) = ((ac'.1;bd'.1);(ac'.2;bd'.2))
          :> {ab : {x:A & B x} & {y:C ab.1 & D ab.1 ab.2 y} }).
  clearbody ac' bd'; clear a' b' c' d'.
  destruct (@path_contr {x:A & C x} _ (a;c) ac').
  destruct (@path_contr {y:B a & D a y c} _ (b;d) bd').
  reflexivity.
Defined.

(** This tactic just applies the previous lemma, using a match to figure out the appropriate type families so the user doesn't have to specify them. *)
Ltac contr_sigsig a c :=
  match goal with
  | [ |- Contr (@sig (@sig ?A ?B) (fun ab => @sig (@?C ab) (@?D ab))) ] =>
    (* The lemma only applies when C depends only on the first component of ab, so we need to factor it somehow through pr1. *)
    let C' := fresh in
    transparent assert (C' : {C' : A -> Type & forall ab, C' ab.1 = C ab});
    [ eexists; intros ab; reflexivity
    | refine (contr_sigma_sigma A B C'.1 (fun a b c => D (a;b) c) a c);
      subst C' ]
  end.

(** For examples of the use of this tactic, see for instance [Factorization] and [Idempotents]. *)
