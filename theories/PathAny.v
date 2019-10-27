Require Import HoTT.Basics HoTT.Types Fibrations FunextVarieties.

(** A nice method for proving characterizations of path-types of nested sigma-types, due to Rijke. *)

(** To show that the path-type of [A] is equivalent to some specified family [P], it suffices to show that [P] is reflexive and its "based path-spaces" are contractible. *)
Definition equiv_path_from_contr {A : Type} (P : A -> A -> Type)
           (Prefl : forall x, P x x)
           (cp : forall x, Contr {y:A & P x y} )
           (a b : A)
  : P a b <~> a = b.
Proof.
  apply equiv_inverse.
  srefine (BuildEquiv _ _ _ _).
  { intros []; apply Prefl. }
  revert b; apply isequiv_from_functor_sigma.
  (* For some reason, typeclass search can't find the Contr instances unless we give the types explicitly. *)
  refine (@isequiv_contr_contr {x:A & a=x} {x:A & P a x} _ _ _).
Defined.

(** This tactic applies the above equivalence and combines it with an [issig] lemma for [A].  (If the type family [P] is also a record, then the user has to apply its [issig] manually.) *)
Ltac eqp_issig_contr e :=
  match goal with
  | [ |- ?X <~> ?x = ?y ] => revert x y
  | _ => idtac
  end;
  let x := fresh in
  let y := fresh in
  equiv_intro e x;
  equiv_intro e y;
  refine ((equiv_ap' e^-1 _ _)^-1 oE _);
  revert x y;
  match goal with
    [ |- forall x y, @?P x y <~> ?eq ] =>
    refine (equiv_path_from_contr P _ _)
  end.

(** After [eqp_issig_contr], we are left showing the contractibility of a sigma-type whose base and fibers are large nested sigma-types of the same depth.  Moreover, we expect that the types appearing in those two large nested sigma-types "pair up" to form contractible based "path-types".  The following lemma "peels off" the first such pair, whose contractibility can often be found with typeclass search.  The remaining contractibility goal is then simplified by substituting the center of contraction of that first based "path-type", or more precisely a *specific* center that may or may not be the one given by the contractibility instance; the latter freedom sometimes makes things faster and simpler. *)
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
