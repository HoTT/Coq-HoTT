Require Import Basics Types.
Require Import HoTT.Tactics.

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
  rapply isequiv_contr_contr.
Defined.

(** See Homotopy/EncodeDecode.v for a related characterization of identity types. *)

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
  srapply equiv_path_from_contr.
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
  apply (Build_Contr _ ((a;b);(c;d))).
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
    | nrefine (contr_sigma_sigma A B C'.1 (fun a b => D (a;b)) a c);
      (** In practice, usually the first [Contr] hypothesis can be found by typeclass search, so we try that.  But we don't try on the second one, since often it can't be, and trying can be slow. *)
      [ try exact _ | subst C' ] ]
  end.

(** For examples of the use of this tactic, see for instance [Factorization] and [Idempotents]. *)

(** Given that some type family [R] is fiber-wise equivalent to identity types based at [a], then the total space [sig R] is contractible. This is part of Theorem 5.8.2, (iii) implies (iv). *)
Definition contr_sigma_refl_rel {A : Type}
  (a : A) (R : A -> Type) (r0 : R a)
  (f : forall b, (a = b) <~> R b)
  : Contr (sig R).
Proof.
  rapply contr_equiv'.
  1: exact (equiv_functor_sigma_id f).
  apply contr_basedpaths.
Defined.

(** There are also some additional properties that we can be use to characterize identity types. A pointed type family is an identity system if it satisfies the J-rule. *)
Class IsIdentitySystem {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0)
  := 
  { IdentitySystem_ind (D : forall a : A, R a -> Type) (d : D a0 r0) (a : A) (r : R a) 
      : D a r;
    IdentitySystem_ind_beta (D : forall a : A, R a -> Type) (d : D a0 r0) 
      : IdentitySystem_ind D d a0 r0 = d
  }.

(** The mapping space between two pointed type families over the same base point, is a family of maps that preserves the basepoint. *)
Definition pfamMap {A : Type} {a0 : A} 
  (R S : A -> Type) (r0 : R a0) (s0 : S a0) : Type
  := {f : forall a : A, R a -> S a & f a0 r0 = s0}.

(** We can also consider pointed homotopies between maps of pointed type families. *)
Definition path_pfamMap {A : Type} {a0 : A}
  {R S : A -> Type} {r0 : R a0} {s0 : S a0} 
  (f g : pfamMap R S r0 s0) : Type
  := { p : forall a : A, pr1 f a == pr1 g a & p a0 r0 = pr2 f @ (pr2 g)^}.

(** Given that a pointed type family [R], [r0] is an identity system, then the mapping space of pointed type families starting at [R] is homotopy contractible. This is a weak form of Theorem 5.8.2, (i) implies (ii). *)
Definition homocontr_pfamMap_identitysystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem R r0} 
  (S : A -> Type) (s0 : S a0) 
  : exists f : pfamMap R S r0 s0, forall g, path_pfamMap f g.
Proof.
  pose (to_S := IdentitySystem_ind (fun a _ => S a) s0).
  pose proof (to_S_beta := IdentitySystem_ind_beta (fun a _ => S a) s0).
  snrefine ((to_S; to_S_beta); _).
  intro g.
  exists (IdentitySystem_ind (fun a r => to_S a r = pr1 g a r) 
    (to_S_beta @ (pr2 g)^)).
  snrapply IdentitySystem_ind_beta.
Defined.

(** If a pointed type family [R], [r0] has homotopy contractible mapping spaces as in the sense above, then [fun p => transport R p r0] is a fiber-wise equivalence. This is a strong form of Theorem 5.8.2, (ii) implies (iii). *)
Definition equiv_path_homocontr_pfamMap {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0)
  (H : forall S : A -> Type, forall s0 : S a0, exists f : pfamMap R S r0 s0, forall g, path_pfamMap f g) (a : A) 
  : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  pose (inv (a : A) := (pr1 o pr1) (H (fun a => a0 = a) 1) a).
  pose proof (inv_beta := (pr2 o pr1) (H (fun a => a0 = a) 1)); 
  cbn in inv_beta.
  snrapply (isequiv_adjointify _ (inv a)); cbn.
  - intro r.
    snrefine (_ @ _).
    + exact ((pr1 o pr1) (H R r0) a r).
    + exact ((pr1 (pr2 (H R r0) 
      (fun a r => transport R (inv a r) r0; 
      ((ap (fun x => transport R x r0) inv_beta))))) a r)^.
    + exact ((pr1 (pr2 (H R r0) (fun a r => r; (idpath r0)))) a r).
  - by intros [].
Defined.

(** For any pointed type family [R], [r0] such that the total space of [R] is contractible, then [R], [r0] is an identity system. This is Theorem 5.8.2, (iv) implies (i). *)
Definition IsIdentitySystem_contr_sigma {A : Type} {a0 : A} (R : A -> Type) 
  (r0 : R a0) {C : Contr (sig R)} 
  : IsIdentitySystem R r0.
Proof.
  snrapply Build_IsIdentitySystem.
  - intros D d0 a r.
    exact (transport 
      (fun ar : sig R => D (pr1 ar) (pr2 ar)) 
      ((@contr _ C (a0; r0))^ @ @contr _ C (a; r)) d0).
  - intros D d0; cbn.
    by lhs nrapply (ap (fun x => transport _ x _) (concat_Vp _)).
Defined.

(** The fundamental theorem of identity systems tells us that these four different properties are logically equivalent. *)
Definition FundamentalThmIdentitySystems {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0)
  : (IsIdentitySystem R r0 -> forall S : A -> Type, forall s0 : S a0, exists f : pfamMap R S r0 s0, forall g, path_pfamMap f g)
    * ((forall S : A -> Type, forall s0 : S a0, 
      exists f : pfamMap R S r0 s0, forall g, path_pfamMap f g) 
      -> forall a : A, IsEquiv (fun p : a0 = a => transport R p r0))
    * ((forall a : A, IsEquiv (fun p : a0 = a => transport R p r0)) 
      -> Contr (sig R))
    * (Contr (sig R) -> IsIdentitySystem R r0).
Proof.
  repeat split.
  - nrapply homocontr_pfamMap_identitysystem.
  - nrapply equiv_path_homocontr_pfamMap.
  - intros e_transport.
    exact (contr_sigma_refl_rel a0 R r0 
      (fun a => @Build_Equiv _ _ _ (e_transport a))).
  - nrapply IsIdentitySystem_contr_sigma.
Defined.

(** It is useful to have some composites of the above. Given an identity system, transporting the point [r0] induces a fiber-wise equivalence between the based path type on [a0] and [R]. This is Theorem 5.8.2 (i) implies (iii) from the Book. *)
Global Instance isequiv_transport_IsIdentitySystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} (a : A) 
  : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  nrapply equiv_path_homocontr_pfamMap.
  by nrapply homocontr_pfamMap_identitysystem.
Defined.

Definition equiv_transport_IsIdentitySystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} (a : A) 
  : (a0 = a) <~> R a 
  := Build_Equiv _ _ (fun p => transport R p r0) _.
