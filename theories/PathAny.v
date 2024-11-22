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

(** Given that some type family [R] is fiber-wise equivalent to identity types based at [a], then the total space [sig R] is contractible. This is Theorem 5.8.2 (iii) => (iv). *)
Definition contr_sigma_refl_rel {A : Type}
  (a : A) (R : A -> Type) (r0 : R a)
  (f : forall b, (a = b) <~> R b)
  : Contr (sig R).
Proof.
  rapply contr_equiv'.
  1: exact (equiv_functor_sigma_id f).
  apply contr_basedpaths.
Defined.

(** A pointed type family is an identity system if it satisfies the J-rule. *)
Class IsIdentitySystem {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0)
  := 
  { IdentitySystem_ind (D : forall a : A, R a -> Type) (d : D a0 r0) (a : A) (r : R a) 
      : D a r;
    
    IdentitySystem_ind_beta (D : forall a : A, R a -> Type) (d : D a0 r0) 
      : IdentitySystem_ind D d a0 r0 = d
  }.

(** Given an identity system, transporting the point [r0] induces a fiber-wise equivalence between the based path type on [a0] and [R]. This is Theorem 5.8.2 (i) => (iii) from the Book. *)
Global Instance isequiv_transport_IsIdentitySystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} 
  (a : A) : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  pose (to_paths := IdentitySystem_ind (fun a _ => a0 = a) (idpath _)).
  pose (to_paths_beta := IdentitySystem_ind_beta (fun a _ => a0 = a) (idpath _)).
  snrapply isequiv_adjointify.
  - exact (to_paths a).
  - exact ((IdentitySystem_ind 
      (fun (a' : A) (r' : R a') => transport R (to_paths a' r') r0 = r') 
      (ap (fun x => transport R x r0) to_paths_beta)) 
      a).
  - by intros [].
Defined.

Definition equiv_transport_IsIdentitySystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} 
  (a : A) : (a0 = a) <~> R a 
  := Build_Equiv _ _ (fun p => transport R p r0) _.

(** I could use pointed maps, but this will introduce more dependencies. It might be wise to factor out this part of lemma 5.8.2. and relocate it, so that this file can depend on less, and add the full statement into contrib. Notice that we also need funext to make this work, so it isn't as nice as i) <=> iii) <=> iv) *)
Definition pfamMap {A : Type} {a0 : A} 
  (R S : A -> Type) (r0 : R a0) (s0 : S a0) : Type
  := {f : forall a : A, R a -> S a & f a0 r0 = s0}.

Definition path_pfamMap {A : Type} {a0 : A}
  {R S : A -> Type} {r0 : R a0} {s0 : S a0} 
  (f g : pfamMap R S r0 s0) : Type
  := { p : forall a : A, pr1 f a == pr1 g a & p a0 r0 = pr2 f @ (pr2 g)^}.

(** A weak form of (i) => (ii) *)
Definition homocontr_pfamMap_identitysystem {A : Type} {a0 : A} 
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem R r0} 
  (S : A -> Type) (s0 : S a0) 
  : exists f : pfamMap R S r0 s0, forall g, path_pfamMap f g.
Proof.
  pose (to_S := IdentitySystem_ind (fun a _ => S a) s0).
  pose proof (to_S_beta := IdentitySystem_ind_beta (fun a _ => S a) s0).
  snrefine ((to_S; to_S_beta); _).
  intro g; cbn.
  exists (IdentitySystem_ind (fun a r => to_S a r = pr1 g a r) (to_S_beta @ (pr2 g)^)).
  snrapply IdentitySystem_ind_beta.
Defined.

(** (ii) => (iii). I literally hate this. *)
Global Instance equiv_path_contr_pfamMap {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0) 
  (H : forall S : A -> Type, forall s0 : S a0, Contr (pfamMap R S r0 s0))
  (a : A) : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  snrapply isequiv_adjointify.
  - exact (pr1 (@center (pfamMap _ _ _ _) (H (fun a => a0 = a) 1)) a).
  - intro r.
    pose (c := @center (pfamMap _ _ _ _) (H R r0)).
    srefine (_ @ _).
    + exact (pr1 c a r).
    + symmetry.
      pose (inv := fun a r => transport R (pr1 (@center (pfamMap _ _ _ _) (H (fun a => a0 = a) 1)) a r) r0).
      pose (inv0 := (ap (fun x => transport R x r0) (pr2 (@center (pfamMap _ _ _ _) (H (fun a => a0 = a) 1))))).
      revert r; apply apD10.
      revert a; apply apD10.
      exact (ap pr1 (contr (@exist (forall a : A, R a -> R a) (fun f => f a0 r0 = r0) inv inv0))).
    + revert r; apply apD10.
      revert a; apply apD10.
      exact (ap pr1 (contr (@exist (forall a : A, R a -> R a) (fun f => f a0 r0 = r0) (fun a r => r) 1))).
  - intros []; cbn.
    exact ((pr2 (@center (pfamMap _ _ _ _) (H (fun a => a0 = a) 1)))).
Defined.
