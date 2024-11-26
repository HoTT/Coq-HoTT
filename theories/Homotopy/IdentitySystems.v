Require Import Basics.
Require Import Types.Sigma Types.Equiv Types.Paths.
Require Import HoTT.Tactics.

(** * Characterization of identity types by identity systems *)

(** See Homotopy/EncodeDecode.v for a related characterization of identity types. *)

(** To avoid dependencies coming from Pointed.Core, we will write out some of the definitions found there. Let [A : Type], together with a distinguished base point [a0 : A]. A pointed type family is a type family [R : A -> Type], together with a distinguished point [r0 : R a0]. A pointed type family [(R; r0)] is called an identity system if it satisfies the J-rule. Given a pointed type family [(R; r0)], the fundamental theorem of identity systems (Theorem 5.8.2 from the HoTT Book) tells us that the following are equivalent: (i) an identity system structure on [(R; r0)], (ii) homotopy contractibility of the space of pointed type family maps from [(R; r0)] to any pointed type family [(S; s0)], (iii) transport along [R] being an equivalence, and (iv) the total space of [R] being contractible. *)
Class IsIdentitySystem {A : Type} {a0 : A} (R : A -> Type) (r0 : R a0) := {
    idsys_ind (D : forall a : A, R a -> Type) (d : D a0 r0) (a : A) (r : R a)
      : D a r;
    idsys_ind_beta (D : forall a : A, R a -> Type) (d : D a0 r0)
      : idsys_ind D d a0 r0 = d
  }.

(** The mapping space between two pointed type families over the same pointed type is a family of maps that preserves the distinguished points. *)
Definition pfamMap {A : Type} {a0 : A} (R S : A -> Type) (r0 : R a0) (s0 : S a0)
  := {f : forall a : A, R a -> S a & f a0 r0 = s0}.

(** A pointed homotopy between maps of pointed type families is a family of homotopies that is pointed in the fiber over [a0]. *)
Definition pfammap_homotopy {A : Type} {a0 : A} {R S : A -> Type} {r0 : R a0} {s0 : S a0}
  (f g : pfamMap R S r0 s0)
  := { p : forall a : A, pr1 f a == pr1 g a & p a0 r0 = pr2 f @ (pr2 g)^}.

Global Instance reflexive_pfammap_homotopy {A : Type} {a0 : A}
  {R S : A -> Type} {r0 : R a0} {s0 : S a0}
  : Reflexive (pfammap_homotopy (r0:=r0) (s0:=s0)).
Proof.
  intro g.
  snrefine (_;_).
  - exact (fun _ _ => idpath).
  - cbn; symmetry.
    exact (concat_pV _).
Defined.

(** We weaken part (ii) of Theorem 5.8.2. Instead of requiring that the mapping space is contractible, we will only require it to be homotopy contractible, i.e. it is inhabited and there is a homotopy between every map and the chosen map. This allows us to avoid function extensionality. Given that a pointed type family [(R; r0)] is an identity system, then the mapping space of pointed type families from [(R; r0)] to any [(S; s0)] is homotopy contractible. This is a weak form of Theorem 5.8.2, (i) implies (ii). *)
Definition homocontr_pfammap_identitysystem {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem R r0}
  (S : A -> Type) (s0 : S a0)
  : exists f : pfamMap R S r0 s0, forall g, pfammap_homotopy f g.
Proof.
  pose (to_S := idsys_ind (fun a _ => S a) s0).
  pose proof (to_S_beta := idsys_ind_beta (fun a _ => S a) s0).
  snrefine ((to_S; to_S_beta); _).
  intro g.
  exists (idsys_ind (fun a r => to_S a r = pr1 g a r) (to_S_beta @ (pr2 g)^)).
  snrapply idsys_ind_beta.
Defined.

(** If a pointed type family [(R; r0)] has homotopy contractible mapping spaces in the sense above, then [fun p => transport R p r0] is a fiberwise equivalence. This is a strong form of Theorem 5.8.2, (ii) implies (iii). *)
Definition equiv_path_homocontr_pfammap {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0)
  (H : forall S : A -> Type, forall s0 : S a0,
    exists f : pfamMap R S r0 s0, forall g, pfammap_homotopy f g)
  (a : A)
  : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  pose (inv := (H (fun a => a0 = a) 1).1.1).
  pose proof (inv_beta := (H (fun a => a0 = a) 1).1.2); cbn in inv_beta.
  snrapply (isequiv_adjointify _ (inv a)); cbn.
  - destruct (H R r0) as [[f fp] h].
    pose proof (h' := fun g => (h g).1 a); cbn in h'; clear h fp.
    (* Both sides are the underlying maps of [pfammap]s, so [h'] says that both are homotopic to [f a]. *)
    transitivity (f a).
    + symmetry.
      nrefine (h' (fun _ _ => transport R (inv _ _) r0; _)).
      exact (ap (fun x => transport R x r0) inv_beta).
    + exact (h' (_; idpath)).
  - by intros [].
Defined.

(** Given that some type family [R] is fiberwise equivalent to identity types based at [a0], then the total space [sig R] is contractible. This is a stronger form of Theorem 5.8.2, (iii) implies (iv). *)
Definition contr_sigma_equiv_path {A : Type} {a0 : A}
  (R : A -> Type) (f : forall a, (a0 = a) <~> R a)
  : Contr (sig R).
Proof.
  rapply contr_equiv'.
  1: exact (equiv_functor_sigma_id f).
  apply contr_basedpaths.
Defined.

(** Any pointed type family [(R; r0)] with contractible total space is an identity system. This is Theorem 5.8.2, (iv) implies (i). *)
Definition identitysystem_contr_sigma {A : Type} {a0 : A} (R : A -> Type)
  (r0 : R a0) {C : Contr (sig R)}
  : IsIdentitySystem R r0.
Proof.
  snrapply Build_IsIdentitySystem.
  - intros D d0 a r.
    exact (transport (fun ar : sig R => D (pr1 ar) (pr2 ar))
             (path_contr (a0; r0) (a; r)) d0).
  - intros D d0; cbn; unfold path_contr.
    nrapply (transport2 _ (concat_Vp _)).
Defined.

(** Assuming function extensionality, pointed homotopy contractible fiberwise mapping spaces of pointed type families are contractible. We thus obtain the proper statement of Theorem 5.8.2. *)
Definition contr_pfammap_homocontr `{Funext} {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0)
  (S : A -> Type) (s0 : S a0)
  (fH : exists f : pfamMap R S r0 s0, forall g, pfammap_homotopy f g)
  : Contr (pfamMap R S r0 s0).
Proof.
  snrapply Build_Contr.
  - exact fH.1.
  - intro g.
    snrapply path_sigma; cbn.
    + funext a.
      nrapply path_forall.
      exact ((fH.2 g).1 a).
    + transport_path_forall_hammer.
      lhs nrapply transport_paths_l.
      nrapply moveR_Vp.
      nrapply moveL_pM.
      symmetry.
      exact (fH.2 g).2.
Defined.

(** The fiberwise mapping spaces of pointed type families are pointed homotopy contractible if they are contractible. *)
Definition homocontr_pfammap_contr {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0)
  (S : A -> Type) (s0 : S a0)
  (cp : Contr (pfamMap R S r0 s0))
  : exists f : pfamMap R S r0 s0, forall g, pfammap_homotopy f g.
Proof.
  snrefine (_;_).
  - exact (@center _ cp).
  - intro g.
    by destruct (@contr _ cp g).
Defined.

(** The fundamental theorem of identity systems is now proven. It is useful to write down some of the composite implications. Given an identity system [(R; r0)], transporting the point [r0] induces a fiberwise equivalence between the based path type [a0 = x] and [R x]. This is Theorem 5.8.2 (i) implies (iii). *)
Global Instance isequiv_transport_identitysystem {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} (a : A)
  : IsEquiv (fun p : a0 = a => transport R p r0).
Proof.
  nrapply equiv_path_homocontr_pfammap.
  by nrapply homocontr_pfammap_identitysystem.
Defined.

Definition equiv_transport_identitysystem {A : Type} {a0 : A}
  (R : A -> Type) (r0 : R a0) `{!IsIdentitySystem _ r0} (a : A)
  : (a0 = a) <~> R a
  := Build_Equiv _ _ (fun p => transport R p r0) _.

(** A more general version of Theorem 5.8.2 (iii) implies (i) is proven in Basics/Equivalences.v as [equiv_path_ind]. The original statement is recovered if [e] is assumed to be [fun p => transport R p r0]. *)

(** Theorem 5.8.2, (iv) implies (iii), can be proven with a nice method due to Rijke. *)
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

(** This is another result for characterizing the path types of [A] when given an equivalence [e : B <~> A], such as an [issig] lemma for [A]. It can help Coq to deduce the type family [P] if [revert] is used to move [a0] and [a1] into the goal, if needed. *)
Definition equiv_path_along_equiv {A B : Type} {P : A -> A -> Type}
  (e : B <~> A)
  (K : forall b0 b1 : B, P (e b0) (e b1) <~> b0 = b1)
  : forall a0 a1 : A, P a0 a1 <~> a0 = a1.
Proof.
  equiv_intros e b0 b1.
  nrefine (_ oE K b0 b1).
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
