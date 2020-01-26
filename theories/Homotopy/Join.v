(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import HProp.
Require Import HSet.
Require Import NullHomotopy.
Require Import Extensions.
Require Import Colimits.Pushout.
Require Import Truncations.
Import TrM.

Local Open Scope path_scope.

(** * Joins *)

(** The join is the pushout of two types under their product. *)
Section Join.

  Definition Join (A : Type@{i}) (B : Type@{j})
    := Pushout@{k i j k} (@fst A B) (@snd A B).

  Definition joinl {A B} : A -> Join A B
    := fun a => @pushl (A*B) A B fst snd a.

  Definition joinr {A B} : B -> Join A B
    := fun b => @pushr (A*B) A B fst snd b.

  Definition jglue {A B} a b : joinl a = joinr b
    := @pglue (A*B) A B fst snd (a , b).

  Definition Join_ind {A B : Type} (P : Join A B -> Type)
    (P_A : forall a, P (joinl a)) (P_B : forall b, P (joinr b))
    (P_g : forall a b, DPath P (jglue a b) (P_A a) (P_B b))
    : forall (x : Join A B), P x.
  Proof.
    serapply (Pushout_ind P P_A P_B).
    intros [a b].
    apply dp_path_transport^-1.
    exact (P_g a b).
  Defined.

  Definition Join_ind_beta_jglue {A B : Type} (P : Join A B -> Type)
    (P_A : forall a, P (joinl a)) (P_B : forall b, P (joinr b))
    (P_g : forall a b, DPath P (jglue a b) (P_A a) (P_B b)) a b
    : dp_apD (Join_ind P P_A P_B P_g) (jglue a b) = P_g a b.
  Proof.
    apply dp_apD_path_transport.
    serapply Pushout_ind_beta_pglue.
  Defined.

  Definition Join_rec {A B P : Type} (P_A : A -> P) (P_B : B -> P)
    (P_g : forall a b, P_A a = P_B b) : Join A B -> P.
  Proof.
    serapply (Pushout_rec P P_A P_B).
    intros [a b].
    apply P_g.
  Defined.

  Definition Join_rec_beta_jglue {A B P : Type} (P_A : A -> P)
    (P_B : B -> P) (P_g : forall a b, P_A a = P_B b) a b
    : ap (Join_rec P_A P_B P_g) (jglue a b) = P_g a b.
  Proof.
    serapply Pushout_rec_beta_pglue.
  Defined.

  (** Joining with a contractible type produces a contractible type *)
  Global Instance contr_join A B `{Contr A} : Contr (Join A B).
  Proof.
    exists (pushl (center A)).
    intros y; simple refine (Pushout_ind _ _ _ _ y).
    - intros a; apply ap, contr.
    - intros b; exact (pglue (center A , b)).
    - intros [a b]; cbn.
      refine ( _ @ apD (fun a' => jglue a' b) (contr a)^).
      rewrite transport_paths_r, transport_paths_FlFr; cbn.
      rewrite ap_V, inv_V, concat_pp_p.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

  (** Join is symmetric *)
  Definition join_sym A B : Join A B <~> Join B A.
  Proof.
    unfold Join; refine (pushout_sym oE _).
    refine (equiv_pushout (equiv_prod_symm A B) 1 1 _ _);
      intros [a b]; reflexivity.
  Defined.

  Definition join_natsq_v {A B : Type} {a a' : A} {b b' : B}
    (p : a = a') (q : b = b')
    : PathSquare (ap joinl p) (ap joinr q) (jglue a b) (jglue a' b').
  Proof.
    destruct p, q.
    apply sq_refl_v.
  Defined.

  Definition join_natsq_h {A B : Type} {a a' : A} {b b' : B}
    (p : a = a') (q : b = b')
    : PathSquare (jglue a b) (jglue a' b') (ap joinl p) (ap joinr q).
  Proof.
    destruct p, q.
    apply sq_refl_h.
  Defined.

  Definition functor_join {A B C D} (f : A -> C) (g : B -> D)
    : Join A B -> Join C D.
  Proof.
    serapply Join_rec.
    1: intro a; apply joinl, f, a.
    1: intro b; apply joinr, g, b.
    intros a b.
    apply jglue.
  Defined.

  Definition functor_join_compose {A B C D E F}
    (f : A -> C) (g : B -> D) (h : C -> E) (i : D -> F)
    : functor_join (h o f) (i o g) == functor_join h i o functor_join f g.
  Proof.
    serapply Join_ind.
    1,2: reflexivity.
    intros a b.
    simpl.
    apply sq_dp^-1.
    apply sq_1G.
    symmetry.
    rewrite ap_compose.
    rewrite 3 Join_rec_beta_jglue.
    reflexivity.
  Defined.

  Definition functor_join_idmap {A}
    : functor_join idmap idmap == (idmap : Join A A -> Join A A).
  Proof.
    serapply Join_ind.
    1,2: reflexivity.
    intros a b.
    cbn; apply dp_paths_FlFr.
    rewrite Join_rec_beta_jglue.
    rewrite ap_idmap, concat_p1.
    apply concat_Vp.
  Defined.

  Global Instance isequiv_functor_join {A B C D}
    (f : A -> C) `{!IsEquiv f} (g : B -> D) `{!IsEquiv g}
    : IsEquiv (functor_join f g).
  Proof.
    serapply isequiv_adjointify.
    1: apply (functor_join f^-1 g^-1).
    1,2: serapply Join_ind.
    1,2: intro; simpl; apply ap, eisretr.
    2,3: intro; simpl; apply ap, eissect.
    1,2: intros c d.
    1,2: apply sq_dp^-1.
     1 : rewrite (ap_compose _ (functor_join f g)).
     2 : rewrite (ap_compose (functor_join f g)).
    1,2: rewrite 2 Join_rec_beta_jglue, ap_idmap.
    1,2: apply join_natsq_v.
  Defined.

  Definition equiv_functor_join {A B C D} (f : A <~> C) (g : B <~> D)
    : Join A B <~> Join C D := Build_Equiv _ _ (functor_join f g) _.

  (** The join of hprops is an hprop *)
  Global Instance ishprop_join `{Funext} A B `{IsHProp A} `{IsHProp B} : IsHProp (Join A B).
  Proof.
    apply hprop_inhabited_contr.
    unfold Join.
    refine (Pushout_rec _ _ _ (fun _ => path_ishprop _ _)).
    - intros a; apply contr_join.  
      exact (contr_inhabited_hprop A a).
    - intros b; refine (trunc_equiv (Join B A) (join_sym B A)).
      apply contr_join.
      exact (contr_inhabited_hprop B b).
  Defined.

  (** And coincides with their disjunction *)
  Definition equiv_join_hor `{Funext} A B `{IsHProp A} `{IsHProp B} 
    : Join A B <~> hor A B.
  Proof.
    apply equiv_iff_hprop.
    - refine (Pushout_rec _ (fun a => tr (inl a)) (fun b => tr (inr b)) (fun _ => path_ishprop _ _)).
    - apply Trunc_rec, push.
  Defined.

  (** Joins add connectivity *)
  Global Instance isconnected_join `{Univalence} {m n : trunc_index}
         (A B : Type) `{IsConnected m A} `{IsConnected n B}
    : IsConnected (m +2+ n) (Join A B).
  Proof.
    apply isconnected_from_elim; intros C ? k.
    pose proof (istrunc_extension_along_conn
                  (fun b:B => tt) (fun _ => C) (k o pushr)).
    unfold ExtensionAlong in *.
    transparent assert (f : (A -> {s : Unit -> C &
                                   forall x, s tt = k (pushr x)})).
    { intros a; exists (fun _ => k (pushl a)); intros b.
      exact (ap k (jglue a b)). }
    assert (h := isconnected_elim
                   m {s : Unit -> C & forall x : B, s tt = k (pushr x)} f).
    unfold NullHomotopy in *; destruct h as [[c g] h].
    exists (c tt).
    srefine (Pushout_ind _ _ _ _).
    - intros a; cbn. exact (ap10 (h a)..1 tt).
    - intros b; cbn. exact ((g b)^).
    - intros [a b].
      rewrite transport_paths_FlFr, ap_const, concat_p1; cbn.
      subst f; set (ha := h a); clearbody ha; clear h;
      assert (ha2 := ha..2); set (ha1 := ha..1) in *;
      clearbody ha1; clear ha; cbn in *.
      rewrite <- (inv_V (ap10 ha1 tt)).
      rewrite <- inv_pp.
      apply inverse2.
      refine (_ @ apD10 ha2 b); clear ha2.
      rewrite transport_forall_constant, transport_paths_FlFr.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

End Join.

(** Diamond lemmas for Join *)
Section Diamond.

  Context {A B : Type}.

  Definition Diamond (a a' : A) (b b' : B)
    := PathSquare (jglue a b) (jglue a' b')^ (jglue a b') (jglue a' b)^.

  Definition diamond_h {a a' : A} (b b' : B) (p : a = a')
    : Diamond a a' b b'.
  Proof.
    destruct p.
    apply sq_path.
    exact (concat_pV _ @ (concat_pV _)^).
  Defined.

  Definition diamond_v (a a' : A) {b b' : B} (p : b = b')
    : Diamond a a' b b'.
  Proof.
    destruct p.
    by apply sq_path.
  Defined.

  Lemma diamond_symm (a : A) (b : B)
    : diamond_v a a 1 = diamond_h b b 1.
  Proof.
    unfold diamond_v, diamond_h.
    symmetry; apply ap, concat_pV.
  Defined.

End Diamond.

Definition diamond_twist {A : Type} {a a' : A} (p : a = a')
  : DPath (fun x => Diamond a' x a x) p
    (diamond_v a' a 1) (diamond_h a a' 1).
Proof.
  destruct p.
  apply diamond_symm.
Defined.

