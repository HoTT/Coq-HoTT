(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesFunext Fibrations.
Require Import Modalities.Modality Truncations.
Import TrM.
Require Import Spaces.BAut.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * Rigid types *)

Class IsRigid (A : Type) := 
  path_aut_rigid : forall f g : A <~> A, f == g.

(** Assuming funext, rigidity is equivalent to contractibility of [A <~> A]. *)

Global Instance contr_aut_rigid `{Funext} (A : Type) `{IsRigid A}
  : Contr (A <~> A).
Proof.
  exists equiv_idmap.
  intros f; apply path_equiv, path_arrow, path_aut_rigid.
Defined.

(** Assuming univalence, rigidity is equivalent to contractibility of [BAut A]. *)

Global Instance contr_baut_rigid `{Univalence} {A : Type} `{IsRigid A}
  : Contr (BAut A).
Proof.
  refine (contr_trunc_conn (Tr 0)).
  intros Z W; baut_reduce.
  refine (trunc_equiv (A <~> A)
                      (path_baut (point (BAut A)) (point (BAut A)))).
Defined.

Definition rigid_contr_Baut `{Univalence} {A : Type} `{Contr (BAut A)}
  : IsRigid A.
Proof.
  unfold IsRigid.
  equiv_intro ((path_baut (point (BAut A)) (point (BAut A)))^-1) f.
  equiv_intro ((path_baut (point (BAut A)) (point (BAut A)))^-1) g.
  apply ap10, ap, ap, path_contr.
Defined.

(** ** HProps are rigid *)

Global Instance rigid_ishprop
       (A : Type) `{IsHProp A} : IsRigid A.
Proof.
  intros f g x; apply path_ishprop.
Defined.

(** ** Equivalences of BAut *)

(** Under a truncatedness/connectedness assumption, multiplying by a rigid type doesn't change the automorphism oo-group. *)

(** A lemma: a "monoid homomorphism up to homotopy" between endomorphism monoids restricts to automorphism groups. *)
Definition aut_homomorphism_end `{Funext} {X Y : Type}
           (M : (X -> X) -> (Y -> Y))
           (Mid : M idmap == idmap)
           (MC : forall f g, M (g o f) == M g o M f)
  : (X <~> X) -> (Y <~> Y).
Proof.
  assert (MS : forall f g, Sect f g -> Sect (M f) (M g)).
  { intros g f s x.
    transitivity (M (f o g) x).
    + symmetry. refine (MC g f x).
    + transitivity (M idmap x).
      * apply ap10, ap, path_arrow.
        intros y; apply s.
      * apply Mid. }
  assert (ME : (forall f, IsEquiv f -> IsEquiv (M f))).
  { intros f ?.
    refine (isequiv_adjointify (M f) (M f^-1) _ _);
      apply MS; [ apply eisretr | apply eissect ]. }
  exact (fun f => (Build_Equiv _ _ (M f) (ME f _))).
Defined.

Definition baut_prod_rigid_equiv `{Univalence}
           (X A : Type) (n : trunc_index)
           `{IsTrunc n.+1 X} `{IsRigid A} `{IsConnected n.+1 A}
  : BAut X <~> BAut (X * A).
Proof.
  refine (Build_Equiv _ _ (baut_prod_r X A) _).
  apply isequiv_surj_emb.
  { apply BuildIsSurjection; intros Z.
    baut_reduce.
    refine (tr (point _ ; _)).
    apply path_sigma_hprop; reflexivity. }
  { apply isembedding_isequiv_ap.
    intros Z W.
    pose (L := fun e : Z <~> W => equiv_functor_prod_r (B := A) e).
    refine (isequiv_commsq
             L (ap (baut_prod_r X A))
             (path_baut Z W)
             (path_baut (baut_prod_r X A Z) (baut_prod_r X A W))
             (fun e => (ap_baut_prod_r X A e)^)).
    refine ((isconnected_elim (Tr (-1)) (A := A) _ _).1).
    { apply contr_inhabited_hprop;
        [ exact _ | refine (merely_isconnected n A) ]. }
    intros a0.
    baut_reduce.
    pose (M := fun f:X*A -> X*A => fun x => fst (f (x,a0))).
    assert (MH : forall (a:A) (f:X*A -> X*A) (x:X),
               fst (f (x,a)) = fst (f (x,a0))).
    { refine (conn_map_elim (Tr n) (unit_name a0) _ _).
      - apply conn_point_incl; assumption.
      - intros; reflexivity. }
    assert (MC : forall (f g :X*A -> X*A), M (g o f) == M g o M f).
    { intros f g x; unfold M.
      transitivity (fst (g (fst (f (x,a0)), snd (f (x,a0))))).
      - reflexivity.
      - apply MH. }
    pose (M' := aut_homomorphism_end M (fun x => 1) MC).
    assert (Mker : forall f, M' f == 1%equiv -> f == 1%equiv).
    { unfold M', M; cbn. intros f p.
      pose (fh := fun x a => (MH a f x) @ p x).
      pose (g := fun x a => snd (f (x,a))).
      assert (ge : forall x, IsEquiv (g x)).
      { apply isequiv_from_functor_sigma.
        refine (isequiv_commsq' _ f
                  (equiv_sigma_prod0 X A) (equiv_sigma_prod0 X A) _).
        intros [x a]; cbn.
        apply path_prod; [ apply fh | reflexivity ]. }
      intros [x a].
      pose (gisid := path_aut_rigid (Build_Equiv _ _ (g x) (ge x)) 1).
      apply path_prod.
      - apply fh.
      - apply gisid. }
    assert (Minj : forall f g, M' f == M' g -> f == g).
    { intros f g p z.
      apply moveL_equiv_M.
      revert z.
      refine (Mker (g^-1 oE f) _).
      intros x.
      refine (MC f g^-1 x @ _).
      change ((M' g)^-1 (M f x) = x).
      apply moveR_equiv_V, p. }
    refine (isequiv_adjointify L M' _ _);
      intros e;
      apply path_equiv, path_arrow;
      try apply Minj;
      intros x; reflexivity. }
Defined.
