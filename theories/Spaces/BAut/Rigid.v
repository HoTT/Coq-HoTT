(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesFunext Fibrations.
Require Import Modalities.Modality HIT.Truncations HIT.Connectedness.
Import TrM.
Require Import Spaces.BAut.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * Rigid types *)

Class IsRigid (A : Type) := 
  contr_baut_rigid : Contr (BAut A).
Existing Instance contr_baut_rigid.

Definition aut_idmap_rigid `{Univalence} {A : Type} `{IsRigid A}
           (f : A <~> A)
  : f == equiv_idmap.
Proof.
  apply ap10, (ap equiv_fun).
  refine ((eissect (path_baut (point _) (point _)) f)^ @ _).
  apply moveR_equiv_V.
  apply path_contr.
Defined.

Definition baut_prod_rigid_equiv `{Univalence}
           (X A : Type) (n : trunc_index)
           `{IsTrunc n.+1 X} `{IsRigid A} `{IsConnected n.+1 A}
  : BAut X <~> BAut (X * A).
Proof.
  pose (f := fun Z:BAut X =>
               (Z * A ; Trunc_functor -1 (ap (fun W => W * A)) (pr2 Z))
               : BAut (X * A)).
  assert (p : f (point (BAut X)) = (point (BAut (X * A))))
    by (apply path_sigma_hprop; reflexivity).
  refine (BuildEquiv _ _ f _).
  apply isequiv_surj_emb.
  { apply BuildIsSurjection; intros Z.
    baut_reduce.
    exact (tr (point _ ; p)). }
  { apply isembedding_isequiv_ap.
    intros Z W; baut_reduce.
    pose (L := fun e : X <~> X => equiv_functor_prod_r (B := A) e).
    refine (isequiv_commsq
             L _
             (path_baut (point (BAut X)) (point (BAut X)))
             (path_baut (point (BAut (X*A))) (point (BAut (X*A))))
             _).
    { intros e; revert e; equiv_intro (equiv_path X X) e; cbn.
      rewrite path_universe_uncurried_equiv_path.
      apply moveR_equiv_M; cbn; unfold pr1_path.
      refine (_ @ ap_compose f pr1
                (path_sigma_hprop (X; tr 1) (X; tr 1) e)).
      unfold f.
      refine (_ @ (ap_compose pr1 (fun Z => Z * A)
                (path_sigma_hprop (X; tr 1) (X; tr 1) e))^).
      rewrite ap_pr1_path_sigma_hprop. unfold L.
      assert (G : forall Y W (e:Y=W),
                 path_universe_uncurried (equiv_functor_prod_r (equiv_path Y W e))
                 = ap (fun Z => Z * A) e).
      { intros ? ? []; cbn.
        apply moveR_equiv_M; cbn.
        apply path_equiv, path_arrow; intros x; reflexivity. }
      apply G. }
    clear f p.
    refine ((isconnected_elim (Tr -1) (A := A) _ _).1).
    { apply contr_inhabited_hprop;
        [ exact _ | refine (merely_isconnected n A) ]. }
    intros a0.
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
    transparent assert (ME : (forall (f:X*A -> X*A), IsEquiv f -> IsEquiv (M f))).
    { intros f ?.
      refine (isequiv_adjointify (M f) (M f^-1) _ _).
      - intros x. transitivity (M (f o f^-1) x).
        + symmetry. refine (MC f^-1 f x).
        + transitivity (M idmap x).
          * apply ap10, ap, path_arrow. 
            intros y; apply eisretr.
          * reflexivity.
      - intros x. transitivity (M (f^-1 o f) x).
        + symmetry. refine (MC f f^-1 x).
        + transitivity (M idmap x).
          * apply ap10, ap, path_arrow. 
            intros y; apply eissect.
          * reflexivity. }
    pose (M' := fun f:X*A<~>X*A => (BuildEquiv _ _ (M f) (ME f _))).
    assert (Misretr : forall e, M' (L e) = e)
      by (intros e; apply path_equiv, path_arrow;
          intros x; reflexivity).
    assert (Mker : forall f, M' f == equiv_idmap -> f == equiv_idmap).
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
      pose (gisid := aut_idmap_rigid (BuildEquiv _ _ (g x) (ge x))).
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
      change ((M g)^-1 (M f x) = x).
      apply moveR_equiv_V, p. }
    refine (isequiv_adjointify L M' _ Misretr).
    intros f.
    apply path_equiv, path_arrow, Minj. 
    intros x; reflexivity. }
Defined.