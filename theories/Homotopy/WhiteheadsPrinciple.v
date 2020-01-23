Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Fibrations.
Require Import EquivalenceVarieties UnivalenceImpliesFunext.
Require Import Algebra.Group.
Require Import Homotopy.HomotopyGroup.
Require Import Truncations.
Import TrM.

Local Open Scope pointed_scope.
Local Open Scope nat_scope.

(** 8.8.1 *)
Definition isequiv_issurj_tr0_isequiv_ap
           `{Univalence} {A B : Type} (f : A -> B)
           {i  : IsSurjection (Trunc_functor 0 f)}
           {ii : forall x y, IsEquiv (@ap _ _ f x y)}
  : IsEquiv f.
Proof.
  apply (equiv_isequiv_ap_isembedding f)^-1 in ii.
  serapply isequiv_surj_emb.
  serapply BuildIsSurjection.
  cbn; intro b.
  pose proof (@center _ (i (tr b))) as p.
  revert p.
  apply Trunc_functor.
  apply sig_ind.
  serapply Trunc_ind.
  intros a p.
  apply (equiv_path_Tr _ _)^-1 in p.
  strip_truncations.
  exists a.
  exact p.
Defined.

(** 8.8.2 *)
Definition isequiv_isbij_tr0_isequiv_loops
           `{Univalence} {A B : Type} (f : A -> B)
           {i  : IsEquiv (Trunc_functor 0 f)}
           {ii : forall x, IsEquiv (loops_functor (pmap_from_point f x)) }
  : IsEquiv f.
Proof.
  serapply (isequiv_issurj_tr0_isequiv_ap f).
  intros x y.
  apply isequiv_inhab_codomain.
  intro p.
  apply (ap (@tr 0 _)) in p.
  apply (ap (Trunc_functor 0 f)^-1) in p.
  pose proof ((eissect (Trunc_functor 0 f) (tr x))^
              @ p @ eissect (Trunc_functor 0 f) (tr y)) as q.
  clear p.
  apply (equiv_path_Tr _ _)^-1 in q.
  strip_truncations.
  destruct q.
  cbn in ii.
  serapply isequiv_homotopic.
  { intro p.
    exact (1 @ (ap f p @ 1)). }
  1: apply (ii x).
  exact (fun _ => concat_1p _ @ concat_p1 _).
Defined.

(** Truncated Whitehead's principle (8.8.3) *)

Definition whiteheads_principle
           {ua : Univalence} {A B : Type} {f : A -> B}
           (n : trunc_index) {H0 : IsTrunc n A} {H1 : IsTrunc n B}
           {i  : IsEquiv (Trunc_functor 0 f)}
           {ii : forall (x : A) (k : nat), IsEquiv (pi_functor k.+1 (pmap_from_point f x)) }
  : IsEquiv f.
Proof.
  revert A B H0 H1 f i ii.
  induction n as [|n IHn].
  1: intros; apply isequiv_contr_contr.
  intros A B H0 H1 f i ii.
  ntc_refine (@isequiv_isbij_tr0_isequiv_loops ua _ _ f i _).
  intro x.
  ntc_refine (isequiv_homotopic (@ap _ _ f x x) _).
  2:{intros p; cbn.
     symmetry; exact (concat_1p _ @ concat_p1 _). }
  pose proof (@istrunc_paths _ _ H0 x x) as h0.
  pose proof (@istrunc_paths _ _ H1 (f x) (f x)) as h1.
  ntc_refine (IHn (x=x) (f x=f x) h0 h1 (@ap _ _ f x x) _ _).
  - pose proof (ii x 0) as h2.
    unfold pi_functor in h2; cbn in h2.
    refine (@isequiv_homotopic _ _ _ _ h2 _).
    apply O_functor_homotopy; intros p.
    exact (concat_1p _ @ concat_p1 _).
  - intros p k; revert p.
    assert (h3 : forall (y:A) (q:x=y),
               IsEquiv (pi_functor k.+1 (pmap_from_point (@ap _ _ f x y) q))).
    2:exact (h3 x).
    intros y q. destruct q.
    ntc_refine (isequiv_homotopic (pi_functor k.+1 (loops_functor (pmap_from_point f x))) _).
    2:{ apply pi_2functor; srefine (Build_pHomotopy _ _).
        - intros p; cbn.
          refine (concat_1p _ @ concat_p1 _).
        - reflexivity. }
    ntc_refine (isequiv_commsq _ _ _ _ (pi_functor_loops k.+1 (pmap_from_point f x))).
    2-3:refine (equiv_isequiv (pi_loops _ _)).
    exact (ii x k.+1).
Defined.
