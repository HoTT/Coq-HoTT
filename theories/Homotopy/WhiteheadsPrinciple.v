From HoTT Require Import Basics Types.
Require Import Pointed.
Require Import WildCat.Core HFiber.
Require Import Truncations.
Require Import Algebra.Groups.Group.
Require Import Homotopy.HomotopyGroup.

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
  srapply isequiv_surj_emb.
  srapply BuildIsSurjection.
  cbn; intro b.
  pose proof (@center _ (i (tr b))) as p.
  revert p.
  apply Trunc_functor.
  apply sig_ind.
  srapply Trunc_ind.
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
           {ii : forall x, IsEquiv (fmap loops (pmap_from_point f x)) }
  : IsEquiv f.
Proof.
  srapply (isequiv_issurj_tr0_isequiv_ap f).
  intros x y.
  apply isequiv_inhab_codomain.
  intro p.
  apply (ap (@tr 0 _)) in p.
  apply (@equiv_inj _ _ _ i (tr x) (tr y)) in p.
  apply (equiv_path_Tr _ _)^-1 in p.
  strip_truncations.
  destruct p.
  cbn in ii.
  snapply (isequiv_homotopic _ (H:=ii x)).
  exact (fun _ => concat_1p _ @ concat_p1 _).
Defined.

(** When the types are 0-connected and the map is pointed, just one [loops_functor] needs to be checked. *)
Definition isequiv_is0connected_isequiv_loops
           `{Univalence} {A B : pType} `{IsConnected 0 A} `{IsConnected 0 B}
           (f : A ->* B)
           (e : IsEquiv (fmap loops f))
  : IsEquiv f.
Proof.
  apply isequiv_isbij_tr0_isequiv_loops.
  (** The pi_0 condition is trivial because [A] and [B] are 0-connected. *)
  1: apply isequiv_contr_contr.
  (** Since [A] is 0-connected, it's enough to check the [loops_functor] condition for the basepoint. *)
  rapply conn_point_elim.
  (** The [loops_functor] condition for [pmap_from_point f _] is equivalent to the [loops_functor] condition for [f] with its given pointing. *)
  srapply isequiv_homotopic'.
  - exact (equiv_concat_lr (point_eq f) (point_eq f)^ oE (Build_Equiv _ _ _ e)).
  - intro r.
    simpl.
    hott_simpl.
Defined.

(** Truncated Whitehead's principle (8.8.3) *)
Definition whiteheads_principle
           {ua : Univalence} {A B : Type} {f : A -> B}
           (n : trunc_index) {H0 : IsTrunc n A} {H1 : IsTrunc n B}
           {i  : IsEquiv (Trunc_functor 0 f)}
           {ii : forall (x : A) (k : nat), IsEquiv (fmap (Pi k.+1) (pmap_from_point f x)) }
  : IsEquiv f.
Proof.
  revert A B H0 H1 f i ii.
  induction n as [|n IHn].
  1: intros; apply isequiv_contr_contr.
  intros A B H0 H1 f i ii.
  nrefine (@isequiv_isbij_tr0_isequiv_loops ua _ _ f i _).
  intro x.
  nrefine (isequiv_homotopic (@ap _ _ f x x) _).
  2:{intros p; cbn.
     symmetry; exact (concat_1p _ @ concat_p1 _). }
  pose proof (@istrunc_paths _ _ H0 x x) as h0.
  pose proof (@istrunc_paths _ _ H1 (f x) (f x)) as h1.
  nrefine (IHn (x=x) (f x=f x) h0 h1 (@ap _ _ f x x) _ _).
  - pose proof (ii x 0) as h2.
    unfold is0functor_pi in h2; cbn in h2.
    refine (@isequiv_homotopic _ _ _ _ h2 _).
    apply (O_functor_homotopy (Tr 0)); intros p.
    exact (concat_1p _ @ concat_p1 _).
  - intros p k; revert p.
    assert (h3 : forall (y:A) (q:x=y),
               IsEquiv (fmap (Pi k.+1) (pmap_from_point (@ap _ _ f x y) q))).
    2:exact (h3 x).
    intros y q. destruct q.
    snrefine (isequiv_homotopic _ _).
    1: exact (fmap (Pi k.+1) (fmap loops (pmap_from_point f x))).
    2:{ tapply (fmap2 (Pi k.+1)); srefine (Build_pHomotopy _ _).
        - intros p; cbn.
          exact (concat_1p _ @ concat_p1 _).
        - reflexivity. }
    nrefine (isequiv_commsq _ _ _ _ (fmap_pi_loops k.+1 (pmap_from_point f x))).
    2-3:exact (equiv_isequiv (pi_loops _ _)).
    exact (ii x k.+1).
Defined.

(** A pointed map between [n]-connected, [n.+1]-truncated types which induces an equivalence on [Pi n.+1] is an equivalence.  Only the top homotopy group of such a type is non-trivial, so this is the only condition Whitehead's principle leaves to check. *)
Definition isequiv_pi_connected_truncated `{Univalence} (n : nat) {X Y : pType}
  (f : X ->* Y)
  (cX : IsConnected n X) (tX : IsTrunc n.+1 X)
  (cY : IsConnected n Y) (tY : IsTrunc n.+1 Y)
  (e : IsEquiv (fmap (pPi n.+1) f))
  : IsEquiv f.
Proof.
  revert X Y f cX tX cY tY e.
  induction n as [|n IHn]; intros X Y f cX tX cY tY e.
  - snapply (isequiv_is0connected_isequiv_loops (A:=X) (B:=Y) f).
    1,2: assumption.
    (** The loop spaces are sets, so [Tr 0] reflects the equivalence. *)
    napply (@isequiv_O_inverts (Tr 0)).
    1,2: rapply istrunc_loops.
    exact e.
  - snapply (isequiv_is0connected_isequiv_loops (A:=X) (B:=Y) f).
    1,2: rapply is0connected_isconnected.
    (** [fmap loops f] satisfies the hypotheses one level down, using that [Pi n.+1 o loops] is [Pi n.+2] up to the equivalences [pi_loops]. *)
    assert (el : IsEquiv (fmap (pPi n.+1) (fmap loops f))).
    { napply (isequiv_commsq _ _ (pi_loops n.+1 X) (pi_loops n.+1 Y)).
      1: exact (fmap_pi_loops n.+1 f).
      all: exact _. }
    exact (IHn (loops X) (loops Y) (fmap loops f)
             (isconnected_loops _) (istrunc_loops _)
             (isconnected_loops _) (istrunc_loops _) el).
Defined.
