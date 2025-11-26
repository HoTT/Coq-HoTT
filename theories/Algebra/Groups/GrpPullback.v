From HoTT Require Import Basics Types Limits.Pullback Cubical.PathSquare.
Require Import Algebra.Groups.Group.
Require Import WildCat.Core.

(** Pullbacks of groups are formalized by equipping the set-pullback with the desired group structure. The universal property in the category of groups is proved by saying that the corecursion principle [grp_pullback_corec] is an equivalence. *) 

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Section GrpPullback.

  (* Variables are named to correspond with Limits.Pullback. *)
  Context {A B C : Group} (f : B $-> A) (g : C $-> A).

  Local Instance grp_pullback_sgop : SgOp (Pullback f g).
  Proof.
    intros [b [c p]] [d [e q]].
    refine (b * d; c * e; _).
    exact (grp_homo_op_agree _ _ p q).
  Defined.

  Local Instance grp_pullback_sgop_associative
    : Associative grp_pullback_sgop.
  Proof.
    intros [x1 [x2 p]] [y1 [y2 q]] [z1 [z2 u]].
    apply equiv_path_pullback; simpl.
    refine (associativity _ _ _; associativity _ _ _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Local Instance grp_pullback_issemigroup : IsSemiGroup (Pullback f g) := {}.
  
  Local Instance grp_pullback_mon_unit : MonUnit (Pullback f g)
    := (1; 1; grp_homo_unit f @ (grp_homo_unit g)^).

  Local Instance grp_pullback_leftidentity
    : LeftIdentity grp_pullback_sgop grp_pullback_mon_unit.
  Proof.
    intros [b [c p]]; simpl.
    apply equiv_path_pullback; simpl.
    refine (left_identity _; left_identity _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Local Instance grp_pullback_rightidentity
    : RightIdentity grp_pullback_sgop grp_pullback_mon_unit.
  Proof.
    intros [b [c p]]; simpl.
    apply equiv_path_pullback; simpl.
    refine (right_identity _; right_identity _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Local Instance ismonoid_grp_pullback : IsMonoid (Pullback f g) := {}.

  Local Instance grp_pullback_inverse : Inverse (Pullback f g).
  Proof.
    intros [b [c p]].
    refine (b^; c^; grp_homo_inv f b @ _ @ (grp_homo_inv g c)^).
    exact (ap (^) p).
  Defined.

  Local Instance grp_pullback_leftinverse : LeftInverse (.*.) (^) mon_unit.
  Proof.
    unfold LeftInverse.
    intros [b [c p]].
    unfold grp_pullback_sgop; simpl.
    apply equiv_path_pullback; simpl.
    refine (left_inverse _; left_inverse _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Local Instance grp_pullback_rightinverse : RightInverse (.*.) (^) mon_unit.
  Proof.
    intros [b [c p]].
    unfold grp_pullback_sgop; simpl.
    apply equiv_path_pullback; simpl.
    refine (right_inverse _; right_inverse _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  #[export] Instance isgroup_grp_pullback : IsGroup (Pullback f g) := {}.

  Definition grp_pullback : Group
    := Build_Group (Pullback f g) _ _ _ _.

  Definition grp_pullback_pr1 : grp_pullback $-> B.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact pullback_pr1.
    - intros x y. reflexivity.
  Defined.

  Definition grp_pullback_pr2 : grp_pullback $-> C.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact pullback_pr2.
    - intros x y. reflexivity.
  Defined.

  Proposition grp_pullback_corec {X : Group}
              (b : X $-> B) (c : X $-> C)
              (p : f o b == g o c)
    : X $-> grp_pullback.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (fun x => (b x; c x; p x)).
    - intros x y.
      srapply path_sigma.
      + simpl.
        apply (grp_homo_op b).
      + unfold pr2.
        refine (transport_sigma' _ _ @ _). unfold pr1.
        apply path_sigma_hprop.
        simpl.
        apply (grp_homo_op c).
  Defined.

  Corollary grp_pullback_corec' (X : Group)
    : {b : X $-> B & { c : X $-> C & f o b == g o c}}
      -> (X $-> grp_pullback).
  Proof.
    intros [b [c p]]; exact (grp_pullback_corec b c p).
  Defined.

End GrpPullback.

Definition functor_grp_pullback {A A' B B' C C' : Group}
           (f : B $-> A) (f' : B' $-> A')
           (g : C $-> A) (g' : C' $-> A')
           (alpha : A $-> A') (beta : B $-> B') (gamma : C $-> C')
           (h : f' o beta == alpha o f)
           (k : alpha o g == g' o gamma)
  : grp_pullback f g $-> grp_pullback f' g'.
Proof.
  srapply grp_pullback_corec.
  - exact (beta $o grp_pullback_pr1 f g).
  - exact (gamma $o grp_pullback_pr2 f g).
  - intro x; cbn.
    refine (h _ @ ap alpha _ @ k _).
    apply pullback_commsq.
Defined.

Definition equiv_functor_grp_pullback {A A' B B' C C' : Group}
           (f : B $-> A) (f' : B' $-> A')
           (g : C $-> A) (g' : C' $-> A')
           (alpha : GroupIsomorphism A A')
           (beta : GroupIsomorphism B B')
           (gamma : GroupIsomorphism C C')
           (h : f' o beta == alpha o f)
           (k : alpha o g == g' o gamma)
  : GroupIsomorphism (grp_pullback f g) (grp_pullback f' g').
Proof.
  srapply Build_GroupIsomorphism.
  1: exact (functor_grp_pullback f f' g g' _ _ _ h k).
  srapply isequiv_adjointify.
  { srapply (functor_grp_pullback f' f g' g).
    1-3: rapply grp_iso_inverse; assumption.
    + rapply (equiv_ind beta); intro b.
      refine (ap f (eissect _ _) @ _).
      apply (equiv_ap' alpha _ _)^-1.
      exact ((h b)^ @ (eisretr _ _)^).
    + rapply (equiv_ind gamma); intro c.
      refine (_ @ ap g (eissect _ _)^).
      apply (equiv_ap' alpha _ _)^-1.
      exact (eisretr _ _ @ (k c)^). }
  all: intro x;
    apply equiv_path_pullback_hset; split; cbn.
  1-2: apply eisretr.
  1-2: apply eissect.
Defined.

(** Pulling back along some [g : Y $-> Z] and then [g' : Y' $-> Y] is the same as pulling back along [g $o g']. *)
Definition equiv_grp_pullback_compose_r {X Z Y Y' : Group} (f : X $-> Z) (g' : Y' $-> Y) (g : Y $-> Z)
  : GroupIsomorphism (grp_pullback (grp_pullback_pr2 f g) g') (grp_pullback f (g $o g')).
Proof.
  srapply Build_GroupIsomorphism.
  - srapply grp_pullback_corec.
    + exact (grp_pullback_pr1 _ _ $o grp_pullback_pr1 _ _).
    + apply grp_pullback_pr2.
    + intro x; cbn.
      exact (pullback_commsq _ _ _ @ ap g (pullback_commsq _ _ _)).
  - srapply isequiv_adjointify.
    + srapply grp_pullback_corec.
      * srapply functor_grp_pullback.
        1,2: exact grp_homo_id.
        1: exact g'.
        all: reflexivity.
      * apply grp_pullback_pr2.
      * reflexivity.
    + intro x; cbn.
      by srapply equiv_path_pullback_hset.
    + intros [[x [y z0]] [y' z1]]; srapply equiv_path_pullback_hset; split; cbn.
      2: reflexivity.
      srapply equiv_path_pullback_hset; split; cbn.
      1: reflexivity.
      symmetry; exact z1.
Defined.

Section IsEquivGrpPullbackCorec.

  (* New section with Funext at the start of the Context. *)
  Context `{Funext} {A B C : Group} (f : B $-> A) (g : C $-> A).

  Lemma grp_pullback_corec_pr1 {X : Group}
        (b : X $-> B) (c : X $-> C)
        (p : f o b == g o c)
    : grp_pullback_pr1 f g $o grp_pullback_corec f g b c p = b.
  Proof.
    apply equiv_path_grouphomomorphism; reflexivity.
  Defined.

  Lemma grp_pullback_corec_pr2 {X : Group}
        (b : X $-> B) (c : X $-> C)
        (p : f o b == g o c)
    : grp_pullback_pr2 f g $o grp_pullback_corec f g b c p = c.
  Proof.
    apply equiv_path_grouphomomorphism; reflexivity.
  Defined.

  Theorem isequiv_grp_pullback_corec (X : Group)
    : IsEquiv (grp_pullback_corec' f g X).
  Proof.
    snapply isequiv_adjointify.
    - intro phi.
      refine (grp_pullback_pr1 f g $o phi; grp_pullback_pr2 f g $o phi; _).
      intro x; exact (pullback_commsq f g (phi x)).
    - intro phi.
      apply equiv_path_grouphomomorphism; reflexivity.
    - intro bcp; simpl.
      srapply path_sigma.
      + simpl. apply grp_pullback_corec_pr1.
      + refine (transport_sigma' _ _ @ _).
        apply path_sigma_hprop; simpl pr1.
        simpl. apply grp_pullback_corec_pr2.
  Defined.

End IsEquivGrpPullbackCorec.
