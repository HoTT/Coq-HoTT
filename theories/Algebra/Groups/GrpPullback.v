Require Import Basics Types Limits.Pullback Cubical.PathSquare.
Require Import Algebra.Groups.Group.
Require Import WildCat.

(** Pullbacks of groups are formalized by equipping the set-pullback with the desired group structure. The universal property in the category of groups is proved by saying that the corecursion principle (grp_pullback_corec) is an equivalence. *) 

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Section GrpPullback.

  (* Variables are named to correspond with Limits.Pullback. *)
  Context {A B C : Group} (f : B $-> A) (g : C $-> A).

  Local Instance grp_pullback_sgop : SgOp (Pullback f g).
  Proof.
    intros [b [c p]] [d [e q]].
    refine (b * d; c * e; _).
    refine (grp_homo_op f b d @ (_ @ _) @ (grp_homo_op g c e)^).
    - exact (ap (fun y:A => f b * y) q).
    - exact (ap (fun x:A => x * g e) p).
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

  Local Instance grp_pullback_negate : Negate (Pullback f g).
  Proof.
    intros [b [c p]].
    refine (-b; -c; grp_homo_inv f b @ _ @ (grp_homo_inv g c)^).
    exact (ap (fun a => -a) p).
  Defined.

  Local Instance grp_pullback_leftinverse
    : LeftInverse grp_pullback_sgop grp_pullback_negate grp_pullback_mon_unit.
  Proof.
    unfold LeftInverse.
    intros [b [c p]].
    unfold grp_pullback_sgop; simpl.
    apply equiv_path_pullback; simpl.
    refine (left_inverse _; left_inverse _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Local Instance grp_pullback_rightinverse
    : RightInverse grp_pullback_sgop grp_pullback_negate grp_pullback_mon_unit.
  Proof.
    intros [b [c p]].
    unfold grp_pullback_sgop; simpl.
    apply equiv_path_pullback; simpl.
    refine (right_inverse _; right_inverse _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Global Instance isgroup_grp_pullback : IsGroup (Pullback f g) := {}.

  Definition grp_pullback : Group
    := Build_Group (Pullback f g) _ _ _ _.

  Definition grp_pullback_pr1 : grp_pullback $-> B.
  Proof.
    snrapply Build_GroupHomomorphism.
    - apply pullback_pr1.
    - intros x y. reflexivity.
  Defined.

  Definition grp_pullback_pr2 : grp_pullback $-> C.
  Proof.
    snrapply Build_GroupHomomorphism.
    - apply pullback_pr2.
    - intros x y. reflexivity.
  Defined.

  Proposition grp_pullback_corec {X : Group}
              (b : X $-> B) (c : X $-> C)
              (p : f o b == g o c)
    : X $-> grp_pullback.
  Proof.
    snrapply Build_GroupHomomorphism.
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
    snrapply isequiv_adjointify.
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
