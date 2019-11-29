Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Truncations.
Require Import Spaces.Nat.
Require Import Modalities.ReflectiveSubuniverse.

Import TrM.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** The type that the nth homotopy group will have. *)
Definition HomotopyGroup_type (n : nat) : Type
  := match n with
      | 0 => pType
      | n.+1 => Group
     end.

(* Every homotopy group is, in particular, a pointed type. *)
Definition HomotopyGroup_type_ptype (n : nat) : HomotopyGroup_type n -> pType
  := match n return HomotopyGroup_type n -> pType with
     | 0    => fun X => X
     | n.+1 => fun G => G       (* This works because [ptype_group] is already a coercion. *)
     end.

Coercion HomotopyGroup_type_ptype : HomotopyGroup_type >-> pType.

(** Definition of the nth homotopy group *)
Definition Pi (n : nat) (X : pType) : HomotopyGroup_type n.
Proof.
  destruct n.
  1: exact (pTr 0 X).
  serapply (Build_Group (Tr 0 (iterated_loops n.+1 X)));
  repeat split.
  (** Operation *)
  + intros x y.
    strip_truncations.
    exact (tr (x @ y)).
  (** Unit *)
  + exact (tr 1).
  (** Inverse *)
  + serapply Trunc_rec; intro x.
    exact (tr x^).
  (** IsHSet *)
  + exact _.
  (** Associativity *)
  + intros x y z.
    strip_truncations.
    cbn; apply ap.
    apply concat_p_pp.
  (** Left identity *)
  + intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_1p.
  (** Right identity *)
  + intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_p1.
  (** Left inverse *)
  + intro x.
    strip_truncations.
    apply (ap tr).
    apply concat_Vp.
  (** Right inverse *)
  + intro x.
    strip_truncations.
    apply (ap tr).
    apply concat_pV.
Defined.

Module PiUtf8.
  Notation "'π'" := Pi (at level 0).
End PiUtf8.

(** When n >= 2 we have that the nth homotopy group is an abelian group. Note that we don't actually define it as an abelian group but merely show that it is one. This would cause lots of complications with the typechecker. *)
Global Instance isabgroup_pi (n : nat) (X : pType)
  : IsAbGroup (Pi n.+2 X).
Proof.
  ntc_rapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  strip_truncations.
  cbn; apply (ap tr).
  apply eckmann_hilton.
Defined.

(** The nth homotopy group is in fact a functor. We now give the type this functor ought to have. For n = 0, this will simply be a pointed map, for n >= 1 this should be a group homomorphism. *)
Definition pi_functor_type (n : nat) (X Y : pType) : Type
  := match n with
     | 0 => pTr 0 X ->* pTr 0 Y
     | n.+1 => GroupHomomorphism (Pi n.+1 X) (Pi n.+1 Y)
     end.

(* Every such map is, in particular, a pointed map. *)
Definition pi_functor_type_pmap n X Y : pi_functor_type n X Y -> (Pi n X ->* Pi n Y)
  := match n return pi_functor_type n X Y -> (Pi n X ->* Pi n Y) with
     | 0    => fun f => f
     | n.+1 => fun f => f       (* This works because [pmap_GroupHomomorphism] is already a coercion. *)
     end.
Coercion pi_functor_type_pmap : pi_functor_type >-> pMap.

Definition pi_functor (n : nat) {X Y : pType}
  : (X ->* Y) -> pi_functor_type n X Y.
Proof.
  destruct n.
  + exact (ptr_functor 0).
  + intro f.
    serapply Build_GroupHomomorphism.
    { apply Trunc_functor.
      apply iterated_loops_functor.
      assumption. }
    (** Note: we don't have to be careful about which paths we choose here since we are trying to inhabit a proposition. *)
    intros x y.
    strip_truncations.
    apply (ap tr); cbn.
    rewrite 2 concat_pp_p.
    apply whiskerL.
    rewrite 2 concat_p_pp.
    rewrite (concat_pp_p (ap (iterated_loops_functor n f) x)).
    rewrite concat_pV, concat_p1.
    rewrite concat_p_pp.
    apply whiskerR.
    apply ap_pp.
Defined.

Definition pi_functor_idmap n {X : pType}
  : pi_functor n (@pmap_idmap X) == pmap_idmap.
Proof.
  destruct n; intros x.
  - apply Trunc_functor_idmap.
  - etransitivity.
    + apply O_functor_homotopy, iterated_loops_functor_idmap.
    + apply O_functor_idmap.
Defined.

Definition pi_functor_compose n {X Y Z : pType}
  (f : X ->* Y) (g : Y ->* Z)
  : pi_functor n (g o* f) == pi_functor n g o pi_functor n f.
Proof.
  destruct n; intro x.
  - cbn; apply Trunc_functor_compose.
  - etransitivity.
    + apply O_functor_homotopy, iterated_loops_functor_compose.
    + refine (O_functor_compose 0%trunc _ _ x).
Defined.

Definition pi_2functor (n : nat)
  {X Y : pType} (f g : X ->* Y) (p : f ==* g)
  : pi_functor n f == pi_functor n g.
Proof.
  destruct n; intros x.
  - apply O_functor_homotopy; exact p.
  - apply O_functor_homotopy, iterated_loops_2functor; exact p.
Defined.

(* The homotopy groups of a loop space are those of the space shifted.  *)
Definition pi_loops n X : Pi n.+1 X <~> Pi n (loops X).
Proof.
  destruct n.
  all:apply equiv_O_functor.
  all:apply pointed_equiv_equiv.
  all:apply unfold_iterated_loops'.
Defined.

Definition pi_functor_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : (pi_loops n Y) o (pi_functor n.+1 f)
    == (pi_functor n (loops_functor f)) o (pi_loops n X).
Proof.
  destruct n; intros x.
  all:refine ((O_functor_compose 0 _ _ _)^ @ _ @ (O_functor_compose 0 _ _ _)).
  all:apply O_functor_homotopy.
  - reflexivity.
  - exact (pointed_htpy (unfold_iterated_loops_functor n.+1 f)).
Defined.

Definition groupiso_pi_functor (n : nat)
  {X Y : pType} (e : X <~>* Y)
  : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 Y).
Proof.
  serapply Build_GroupIsomorphism.
  1: apply (pi_functor n.+1 e).
  ntc_refine (Trunc_functor_isequiv _ _).
  refine (isequiv_homotopic _ (pequiv_iterated_loops_functor_is_iterated_loops_functor n.+1 e)).
Defined.

(** Homotopy groups preserve products *)
Lemma pi_prod (X Y : pType) {n : nat}
  : GroupIsomorphism (Pi n.+1 (X * Y))
      (group_prod (Pi n.+1 X) (Pi n.+1 Y)).
Proof.
  serapply Build_GroupIsomorphism'.
  { refine (equiv_O_prod_cmp _ _ _ oE _).
    apply Trunc_functor_equiv.
    serapply iterated_loops_prod. }
  intros x y.
  strip_truncations; simpl.
  set (Z := (iterated_loops_prod X Y)).
  apply path_prod.
  1,2: apply (ap tr).
  1: set (q := ap fst); unfold fst; unfold q; clear q.
  2: set (q := ap snd); unfold snd; unfold q; clear q.
  1,2: rewrite 8 ap_pp.
  1,2: rewrite ? concat_p_pp.
  1,2: do 2 apply whiskerR.
  1,2: rewrite ? ap_V.
  1,2: rewrite concat_pp_p.
  1,2: rewrite concat_pV.
  1,2: rewrite concat_p1.
  1,2: reflexivity.
Defined.
