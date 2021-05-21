Require Import Basics Types Pointed WildCat.
Require Import Algebra.Groups Algebra.AbGroups.
Require Import Truncations Modalities.ReflectiveSubuniverse.
Require Import Spaces.Nat.

Local Open Scope nat_scope.
Local Open Scope path_scope.
Local Open Scope pointed_scope.
Local Open Scope wc_iso_scope.

(** We define the type of homotopy groups of positive index seperately so we can get some coercions to behave well. *)
Definition HomotopyGroup_type_pos (n : nat) : Type :=
  match n with
  | 0 => Group
  | n.+1 => AbGroup
  end.

(** The type that the nth homotopy group will have. *)
Definition HomotopyGroup_type (n : nat) : Type :=
  match n with
  | 0 => pType
  | n.+1 => HomotopyGroup_type_pos n
  end.

(** Almost homotopy group is a group *)
Definition HomotopyGroup_type_pos_group (n : nat) : HomotopyGroup_type_pos n -> Group :=
  match n with
  | 0 => fun G => G
  (** This works since [AbGroup]s coerce to [Group]s *)
  | n.+1 => fun G => G
  end.

(** If we had defined HomotopyGroup_type in one go, we would have violated the uniform inheritence checker that coq's coercion system uses. *)
Coercion HomotopyGroup_type_pos_group : HomotopyGroup_type_pos >-> Group.

(* Every homotopy group is, in particular, a pointed type. *)
Definition HomotopyGroup_type_ptype (n : nat) : HomotopyGroup_type n -> pType.
Proof.
  destruct n.
  1: exact idmap.
  (** We need to simplify the type here for the coercion to be inserted. *)
  cbn; exact idmap.
Defined.

Coercion HomotopyGroup_type_ptype : HomotopyGroup_type >-> pType.

Create HintDb path_hints.
Ltac path_auto := eauto with path_hints.

#[export] Hint Immediate idpath : path_hints.
#[export] Hint Immediate concat_1p : path_hints.
#[export] Hint Immediate concat_p1 : path_hints.
#[export] Hint Immediate concat_Vp : path_hints.
#[export] Hint Immediate concat_pV : path_hints.
#[export] Hint Immediate concat_p_pp : path_hints.
#[export] Hint Immediate concat_pp_p : path_hints.

(** We first define [Pi 1 X], and use this to define [Pi n X]. The reason is to make it easier for Coq to see that [Pi (n.+1) X] is definitionally equal to [Pi 1 (iterated_loops n X)] *)
Definition Pi1 (X : pType) : Group.
Proof.
  snrapply (Build_Group (Tr 0 (loops X))); repeat split.
  (** Operation *)
  { intros x y.
    strip_truncations.
    exact (tr (x @ y)). }
  (** Unit *)
  1: exact (tr 1).
  (** Inverse *)
  { srapply Trunc_rec; intro x.
    exact (tr x^). }
  (** IsHSet *)
  1: exact _.
  (** Axioms *)
  all: hnf; intros; strip_truncations;
    nrapply (ap tr); path_auto.
Defined.

(** Definition of the nth homotopy group *)
Definition Pi (n : nat) (X : pType) : HomotopyGroup_type n.
Proof.
  destruct n.
  1: exact (pTr 0 X).
  destruct n.
  1: exact (Pi1 X).
  snrapply Build_AbGroup'.
  1: exact (Pi1 (iterated_loops n.+1 X)).
  hnf; intros x y; strip_truncations; apply (ap tr).
  apply eckmann_hilton.
Defined.

(** To get coq to accept the types, we need to massage the type manually *)
Definition pi_succ n X
  : ((Pi n.+1 X : _ n) : Group) $<~> Pi 1 (iterated_loops n X).
Proof.
  destruct n; reflexivity.
Defined.

Module PiUtf8.
  Notation "'π'" := Pi.
End PiUtf8.

(** The nth homotopy group is in fact a functor. We now give the type this functor ought to have. For n = 0, this will simply be a pointed map, for n >= 1 this should be a group homomorphism.  *)
Definition pi_functor_type (n : nat) (X Y : pType) : Type
  := match n with
     | 0 => pTr 0 X ->* pTr 0 Y
     | n.+1 => GroupHomomorphism (Pi n.+1 X : _ n) (Pi n.+1 Y : _ n)
     end.

(* Every such map is, in particular, a pointed map. *)
Definition pi_functor_type_pmap {n X Y}
  : pi_functor_type n X Y -> Pi n X ->* Pi n Y
  := match n return pi_functor_type n X Y -> (Pi n X ->* Pi n Y) with
     | 0 => fun f => f
     (* This works because [pmap_GroupHomomorphism] is already a coercion. *)
     | n.+1 => fun f => f
     end.
Coercion pi_functor_type_pmap : pi_functor_type >-> pForall.

(** For the same reason as for [Pi1] we first define [pi1_functor]. *)
Definition pi1_functor {X Y : pType}
  : (X ->* Y) -> Pi1 X $-> Pi1 Y.
Proof.
  intro f.
  snrapply Build_GroupHomomorphism.
  { apply Trunc_functor.
    apply loops_functor.
    assumption. }
  (** Note: we don't have to be careful about which paths we choose here since we are trying to inhabit a proposition. *)
  intros x y.
  strip_truncations.
  apply (ap tr); cbn.
  rewrite 2 concat_pp_p.
  apply whiskerL.
  rewrite 2 concat_p_pp.
  rewrite (concat_pp_p (ap f x)).
  rewrite concat_pV, concat_p1.
  rewrite concat_p_pp.
  apply whiskerR.
  apply ap_pp.
Defined.

Definition pi_functor (n : nat) {X Y : pType}
  : (X ->* Y) -> pi_functor_type n X Y.
Proof.
  destruct n.
  1: exact (ptr_functor 0).
  destruct n.
  1: exact pi1_functor.
  intros f.
  exact (pi1_functor (iterated_loops_functor n.+1 f)).
Defined.

Definition pi_functor_succ {X Y : pType} (f : X $-> Y) (n : nat)
  : pi_functor n.+2 f $== pi1_functor (iterated_loops_functor n.+1 f).
Proof.
  hnf; reflexivity.
Defined.

Definition pi_functor_idmap n {X : pType}
  : pi_functor n (@pmap_idmap X) == pmap_idmap.
Proof.
  destruct n; intros x; [| destruct n].
  - apply Trunc_functor_idmap.
  - nrefine (_ @ _).
    + apply O_functor_homotopy.
      exact (iterated_loops_functor_idmap _ 1).
    + apply O_functor_idmap.
  - nrefine (_ @ _).
    + apply O_functor_homotopy.
      exact (iterated_loops_functor_idmap _ n.+2).
    + apply O_functor_idmap.
Defined.

Definition pi_functor_compose n {X Y Z : pType} (f : X ->* Y) (g : Y ->* Z)
  : pi_functor n (g o* f) == pi_functor n g o pi_functor n f.
Proof.
  destruct n; intros x; [|destruct n].
  - cbn; apply Trunc_functor_compose.
  - etransitivity.
    + apply O_functor_homotopy.
      rapply (iterated_loops_functor_compose 1).
    + refine (O_functor_compose (Tr 0) _ _ x).
  - etransitivity.
    + apply O_functor_homotopy.
      rapply (iterated_loops_functor_compose (n.+2)).
    + refine (O_functor_compose (Tr 0) _ _ x).
Defined.

Definition pi_2functor (n : nat) {X Y : pType} (f g : X ->* Y) (p : f ==* g)
  : pi_functor n f == pi_functor n g.
Proof.
  destruct n; intros x; [|destruct n].
  - apply O_functor_homotopy; exact p.
  - apply O_functor_homotopy.
    refine (iterated_loops_2functor 1 _); exact p.
  - apply O_functor_homotopy.
    refine (iterated_loops_2functor (n.+2) _); exact p.
Defined.

(** The homotopy groups of a loop space are those of the space shifted.  *)
Definition pi_loops n X : Pi n.+1 X <~> Pi n (loops X).
Proof.
  destruct n; [|destruct n].
  1,2: reflexivity.
  apply equiv_O_functor.
  apply pointed_equiv_equiv.
  apply unfold_iterated_loops'.
Defined.

Definition pi_functor_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : (pi_loops n Y) o (pi_functor n.+1 f)
    == (pi_functor n (loops_functor f)) o (pi_loops n X).
Proof.
  destruct n; intros x; [|destruct n].
  1,2: reflexivity.
  refine ((O_functor_compose 0 _ _ _)^ @ _ @ (O_functor_compose 0 _ _ _)).
  apply O_functor_homotopy; hnf.
  exact (pointed_htpy (unfold_iterated_loops_functor n.+2 f)).
Defined.

(** We have to seperate lemmas about functoriality since the target category changes between Group and AbGroup. *)

Definition groupiso_pi1_functor {X Y : pType} (e : X <~>* Y)
  : Pi 1 X ≅ Pi 1 Y.
Proof.
  snrapply Build_GroupIsomorphism.
  1: apply (pi1_functor e).
  nrefine (Trunc_functor_isequiv _ _).
  refine (isequiv_homotopic _
    (pequiv_iterated_loops_functor_is_iterated_loops_functor 1 e)). 
Defined.

Definition groupiso_pi_functor (n : nat) {X Y : pType} (e : X <~>* Y)
  : Pi n.+2 X ≅ Pi n.+2 Y.
Proof.
  snrapply Build_GroupIsomorphism.
  1: apply (pi_functor n.+2 e).
  nrefine (Trunc_functor_isequiv _ _).
  refine (isequiv_homotopic _
    (pequiv_iterated_loops_functor_is_iterated_loops_functor n.+2 e)).
Defined.

(**  Pi1 preserve products *)
Lemma pi1_prod (X Y : pType)
  : Pi 1 (X * Y) ≅ grp_prod (Pi 1 X) (Pi 1 Y).
Proof.
  srapply Build_GroupIsomorphism'.
  { refine (equiv_O_prod_cmp _ _ _ oE _).
    apply Trunc_functor_equiv.
    rapply loops_prod. }
  intros x y.
  strip_truncations; simpl.
  apply path_prod.
  1,2: apply (ap tr).
  1,2: exact (ap_pp _ x y).
Defined.

(** Homotopy groups preserve products *)
Lemma pi_prod (X Y : pType) {n : nat}
  : Pi n.+2 (X * Y) ≅ ab_biprod (Pi n.+2 X) (Pi n.+2 Y).
Proof.
  srapply Build_GroupIsomorphism'.
  { refine (equiv_O_prod_cmp _ _ _ oE _).
    apply Trunc_functor_equiv.
    refine (iterated_loops_prod _ _ n.+2). }
  intros x y.
  strip_truncations.
  apply path_prod.
  1,2: apply (ap tr).
  1: refine (ap fst _ @ loops_prod_pp_fst _ _).
  2: refine (ap snd _ @ loops_prod_pp_snd _ _).
  1,2: refine (ap (loops_prod _ _) _).
  1,2: rapply loops_functor_pp.
Defined.

(** WildCat instances for [Pi] *)
Global Instance is0functor_pi (n : nat) : Is0Functor (Pi n.+2).
Proof.
  constructor. intros X Y f. exact (pi_functor (n.+2) f).
Defined.

Global Instance is1functor_pi (n : nat) : Is1Functor (Pi n.+2).
Proof.
  constructor. 
  + intros X Y f g h.
    exact (pi_2functor n.+2 _ _ h).
  + intros X.
    exact (pi_functor_idmap n.+2).
  + intros X Y Z f g h.
    exact (pi_functor_compose n.+2 f g h).
Defined.

(** Can we make this reflexivity? *)
Lemma pmap_pi_functor {X Y : pType} (f : X ->* Y) (n : nat) 
  : pi_functor_type_pmap (pi_functor n.+2 f)
  ==* ptr_functor 0 (iterated_loops_functor n.+2 f).
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  apply path_ishprop.
Defined.

(** Homotopy groups of truncations *)

(** The fundamental group 1st truncation of X is isomorphic to the fundamental group of X *) 
Theorem grp_iso_pi1_Tr `{Univalence} (X : pType)
  : GroupIsomorphism (Pi1 (pTr 1 X)) (Pi1 X).
Proof.
  symmetry.
  snrapply Build_GroupIsomorphism'.
  { refine ((Trunc_functor_equiv _ _ )^-1%equiv oE _).
    1: symmetry; rapply ptr_loops.
    rapply equiv_tr. }
  intros x y.
  strip_truncations.
  apply path_Tr, tr.
  exact (ap_pp tr x y).
Defined.
