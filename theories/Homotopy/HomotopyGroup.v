Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Truncations.
Require Import Spaces.Nat.

Import TrM.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** The type that the nth homotopy group will have. *)
Definition HomotopyGroup_type (n : nat) : Type
  := match n with
      | 0 => pType
      | n.+1 => Group
     end.

(** Definition of the nth homotopy group *)
Definition HomotopyGroup (n : nat) (X : pType) : HomotopyGroup_type n.
Proof.
  destruct n.
  1: exact X.
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

(** When n >= 2 we have that the nth homotopy group is an abelian group. Note that we don't actually define it as an abelian group but merely show that it is one. This would cause lots of complications with the typechecker. *)
Global Instance isabgroup_homotopygroup (n : nat) (X : pType)
  : IsAbGroup (HomotopyGroup n.+2 X).
Proof.
  ntc_rapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  strip_truncations.
  cbn; apply (ap tr).
  apply eckmann_hilton.
Defined.

(** The nth homotopy group is infact a functor. We now give the type this functor ought to have. For n = 0, this will simply be a pointed map, for n >= 1 this should be a group homomorphism. *)
Definition homotopygroup_functor_type (n : nat) (X Y : pType) : Type.
Proof.
  destruct n.
  1: exact (pTr 0 X ->* pTr 0 Y).
  serapply (GroupHomomorphism _ _).
  + exact (HomotopyGroup n.+1 X).
  + exact (HomotopyGroup n.+1 Y).
Defined.

Definition homotopygroup_functor (n : nat) {X Y : pType}
  : (X ->* Y) -> homotopygroup_functor_type n X Y.
Proof.
  destruct n.
  + exact (ptr_functor 0).
  + intro f.
    serapply Build_GroupHomomorphism.
    { apply Trunc_functor.
      apply iterated_loops_functor.
      assumption. }
    intros x y.
    strip_truncations.
    cbv zeta beta.
    unfold sg_op.
    unfold Trunc_functor.
    unfold O_functor.
    unfold O_rec.
    cbn.
    serapply ap.
    rewrite 2 concat_pp_p.
    apply whiskerL.
    rewrite 2 concat_p_pp.
    rewrite (concat_pp_p (ap (iterated_loops_functor n f) x)).
    rewrite concat_pV, concat_p1.
    rewrite concat_p_pp.
    apply whiskerR.
    apply ap_pp.
Defined.

Definition homotopygroup_functor_idmap n {X : pType}
  : homotopygroup_functor n.+1 (@pmap_idmap X) == idmap.
Proof.
  intro x.
  strip_truncations.
  change (@tr 0 _ (iterated_loops_functor n.+1 pmap_idmap x) = tr x).
  apply ap, iterated_loops_functor_idmap.
Defined.

Definition homotopygroup_functor_compose n {X Y Z : pType}
  (f : X ->* Y) (g : Y ->* Z)
  : homotopygroup_functor n.+1 (g o* f)
    == homotopygroup_functor n.+1 g o homotopygroup_functor n.+1 f.
Proof.
  intro x.
  strip_truncations.
  change (@tr 0 _ (iterated_loops_functor n.+1 (g o* f) x) =
   tr (((iterated_loops_functor n.+1 g) o* (iterated_loops_functor n.+1 f)) x)).
  apply ap, iterated_loops_functor_compose.
Defined.

Definition homotopygroup_2functor n {X Y : pType} (f g : X ->* Y)
  : f ==* g -> homotopygroup_functor n.+1 f == homotopygroup_functor n.+1 g.
Proof.
  intro p.
  by apply O_functor_homotopy, iterated_loops_2functor.
Defined.

Definition groupiso_homotopygroup_functor (n : nat) {X Y : pType} (e : X <~>* Y)
  : GroupIsomorphism (HomotopyGroup n.+1 X) (HomotopyGroup n.+1 Y).
Proof.
  serapply Build_GroupIsomorphism.
  1: apply (homotopygroup_functor n.+1 e).
  serapply isequiv_adjointify.
  { apply (homotopygroup_functor n.+1).
    apply e^-1*. }
  { intro.
    refine (_^ @ _ @ _).
    1: apply homotopygroup_functor_compose.
    2: apply homotopygroup_functor_idmap.
    apply homotopygroup_2functor.
    apply peisretr. }
  { intro.
    refine (_^ @ _ @ _).
    1: apply homotopygroup_functor_compose.
    2: apply homotopygroup_functor_idmap.
    apply homotopygroup_2functor.
    apply peissect. }
Defined.

(* TODO: move these to a Utf8 file and make them more global. *)
Local Infix "≅" := GroupIsomorphism (at level 20).
Local Notation "'π'" := HomotopyGroup (at level 0).
Local Infix "×" := group_prod (at level 5).

(** Homotopy groups preserve products *)
Lemma homotopygroup_prod (X Y : pType) {n : nat}
  : π n.+1 (X * Y) ≅ ((π n.+1 X) × (π n.+1 Y)).
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
