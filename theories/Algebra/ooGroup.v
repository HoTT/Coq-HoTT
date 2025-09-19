From HoTT Require Import Basics Types.
Require Import Pointed.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Homotopy.ClassifyingSpace.
Require Import Algebra.Groups.
Require Import WildCat.

Local Open Scope trunc_scope.
Local Open Scope path_scope.
Local Open Scope pointed_scope.

(** Keyed unification makes [rewrite !loops_functor_group] take a really long time.  See https://coq.inria.fr/bugs/show_bug.cgi?id=4544 for more discussion. *)
Local Unset Keyed Unification.

(** * oo-Groups *)

(** We want a workable definition of "oo-group" (what a classical homotopy theorist would call a "grouplike Aoo-space"). The classical definitions using operads or Segal spaces involve infinitely much data, which we don't know how to handle in HoTT. But instead, we can invoke the theorem (which is a theorem in classical homotopy theory, and also in any oo-topos) that every oo-group is the loop space of some pointed connected object, and use it instead as a definition: we define an oo-group to be a pointed connected type (its classifying space or delooping). Then we make subsidiary definitions to allow us to treat such an object in the way we would expect, e.g. an oo-group homomorphism is a pointed map between classifying spaces. *)

(** ** Definition *)

Record ooGroup :=
  { classifying_space : pType ;
    isconn_classifying_space :: IsConnected 0 classifying_space
  }.

Local Notation B := classifying_space.

Definition group_type (G : ooGroup) : Type
  := point (B G) = point (B G).

(** The following is fundamental: we declare a coercion from oo-groups to types which takes a pointed connected type not to its underlying type, but to its loop space. Thus, if [G : ooGroup], then [g : G] means that [g] is an element of the oo-group that [G] is intended to denote, which is the loop space of the pointed connected type that is technically the data of which [G : ooGroup] consists. This makes it easier to really think of [G] as "really being" an oo-group rather than its classifying space.

This is also convenient because elements of oo-groups are, definitionally, loops in some type. Thus, the oo-group operations like multiplication, inverse, associativity, higher associativity, etc. are simply special cases of the corresponding operations for paths. *)

Coercion group_type : ooGroup >-> Sortclass.

(** Every pointed type has a loop space that is an oo-group. *)
Definition group_loops (X : pType)
  : ooGroup.
Proof.
  pose (BG := [{ x:X & merely (x = pt) },
               exist (fun x:X => merely (x = pt)) pt (tr 1)]).
  (** Using [cut] prevents Coq from looking for these facts with typeclass search, which is slow and (for some reason) introduces scads of extra universes. *)
  cut (IsConnected 0 BG).
  { exact (Build_ooGroup BG). }
  cut (IsSurjection (unit_name (point BG))).
  { intros; exact (conn_pointed_type pt). }
  apply BuildIsSurjection; simpl; intros [x p].
  strip_truncations; apply tr; exists tt.
  apply path_sigma_hprop; simpl.
  exact (p^).
Defined.

(** Unfortunately, the underlying type of that oo-group is not *definitionally* the same as the ordinary loop space, but it is equivalent to it. *)
Definition loops_group (X : pType)
  : loops X <~> group_loops X.
Proof.
  unfold loops, group_type. simpl.
  exact (equiv_path_sigma_hprop (point X ; tr 1) (point X ; tr 1)).
Defined.

(** ** Homomorphisms *)

(** *** Definition *)

Definition ooGroupHom (G H : ooGroup)
  := B G ->* B H.

Definition grouphom_fun {G H} (phi : ooGroupHom G H) : G -> H
  := fmap loops phi.

Coercion grouphom_fun : ooGroupHom >-> Funclass.

(** The loop group functor takes values in oo-group homomorphisms. *)
Definition group_loops_functor
           {X Y : pType} (f : X ->* Y)
: ooGroupHom (group_loops X) (group_loops Y).
Proof.
  snapply Build_pMap; simpl.
  - intros [x p].
    exists (f x).
    strip_truncations; apply tr.
    exact (ap f p @ point_eq f).
  - apply path_sigma_hprop; simpl.
    apply point_eq.
Defined.

(** And this functor "is" the same as the ordinary loop space functor. *)
Definition loops_functor_group
           {X Y : pType} (f : X ->* Y)
: fmap loops (group_loops_functor f) o loops_group X
  == loops_group Y o fmap loops f.
Proof.
  intros x.
  apply (equiv_inj (equiv_path_sigma_hprop _ _)^-1).
  simpl.
  unfold pr1_path; rewrite !ap_pp.
  rewrite ap_V, !ap_pr1_path_sigma_hprop.
  apply whiskerL, whiskerR.
  transitivity (ap (fun X0 : {x0 : X & merely (x0 = point X)} => f X0.1)
                   (path_sigma_hprop (point X; tr 1) (point X; tr 1) x)).
  - match goal with
        |- ap ?f (ap ?g ?p) = ?z =>
        symmetry; exact (ap_compose g f p)
    end.
  - rewrite ap_compose; apply ap.
    apply ap_pr1_path_sigma_hprop.
Qed.

Definition grouphom_compose {G H K : ooGroup}
           (psi : ooGroupHom H K) (phi : ooGroupHom G H)
: ooGroupHom G K
  := pmap_compose psi phi.

(** *** Functoriality *)

Definition group_loops_functor_compose
           {X Y Z : pType}
           (psi : Y ->* Z) (phi : X ->* Y)
: grouphom_compose (group_loops_functor psi) (group_loops_functor phi)
  == group_loops_functor (pmap_compose psi phi).
Proof.
  intros g.
  unfold grouphom_fun, grouphom_compose.
  refine (pointed_htpy (fmap_comp loops _ _) g @ _).
  pose (p := eisretr (loops_group X) g).
  change (fmap loops (group_loops_functor psi)
            (fmap loops (group_loops_functor phi) g)
          = fmap loops (group_loops_functor
                                 (pmap_compose psi phi)) g).
  rewrite <- p.
  rewrite !loops_functor_group.
  apply ap.
  symmetry; tapply (fmap_comp loops).
Qed.

Definition grouphom_idmap (G : ooGroup) : ooGroupHom G G
  := pmap_idmap.

Definition group_loops_functor_idmap {X : pType}
: grouphom_idmap (group_loops X)
  == group_loops_functor (Id (A:=pType) _).
Proof.
  intros g.
  refine (fmap_id loops _ g @ _).
  rewrite <- (eisretr (loops_group X) g).
  unfold grouphom_fun, grouphom_idmap.
  rewrite !loops_functor_group.
  exact (ap (loops_group X) (fmap_id loops _ _)^).
Qed.

(** *** Homomorphic properties *)

(** The following tactic often allows us to "pretend" that phi preserves basepoints strictly.  This is basically a simple extension of [pointed_reduce_rewrite] (see Pointed.v). *)
Ltac grouphom_reduce :=
  unfold grouphom_fun; cbn;
  repeat match goal with
           | [ G : ooGroup |- _ ] => destruct G as [G ?]
           | [ phi : ooGroupHom ?G ?H |- _ ] => destruct phi as [phi ?]
         end;
  pointed_reduce_rewrite.

Definition compose_grouphom {G H K : ooGroup}
           (psi : ooGroupHom H K) (phi : ooGroupHom G H)
: grouphom_compose psi phi == psi o phi.
Proof.
  intros g; grouphom_reduce.
  exact (ap_compose phi psi g).
Qed.

Definition idmap_grouphom (G : ooGroup)
: grouphom_idmap G == idmap.
Proof.
  intros g; grouphom_reduce.
  exact (ap_idmap g).
Qed.

Definition grouphom_pp {G H} (phi : ooGroupHom G H) (g1 g2 : G)
: phi (g1 @ g2) = phi g1 @ phi g2.
Proof.
  grouphom_reduce.
  exact (ap_pp phi g1 g2).
Qed.

Definition grouphom_V {G H} (phi : ooGroupHom G H) (g : G)
: phi g^ = (phi g)^.
Proof.
  grouphom_reduce.
  exact (ap_V phi g).
Qed.

Definition grouphom_1 {G H} (phi : ooGroupHom G H)
: phi 1 = 1.
Proof.
  grouphom_reduce.
  reflexivity.
Qed.

Definition grouphom_pp_p {G H} (phi : ooGroupHom G H) (g1 g2 g3 : G)
: grouphom_pp phi (g1 @ g2) g3
  @ whiskerR (grouphom_pp phi g1 g2) (phi g3)
  @ concat_pp_p (phi g1) (phi g2) (phi g3)
  = ap phi (concat_pp_p g1 g2 g3)
    @ grouphom_pp phi g1 (g2 @ g3)
    @ whiskerL (phi g1) (grouphom_pp phi g2 g3).
Proof.
  grouphom_reduce.
Abort.

(** ** Subgroups *)

Section Subgroups.
  Context {G H : ooGroup} (incl : ooGroupHom H G) `{IsEmbedding incl}.

  (** A subgroup induces an equivalence relation on the ambient group, whose equivalence classes are called "cosets". *)
  Definition in_coset : G -> G -> Type
    := fun g1 g2 => hfiber incl (g1 @ g2^).

  #[export] Instance ishprop_in_coset : is_mere_relation G in_coset.
  Proof.
    exact _.
  Defined.

  #[export] Instance reflexive_coset : Reflexive in_coset.
  Proof.
    intros g.
    exact (1 ; grouphom_1 incl @ (concat_pV g)^).
  Defined.

  #[export] Instance symmetric_coset : Symmetric in_coset.
  Proof.
    intros g1 g2 [h p].
    exists (h^).
    exact (grouphom_V incl h @ inverse2 p @ inv_pp _ _ @ whiskerR (inv_V _) _).
  Defined.

  #[export] Instance transitive_coset : Transitive in_coset.
  Proof.
    intros g1 g2 g3 [h1 p1] [h2 p2].
    exists (h1 @ h2).
    exact (grouphom_pp incl h1 h2
            @ (p1 @@ p2)
            @ concat_p_pp _ _ _
            @ whiskerR (concat_pV_p _ _) _).
  Defined.

  (** Every coset is equivalent (as a type) to the subgroup itself. *)
  Definition equiv_coset_subgroup (g : G)
  : { g' : G & in_coset g g'} <~> H.
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    - intros [? [h ?]]; exact h.
    - intros h; exists (incl h^ @ g); exists h; simpl.
      abstract (rewrite inv_pp, grouphom_V, inv_V, concat_p_Vp; reflexivity).
    - intros h; reflexivity.
    - intros [g' [h p]].
      apply path_sigma_hprop; simpl.
      refine ((grouphom_V incl h @@ 1) @ _).
      apply moveR_Vp, moveL_pM. exact (p^).
  Defined.

  Definition cosets := Quotient in_coset.

End Subgroups.

(** The wild category of oo-groups is induced by the wild category of pTypes *)

Instance isgraph_oogroup : IsGraph ooGroup
  := Build_IsGraph _ ooGroupHom.
Instance is01cat_oogroup : Is01Cat ooGroup
  := Build_Is01Cat _ _ grouphom_idmap (@grouphom_compose).
Instance is2graph_oogroup : Is2Graph ooGroup
  := is2graph_induced classifying_space.
Instance is1cat_oogroup : Is1Cat ooGroup
  := is1cat_induced classifying_space.

(** ** 1-groups as oo-groups *)

Definition group_to_oogroup : Group -> ooGroup
  := fun G => Build_ooGroup (pClassifyingSpace G) _.

Instance is0functor_group_to_oogroup : Is0Functor group_to_oogroup.
Proof.
  snapply Build_Is0Functor.
  intros G H f.
  by tapply (fmap pClassifyingSpace).
Defined.

Instance is1functor_group_to_oogroup : Is1Functor group_to_oogroup.
Proof.
  snapply Build_Is1Functor; hnf; intros.
  1: by tapply (fmap2 pClassifyingSpace).
  1: by tapply (fmap_id pClassifyingSpace).
  by tapply (fmap_comp pClassifyingSpace).
Defined.
