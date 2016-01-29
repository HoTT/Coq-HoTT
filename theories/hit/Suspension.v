(* -*- mode: coq; mode: visual-line -*- *)

(** * The suspension of a type *)

Require Import HoTT.Basics HoTT.Types.
Require Import Pointed NullHomotopy.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

Generalizable Variables X A B f g n.

(* ** Definition of suspension. *)

Module Export Suspension.

(** We ensure that [Susp X] does not live in a lower universe than [X] *)
Private Inductive Susp (X : Type@{i}) : Type@{i} :=
  | North : Susp X
  | South : Susp X.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : forall (X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

Definition Susp_ind {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
: forall (y:Susp X), P y
:= fun y => (match y return (_ -> P y)
     with North => (fun _ => H_N) | South => (fun _ => H_S) end) H_merid.

Axiom Susp_comp_merid : forall {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  (x:X),
apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension.

(* ** Non-dependent eliminator. *)

Definition Susp_rec {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
: Susp X -> Y.
Proof.
  apply (Susp_ind (fun _ => Y) H_N H_S).
  intros x. exact (transport_const _ _ @ H_merid x).
Defined.

Global Arguments Susp_rec {X Y}%type_scope H_N H_S H_merid%function_scope _.

Definition Susp_comp_nd_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
: ap (Susp_rec H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply (cancelL (transport_const (merid x) H_N)).
  transitivity (apD (Susp_rec H_N H_S H_merid) (merid x)).
  symmetry; refine (apD_const (Susp_rec H_N H_S H_merid) _).
  refine (Susp_comp_merid (fun _ : Susp X => Y) _ _ _ _).
Defined.

(** ** Eta-rule. *)

(** The eta-rule for suspension states that any function out of a suspension is equal to one defined by [Susp_ind] in the obvious way. We give it first in a weak form, producing just a pointwise equality, and then turn this into an actual equality using [Funext]. *)
Definition Susp_eta_homot {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f == Susp_ind P (f North) (f South) (fun x => apD f (merid x)).
Proof.
  unfold pointwise_paths. refine (Susp_ind _ 1 1 _).
  intros x.
  refine (transport_paths_FlFr_D
    (g := Susp_ind P (f North) (f South) (fun x : X => apD f (merid x)))
    _ _ @ _); simpl.
  apply moveR_pM. apply (concat (concat_p1 _)), (concatR (concat_1p _)^).
  apply ap, inverse. refine (Susp_comp_merid _ _ _ _ _).
Defined.

Definition Susp_eta `{Funext}
  {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f = Susp_ind P (f North) (f South) (fun x => apD f (merid x))
:= path_forall _ _ (Susp_eta_homot f).

(** ** Universal property *)

Definition equiv_Susp_rec `{Funext} (X Y : Type)
: (Susp X -> Y) <~> { NS : Y * Y & X -> fst NS = snd NS }.
Proof.
  simple refine (BuildEquiv (Susp X -> Y)
                     { NS : Y * Y & X -> fst NS = snd NS } _ _).
  { intros f.
    exists (f North , f South).
    intros x. exact (ap f (merid x)). }
  simple refine (isequiv_adjointify _ _ _ _).
  - intros [[N S] m].
    exact (Susp_rec N S m).
  - intros [[N S] m].
    apply ap, path_arrow. intros x; apply Susp_comp_nd_merid.
  - intros f.
    symmetry.
    refine (Susp_eta f @ _).
    unfold Susp_rec; apply ap.
    apply path_forall; intros x.
    apply apD_const.
Defined.

(** ** Nullhomotopies of maps out of suspensions *)

Definition nullhomot_susp_from_paths {X Z: Type} (f : Susp X -> Z)
  (n : NullHomotopy (fun x => ap f (merid x)))
: NullHomotopy f.
Proof.
  exists (f North).
  refine (Susp_ind _ 1 n.1^ _); intros x.
  refine (transport_paths_Fl _ _ @ _).
  apply (concat (concat_p1 _)), ap. apply n.2.
Defined.

Definition nullhomot_paths_from_susp {X Z: Type} (H_N H_S : Z) (f : X -> H_N = H_S)
  (n : NullHomotopy (Susp_rec H_N H_S f))
: NullHomotopy f.
Proof.
  exists (n.2 North @ (n.2 South)^).
  intro x. apply moveL_pV.
  transitivity (ap (Susp_rec H_N H_S f) (merid x) @ n.2 South).
  apply whiskerR, inverse, Susp_comp_nd_merid.
  refine (concat_Ap n.2 (merid x) @ _).
  apply (concatR (concat_p1 _)), whiskerL. apply ap_const.
Defined.

(** ** Pointedness of [Susp] and path spaces thereof *)
(** We arbitrarily choose [North] to be the point. *)
Global Instance ispointed_susp {X : Type} : IsPointed (Susp X) | 0
  := North.

Global Instance ispointed_path_susp `{IsPointed X} : IsPointed (North = South :> Susp X) | 0
  := merid (point X).

Global Instance ispointed_path_susp' `{IsPointed X} : IsPointed (South = North :> Susp X) | 0
  := (merid (point X))^.

Definition psusp (X : pType) : pType
  := Build_pType (Susp X) _.

(** ** Suspension Functor *)

Definition psusp_functor {X Y : pType} (f : X ->* Y)
: psusp X ->* psusp Y.
Proof.
  refine (Build_pMap (psusp X) (psusp Y)
                     (Susp_rec North South (fun x => merid (f x))) 1).
Defined.

Definition psusp_functor_compose {X Y Z : pType}
           (g : Y ->* Z) (f : X ->* Y)
: psusp_functor (g o* f) ==* psusp_functor g o* psusp_functor f.
Proof.
  pointed_reduce; simple refine (Build_pHomotopy _ _); cbn.
  - refine (Susp_ind _ _ _ _); cbn; try reflexivity.
    intros x.
    rewrite transport_paths_FlFr.
    rewrite concat_p1; apply moveR_Vp; rewrite concat_p1.
    rewrite ap_compose.
    rewrite !Susp_comp_nd_merid.
    reflexivity.
  - reflexivity.
Qed.

(** ** Loop-Suspension Adjunction *)

Module Book_Loop_Susp_Adjunction.

  (** Here is the proof of the adjunction isomorphism given in the book (6.5.4); we put it in a non-exported module for reasons discussed below. *)
  Definition loop_susp_adjoint `{Funext} (A B : pType)
  : (psusp A ->* B) <~> (A ->* loops B).
  Proof.
    refine (_ oE (issig_pmap (psusp A) B)^-1).
    refine (_ oE (equiv_functor_sigma'
                 (Q := fun NSm => fst NSm.1 = point B)
                 (equiv_Susp_rec A B)
                 (fun f => 1%equiv))).
    refine (_ oE (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ oE
              (equiv_functor_sigma'
                 (Q := fun a => {_ : fst a = point B & A -> fst a = snd a })
                 (equiv_idmap (B * B))
                 (fun NS => equiv_sigma_symm0
                              (A -> fst NS = snd NS)
                              (fst NS = point B)))).
    refine (_ oE (equiv_sigma_prod _)^-1); simpl.
    refine (_ oE
              (equiv_functor_sigma'
                 (Q := fun b => {_ : b = point B & { p : B & A -> b = p}})
                 1
                 (fun b => equiv_sigma_symm (A := B) (B := b = point B)
                             (fun p _ => A -> b = p)))).
    refine (_ oE
              (equiv_sigma_assoc (fun b => b = point B)
                                 (fun bq => {p:B & A -> bq.1 = p}))).
    refine (_ oE equiv_contr_sigma _); simpl.
    refine (_ oE (equiv_sigma_contr
                   (A := {p : B & A -> point B = p})
                   (fun pm => { q : point B = pm.1 & pm.2 (point A) = q }))^-1).
    refine (_ oE (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ oE
              (equiv_functor_sigma'
                 (Q := fun b => {q : point B = b & {p : A -> point B = b & p (point A) = q}})
                 1
                 (fun b => equiv_sigma_symm (fun p q => p (point A) = q)))).
    refine (_ oE
              (equiv_sigma_assoc
                 (fun b => point B = b)
                 (fun bq => {p : A -> point B = bq.1 & p (point A) = bq.2}))).
    refine (_ oE equiv_contr_sigma _); simpl.
    refine (issig_pmap A (loops B)).
  Defined.

  (** Unfortunately, with this definition it seems to be quite hard to prove that the isomorphism is natural on pointed maps.  The following proof gets partway there, but ends with a pretty intractable goal.  It's also quite slow, so we don't want to compile it all the time. *)
  (**
<<
  Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
             (f : psusp A ->* B) (g : B ->* B')
  : loop_susp_adjoint A B' (g o* f)
    ==* loops_functor g o* loop_susp_adjoint A B f.
  Proof.
    pointed_reduce.
    refine (Build_pHomotopy _ _).
    - intros a. simpl.
      refine (_ @ (concat_1p _)^).
      refine (_ @ (concat_p1 _)^).
      rewrite !transport_sigma. simpl.
      rewrite !(transport_arrow_fromconst (B := A)).
      rewrite !transport_paths_Fr.
      rewrite !ap_V, !ap_pr1_path_basedpaths.
      rewrite ap_pp, !(ap_compose f g), ap_V.
      reflexivity.
    - cbn.
      Fail reflexivity.
      (** ...but this goal is pretty intractable. *)
  Abort.
>>
   *)

End Book_Loop_Susp_Adjunction.

(** Thus, instead we will construct the adjunction in terms of a unit and counit natural transformation. *)

Definition loop_susp_unit (X : pType) : X ->* loops (psusp X).
Proof.
  refine (Build_pMap X (loops (psusp X))
                     (fun x => merid x @ (merid (point X))^) _).
  apply concat_pV.
Defined.

Definition loop_susp_unit_natural {X Y : pType} (f : X ->* Y)
: loop_susp_unit Y o* f
  ==* loops_functor (psusp_functor f) o* loop_susp_unit X.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; symmetry.
    refine (concat_1p _@ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec North South (merid o f))
                  (merid x) (merid (point X))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine (Susp_comp_nd_merid _ @@ inverse2 (Susp_comp_nd_merid _)).
  - cbn. rewrite !inv_pp, !concat_pp_p, concat_1p; symmetry.
    apply moveL_Vp.
    refine (concat_pV_inverse2 _ _ (Susp_comp_nd_merid (point X)) @ _).
    do 2 apply moveL_Vp.
    refine (ap_pp_concat_pV _ _ @ _).
    do 2 apply moveL_Vp.
    rewrite concat_p1_1, concat_1p_1.
    cbn; symmetry.
    refine (concat_p1 _ @ _).
    refine (ap_compose (fun p' => (ap (Susp_rec North South (merid o f))) p' @ 1)
                       (fun p' => 1 @ p')
                       (concat_pV (merid (point X))) @ _).
    apply ap.
    refine (ap_compose (ap (Susp_rec North South (merid o f)))
                       (fun p' => p' @ 1) _).
Qed.

Definition loop_susp_counit (X : pType) : psusp (loops X) ->* X.
Proof.
  refine (Build_pMap (psusp (loops X)) X
                     (Susp_rec (point X) (point X) idmap) 1).
Defined.

Definition loop_susp_counit_natural {X Y : pType} (f : X ->* Y)
: f o* loop_susp_counit X
  ==* loop_susp_counit Y o* psusp_functor (loops_functor f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); simpl.
  - refine (Susp_ind _ _ _ _); cbn; try reflexivity; intros p.
    rewrite transport_paths_FlFr, ap_compose, concat_p1.
    apply moveR_Vp.
    refine (ap_compose
              (Susp_rec North South (fun x0 => merid (1 @ (ap f x0 @ 1))))
              (Susp_rec (point Y) (point Y) idmap) (merid p) @ _).
    rewrite !Susp_comp_nd_merid.
    apply concat_1p.
  - reflexivity.
Qed.

(** Now the triangle identities *)

Definition loop_susp_triangle1 (X : pType)
: loops_functor (loop_susp_counit X) o* loop_susp_unit (loops X)
  ==* pmap_idmap (loops X).
Proof.
  simple refine (Build_pHomotopy _ _).
  - intros p; cbn.
    refine (concat_1p _ @ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec (point X) (point X) idmap)
                  (merid p) (merid (point (point X = point X)))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine ((Susp_comp_nd_merid p @@ inverse2 (Susp_comp_nd_merid (point (loops X)))) @ _).
    exact (concat_p1 _).
  - destruct X as [X x]; cbn; unfold point.
    apply whiskerR.
    rewrite (concat_pV_inverse2
               (ap (Susp_rec x x idmap) (merid 1))
               1 (Susp_comp_nd_merid 1)).
    rewrite (ap_pp_concat_pV (Susp_rec x x idmap) (merid 1)).
    rewrite ap_compose, (ap_compose _ (fun p => p @ 1)).
    rewrite concat_1p_1; apply ap.
    apply concat_p1_1.
Qed.

Definition loop_susp_triangle2 (X : pType)
: loop_susp_counit (psusp X) o* psusp_functor (loop_susp_unit X)
  ==* pmap_idmap (psusp X).
Proof.
  simple refine (Build_pHomotopy _ _);
  [ simple refine (Susp_ind _ _ _ _) | ]; try reflexivity; cbn.
  - exact (merid (point X)).
  - intros x.
    rewrite transport_paths_FlFr, ap_idmap, ap_compose.
    rewrite Susp_comp_nd_merid.
    apply moveR_pM; rewrite concat_p1.
    refine (inverse2 (Susp_comp_nd_merid _) @ _).
    rewrite inv_pp, inv_V; reflexivity.
Qed.

(** Now we can finally construct the adjunction equivalence. *)

Definition loop_susp_adjoint `{Funext} (A B : pType)
: (psusp A ->* B) <~> (A ->* loops B).
Proof.
  refine (equiv_adjointify
            (fun f => loops_functor f o* loop_susp_unit A)
            (fun g => loop_susp_counit B o* psusp_functor g) _ _).
  - intros g. apply path_pmap.
    refine (pmap_prewhisker _ (loops_functor_compose _ _) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (loop_susp_unit_natural g)^* @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker g (loop_susp_triangle1 B) @* _).
    apply pmap_postcompose_idmap.
  - intros f. apply path_pmap.
    refine (pmap_postwhisker _ (psusp_functor_compose _ _) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (loop_susp_counit_natural f)^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker f (loop_susp_triangle2 A) @* _).
    apply pmap_precompose_idmap.
Defined.

(** And its naturality is easy. *)

Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
           (f : psusp A ->* B) (g : B ->* B')
: loop_susp_adjoint A B' (g o* f)
  ==* loops_functor g o* loop_susp_adjoint A B f.
Proof.
  cbn.
  refine (_ @* pmap_compose_assoc _ _ _).
  apply pmap_prewhisker.
  refine (loops_functor_compose g f).
Defined.

Definition loop_susp_adjoint_nat_l `{Funext} (A A' B : pType)
           (f : A ->* loops B) (g : A' ->* A)
: (loop_susp_adjoint A' B)^-1 (f o* g)
  ==* (loop_susp_adjoint A B)^-1 f o* psusp_functor g.
Proof.
  cbn.
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  apply pmap_postwhisker.
  refine (psusp_functor_compose f g).
Defined.
