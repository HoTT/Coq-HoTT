(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import WildCat.
Require Import Colimits.Pushout.
Require Import NullHomotopy.
Require Import Truncations.
Require Import Extensions.
Import TrM.

(** * The suspension of a type *)

Generalizable Variables X A B f g n.

Local Open Scope path_scope.

(** TODO: remove and replace with HIT description. *)
(* ** Definition of suspension. *)
(* 
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

Axiom Susp_ind_beta_merid : forall {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  (x:X),
apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension. *)

(* ** Definition of suspension *)

Definition Susp (X : Type) := Pushout (@const X _ tt) (const tt).
Definition North {X} : Susp X := pushl tt.
Definition South {X} : Susp X := pushr tt.
Definition merid {X} (x : X) : North = South := pglue x.

Definition Susp_ind {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  : forall (y : Susp X), P y.
Proof.
  serapply Pushout_ind.
  - exact (Unit_ind H_N).
  - exact (Unit_ind H_S).
  - exact (H_merid).
Defined.

Definition Susp_ind_dp {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, DPath P (merid x) H_N H_S)
  : forall (y : Susp X), P y.
Proof.
  serapply Susp_ind.
  - exact H_N.
  - exact H_S.
  - intro x.
    apply dp_path_transport^-1.
    exact (H_merid x).
Defined.

Definition Susp_ind_beta_merid {X : Type}
  (P : Susp X -> Type) (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S) (x : X)
  : apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  serapply Pushout_ind_beta_pglue.
Defined.

Definition Susp_ind_dp_beta_merid {X : Type}
  (P : Susp X -> Type) (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, DPath P (merid x) H_N H_S) (x : X)
  : dp_apD (Susp_ind_dp P H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply dp_apD_path_transport.
  serapply Susp_ind_beta_merid.
Defined.

(** We want to allow the user to forget that we've defined suspension in this way. *)
Arguments Susp : simpl never.
Arguments North : simpl never.
Arguments South : simpl never.
Arguments merid : simpl never.
Arguments Susp_ind_beta_merid : simpl never.

(* ** Non-dependent eliminator. *)

Definition Susp_rec {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
: Susp X -> Y.
Proof.
  apply (Susp_ind (fun _ => Y) H_N H_S).
  intros x. exact (transport_const _ _ @ H_merid x).
Defined.

Global Arguments Susp_rec {X Y}%type_scope H_N H_S H_merid%function_scope _.

Definition Susp_rec_beta_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
: ap (Susp_rec H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply (cancelL (transport_const (merid x) H_N)).
  transitivity (apD (Susp_rec H_N H_S H_merid) (merid x)).
  - symmetry; refine (apD_const (Susp_rec H_N H_S H_merid) _).
  - refine (Susp_ind_beta_merid (fun _ : Susp X => Y) _ _ _ _).
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
  apply ap, inverse. refine (Susp_ind_beta_merid _ _ _ _ _).
Defined.

Definition Susp_eta_homot_dp {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f == Susp_ind_dp P (f North) (f South) (fun x => dp_apD f (merid x)).
Proof.
  unfold pointwise_paths. refine (Susp_ind_dp _ 1 1 _).
  intros x.
  apply dp_paths_FlFr_D.
  cbn.
  refine (concat_pp_p _ _ _ @ _).
  apply moveR_Vp.
  refine (concat_1p _ @ _ @ (concat_p1 _)^).
  apply (equiv_inj dp_path_transport).
  refine (dp_path_transport_apD _ _ @ _). 
  refine (_ @ (dp_path_transport_apD f (merid x))^).
  serapply Susp_ind_dp_beta_merid.
Defined.

Definition Susp_rec_eta_homot {X Y : Type} (f : Susp X -> Y)
: f == Susp_rec (f North) (f South) (fun x => ap f (merid x)).
Proof.
  refine (Susp_ind _ 1 1 _).
  intro x.
  refine ((transport_paths_FlFr _ _) @ _). apply moveR_Mp.
  refine ((Susp_rec_beta_merid _) @ _). hott_simpl.
  refine (_ @ (ap_V f _)). f_ap.
  refine (inv_V _)^.
Defined.  

Definition Susp_eta `{Funext}
  {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f = Susp_ind P (f North) (f South) (fun x => apD f (merid x))
:= path_forall _ _ (Susp_eta_homot f).

Definition Susp_rec_eta `{Funext} {X Y : Type} (f : Susp X -> Y)
  : f = Susp_rec (f North) (f South) (fun x => ap f (merid x))
:= path_forall _ _ (Susp_rec_eta_homot f).

(** ** Functoriality *)

Definition functor_susp {X Y : Type} (f : X -> Y)
  : Susp X -> Susp Y.
Proof.
  serapply Susp_rec.
  - exact North.
  - exact South.
  - intros x; exact (merid (f x)).
Defined.

Definition ap_functor_susp_merid {X Y : Type} (f : X -> Y) (x : X)
  : ap (functor_susp f) (merid x) = merid (f x).
Proof.
  serapply Susp_rec_beta_merid.
Defined.

(** ** Universal property *)

Definition equiv_Susp_rec `{Funext} (X Y : Type)
: (Susp X -> Y) <~> { NS : Y * Y & X -> fst NS = snd NS }.
Proof.
  unshelve econstructor.
  { intros f.
    exists (f North , f South).
    intros x. exact (ap f (merid x)). }
  simple refine (isequiv_adjointify _ _ _ _).
  - intros [[N S] m].
    exact (Susp_rec N S m).
  - intros [[N S] m].
    apply ap, path_arrow. intros x; apply Susp_rec_beta_merid.
  - intros f.
    symmetry.
    refine (Susp_eta f @ _).
    unfold Susp_rec; apply ap.
    apply path_forall; intros x.
    apply apD_const.
Defined.

(** Using wild 0-groupoids, the universal property can be proven without funext.  A simple equivalence of 0-groupoids between [Susp X -> Y] and [{ NS : Y * Y & X -> fst NS = snd NS }] would not carry all the higher-dimensional information, but if we generalize it to dependent functions, then it does suffice. *)
Section UnivProp.
  Context (X : Type) (P : Susp X -> Type).

  (** Here is the domain of the equivalence: sections of [P] over [Susp X]. *)
  Definition Susp_ind_type := forall z:Susp X, P z.

  Local Instance is01cat_Susp_ind_type : Is01Cat Susp_ind_type.
  Proof. apply is01cat_forall; intros; apply is01cat_paths. Defined.

  Local Instance is0gpd_Susp_ind_type : Is0Gpd Susp_ind_type.
  Proof. apply is0gpd_forall; intros; apply is0gpd_paths. Defined.

  (** The codomain is a sigma-groupoid of this family, consisting of input data for [Susp_ind]. *)
  Definition Susp_ind_data' (NS : P North * P South)
    := forall x:X, DPath P (merid x) (fst NS) (snd NS).

  Local Instance is01cat_Susp_ind_data' NS : Is01Cat (Susp_ind_data' NS).
  Proof. apply is01cat_forall; intros; apply is01cat_paths. Defined.

  Local Instance is0gpd_Susp_ind_data' NS : Is0Gpd (Susp_ind_data' NS).
  Proof. apply is0gpd_forall; intros; apply is0gpd_paths. Defined.

  (** Here is the codomain itself. *)
  Definition Susp_ind_data := sig Susp_ind_data'.

  Local Instance is01cat_Susp_ind_data : Is01Cat Susp_ind_data.
  Proof. rapply is01cat_sigma. Defined.

  Local Instance is0gpd_Susp_ind_data : Is0Gpd Susp_ind_data.
  Proof. rapply is0gpd_sigma. Defined.

  (** Here is the functor. *)
  Definition Susp_ind_inv : Susp_ind_type -> Susp_ind_data.
  Proof.
    intros f.
    exists (f North,f South).
    intros x.
    exact (dp_apD f (merid x)).
  Defined.

  Local Instance is0functor_susp_ind_inv : Is0Functor Susp_ind_inv.
  Proof.
    constructor; unfold Susp_ind_type; cbn.
    intros f g p.
    unshelve econstructor.
    - apply path_prod; apply p.
    - intros x.
      rewrite transport_path_prod, !transport_forall_constant; cbn.
      apply equiv_ds_transport_dpath.
      exact (dp_apD_nat p (merid x)).
  Defined.

  (** And now we can prove that it's an equivalence. *)
  Definition equiv0gpd_Susp_ind_inv : IsEquiv0Gpd Susp_ind_inv.
  Proof.
    constructor.
    - intros [[n s] g].
      exists (Susp_ind_dp P n s g); cbn.
      exists idpath.
      intros x; cbn.
      apply Susp_ind_dp_beta_merid.
    - intros f g [p q]; cbn in *.
      serapply Susp_ind_dp; cbn.
      1:exact (ap fst p).
      1:exact (ap snd p).
      intros x; specialize (q x).
      apply equiv_sq_dp_D.
      apply equiv_ds_transport_dpath.
      rewrite transport_forall_constant in q.
      rewrite <- (eta_path_prod p) in q.
      rewrite transport_path_prod in q.
      exact q.
  Defined.

End UnivProp.

(** The full non-funext version of the universal property should be formulated with respect to a notion of "wild hom-oo-groupoid", which we don't currently have.  However, we can deduce statements about full higher universal properties that we do have, for instance the statement that a type is local for [functor_susp f] -- expressed in terms of [ooExtendableAlong] -- if and only if all its identity types are local for [f].  (We will use this in [Modalities.Localization] for separated subuniverses.)  To prove this, we again generalize it to the case of dependent types, starting with naturality of the above 0-dimensional universal property. *)

Section UnivPropNat.
  (** We will show that [Susp_ind_inv] for [X] and [Y] commute with precomposition with [f] and [functor_susp f]. *)
  Context {X Y : Type} (f : X -> Y) (P : Susp Y -> Type).

  (** We recall all those instances from the previous section. *)
  Local Existing Instances is01cat_Susp_ind_type is0gpd_Susp_ind_type is01cat_Susp_ind_data' is0gpd_Susp_ind_data' is01cat_Susp_ind_data is0gpd_Susp_ind_data.

  (** Here is an intermediate family of groupoids that we have to use, since precomposition with [f] doesn't land in quite the right place. *)
  Definition Susp_ind_data'' (NS : P North * P South)
    := forall x:X, DPath P (merid (f x)) (fst NS) (snd NS).

  Local Instance is01cat_Susp_ind_data'' NS : Is01Cat (Susp_ind_data'' NS).
  Proof. apply is01cat_forall; intros; apply is01cat_paths. Defined.

  Local Instance is0gpd_Susp_ind_data'' NS : Is0Gpd (Susp_ind_data'' NS).
  Proof. apply is0gpd_forall; intros; apply is0gpd_paths. Defined.

  (** We decompose "precomposition with [f]" into a functor_sigma of two fiberwise functors.  Here is the first. *)
  Definition functor_Susp_ind_data'' (NS : P North * P South)
    : Susp_ind_data' Y P NS -> Susp_ind_data'' NS
    := fun g x => g (f x).

  Local Instance is0functor_functor_Susp_ind_data'' NS
    : Is0Functor (functor_Susp_ind_data'' NS).
  Proof.
    constructor.
    intros g h p a.
    exact (p (f a)).
  Defined.

  (** And here is the second.  This one is actually a fiberwise equivalence of types at each [x]. *)
  Definition equiv_Susp_ind_data' (NS : P North * P South) (x : X)
    : DPath P (merid (f x)) (fst NS) (snd NS)
      <~> DPath (P o functor_susp f) (merid x) (fst NS) (snd NS).
  Proof.
    etransitivity.
    - apply (equiv_transport (fun p => DPath P p (fst NS) (snd NS))).
      symmetry; apply ap_functor_susp_merid.
    - symmetry. 
      apply (dp_compose (functor_susp f) P (merid x)).
  Defined.

  Definition functor_Susp_ind_data' (NS : P North * P South)
    : Susp_ind_data'' NS -> Susp_ind_data' X (P o functor_susp f) NS.
  Proof.
    serapply (functor_forall idmap); intros x.
    apply equiv_Susp_ind_data'.
  Defined.

  Local Instance is0functor_functor_Susp_ind_data' NS
    : Is0Functor (functor_Susp_ind_data' NS).
  Proof.
    constructor.
    intros g h q x.
    cbn; apply ap, ap.
    exact (q x).
  Defined.

  (** And therefore a fiberwise equivalence of 0-groupoids. *)
  Local Instance isequiv0gpd_functor_Susp_ind_data' NS
    : IsEquiv0Gpd (functor_Susp_ind_data' NS).
  Proof.
    constructor.
    - intros g.
      unshelve econstructor.
      + intros x.
        apply ((equiv_Susp_ind_data' NS x)^-1).
        exact (g x).
      + intros x.
        apply eisretr.
    - intros g h p x.
      apply (equiv_inj (equiv_Susp_ind_data' NS x)).
      exact (p x).
  Defined.

  (** Now we put them together. *)
  Definition functor_Susp_ind_data
    : Susp_ind_data Y P -> Susp_ind_data X (P o functor_susp f)
    := fun NSg => (NSg.1 ; (functor_Susp_ind_data' NSg.1 o
                             (functor_Susp_ind_data'' NSg.1)) NSg.2).

  Local Instance is0functor_functor_Susp_ind_data
    : Is0Functor functor_Susp_ind_data.
  Proof.
    refine (is0functor_sigma _ _
           (fun NS => functor_Susp_ind_data' NS o functor_Susp_ind_data'' NS)).
  Defined.

  (** Here is the "precomposition with [functor_susp f]" functor. *)
  Definition functor_Susp_ind_type
    : Susp_ind_type Y P -> Susp_ind_type X (P o functor_susp f)
    := fun g => g o functor_susp f.

  Local Instance is0functor_functor_Susp_ind_type
    : Is0Functor functor_Susp_ind_type.
  Proof.
    constructor.
    intros g h p a.
    exact (p (functor_susp f a)).
  Defined.

  (** And here is the desired naturality square. *)
  Definition Susp_ind_inv_nat
    : (Susp_ind_inv X (P o functor_susp f)) o functor_Susp_ind_type
      $=> functor_Susp_ind_data o (Susp_ind_inv Y P).
  Proof.
    intros g; exists idpath; intros x.
    change (dp_apD (fun x0 : Susp X => g (functor_susp f x0)) (merid x) =
            (functor_Susp_ind_data (Susp_ind_inv Y P g)).2 x).
    refine (dp_apD_compose (functor_susp f) P (merid x) g @ _).
    cbn; apply ap.
    apply (moveL_transport_V (fun p => DPath P p (g North) (g South))).
    exact (apD (dp_apD g) (ap_functor_susp_merid f x)).
  Defined.

  (** From this we can deduce a equivalence between extendability, which is definitionally equal to split essential surjectivity of a functor between forall 0-groupoids. *)
  Definition extension_iff_functor_susp
    : (forall g, ExtensionAlong (functor_susp f) P g)
      <-> (forall NS g, ExtensionAlong f (fun x => DPath P (merid x) (fst NS) (snd NS)) g).
  Proof.
    (** The proof is by chaining logical equivalences. *)
    transitivity (SplEssSurj functor_Susp_ind_type).
    { reflexivity. }
    etransitivity.
    { refine (isesssurj_iff_commsq Susp_ind_inv_nat); try exact _.
      all:apply equiv0gpd_Susp_ind_inv. }
    etransitivity.
    { refine (isesssurj_iff_sigma _ _ 
                (fun NS => functor_Susp_ind_data' NS o functor_Susp_ind_data'' NS)). }
    apply iff_functor_forall; intros [N S]; cbn.
    etransitivity.
    { apply iffL_isesssurj; exact _. }
    reflexivity.
  Defined.

  (** We have to close the section now because we have to generalize [extension_iff_functor_susp] over [P]. *)

End UnivPropNat.

(** Now we can iterate, deducing [n]-extendability. *)
Definition extendable_iff_functor_susp
           {X Y : Type} (f : X -> Y) (P : Susp Y -> Type) (n : nat)
  : (ExtendableAlong n (functor_susp f) P)
    <-> (forall NS, ExtendableAlong n f (fun x => DPath P (merid x) (fst NS) (snd NS))).
Proof.
  revert P. induction n as [|n IHn]; intros P; [ split; intros; exact tt | ].
  (** It would be nice to be able to do this proof by chaining logcal equivalences too, especially since the two parts seem very similar.  But I haven't managed to make that work. *)
  split.
  - intros [e1 en] [N S]; split.
    + apply extension_iff_functor_susp.
      exact e1.
    + cbn; intros h k.
      pose (h' := Susp_ind_dp P N S h).
      pose (k' := Susp_ind_dp P N S k).
      specialize (en h' k').
      assert (IH := fst (IHn _) en (1,1)); clear IHn en.
      cbn in IH.
      refine (extendable_postcompose' n _ _ f _ IH); clear IH.
      intros y.
      etransitivity.
      1:symmetry; apply equiv_sq_dp_D.
      etransitivity.
      1:apply equiv_ds_transport_dpath.
      subst h' k'; cbn.
      apply equiv_concat_lr.
      * symmetry. exact (Susp_ind_dp_beta_merid P N S h y).
      * exact (Susp_ind_dp_beta_merid P N S k y).
  - intros e; split.
    + apply extension_iff_functor_susp.
      intros NS; exact (fst (e NS)).
    + intros h k.
      apply (IHn _).
      intros [p q].
      specialize (e (h North, k South)).
      cbn in *; apply snd in e.
      refine (extendable_postcompose' n _ _ f _ (e _ _)); intros y.
      etransitivity.
      2:apply equiv_sq_dp_D.
      etransitivity.
      2:symmetry;apply equiv_ds_transport_dpath.
      etransitivity.
      2:apply (equiv_moveR_transport_p (fun y0 : P North => DPath P (merid y) y0 (k South))).
      reflexivity.
Defined.

(** As usual, deducing oo-extendability is trivial. *)
Definition ooextendable_iff_functor_susp
           {X Y : Type} (f : X -> Y) (P : Susp Y -> Type)
  : (ooExtendableAlong (functor_susp f) P)
    <-> (forall NS, ooExtendableAlong f (fun x => DPath P (merid x) (fst NS) (snd NS))).
Proof.
  split; intros e.
  - intros NS n.
    apply extendable_iff_functor_susp.
    exact (e n).
  - intros n.
    apply extendable_iff_functor_susp.
    intros NS; exact (e NS n).
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
  - apply whiskerR, inverse, Susp_rec_beta_merid.
  - refine (concat_Ap n.2 (merid x) @ _).
    apply (concatR (concat_p1 _)), whiskerL. apply ap_const.
Defined.

(** ** Contractibility of the suspension *)

Global Instance contr_susp (A : Type) `{Contr A}
  : Contr (Susp A).
Proof.
  unfold Susp; exact _.
Defined.

(** ** Connectedness of the suspension *)

Global Instance isconnected_susp {n : trunc_index} {X : Type}
  `{H : IsConnected n X} : IsConnected n.+1 (Susp X).
Proof.
  apply isconnected_from_elim.
  intros C H' f. exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 allpath_p0] by (apply (isconnected_elim n); apply H').
  apply (Susp_ind (fun a => f a = f North) 1 p0^).
  intros x.
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.
