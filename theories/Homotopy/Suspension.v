Require Import Basics.
Require Import Types.
Require Import Cubical.DPath Cubical.DPathSquare.
Require Import WildCat.
Require Import Colimits.Pushout.
Require Import Homotopy.NullHomotopy.
Require Import Truncations.Core.
Require Import Modalities.Modality.
Require Import Extensions.

(** * The suspension of a type *)

Generalizable Variables X A B f g n.

Local Open Scope path_scope.

(* ** Definition of suspension *)

(** We define the suspension of a type X as the pushout of 1 <- X -> 1 *)
Definition Susp (X : Type) := Pushout@{_ Set Set _} (const_tt X) (const_tt X).
Definition North {X} : Susp X := pushl tt.
Definition South {X} : Susp X := pushr tt.
Definition merid {X} (x : X) : North = South := pglue x.

(** We think of this as the HIT with two points [North] and [South] and a path [merid] between them *)

(** We can derive an induction principle for the suspension *)
Definition Susp_ind {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  : forall (y : Susp X), P y.
Proof.
  srapply Pushout_ind.
  - exact (Unit_ind H_N).
  - exact (Unit_ind H_S).
  - exact (H_merid).
Defined.

(** We can also derive the computation rule *)
Definition Susp_ind_beta_merid {X : Type}
  (P : Susp X -> Type) (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S) (x : X)
  : apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  srapply Pushout_ind_beta_pglue.
Defined.

(** We want to allow the user to forget that we've defined suspension as a pushout and make it look like it was defined directly as a HIT. This has the advantage of not having to assume any new HITs but allowing us to have conceptual clarity. *)
Arguments Susp : simpl never.
Arguments North : simpl never.
Arguments South : simpl never.
Arguments merid : simpl never.
Arguments Susp_ind_beta_merid : simpl never.

(** A version of [Susp_ind] specifically for proving that two functions defined on a suspension are homotopic. *)
Definition Susp_ind_FlFr {X Y : Type} (f g : Susp X -> Y)
  (HN : f North = g North)
  (HS : f South = g South)
  (Hmerid : forall x, ap f (merid x) @ HS = HN @ ap g (merid x))
  : f == g.
Proof.
  snrapply (Susp_ind _ HN HS).
  intros x.
  nrapply transport_paths_FlFr'.
  exact (Hmerid x).
Defined.

(** A version of [Susp_ind] specifically for proving that the composition of two functions to and from a suspension are homotopic to the identity map. *)
Definition Susp_ind_FFlr {X Y : Type} (f : Susp X -> Y) (g : Y -> Susp X)
  (HN : g (f North) = North)
  (HS : g (f South) = South)
  (Hmerid : forall x, ap g (ap f (merid x)) @ HS = HN @ merid x)
  : g o f == idmap.
Proof.
  snrapply (Susp_ind _ HN HS).
  intros x.
  snrapply (transport_paths_FFlr' (f:=f) (g:=g)).
  exact (Hmerid x).
Defined.

Definition Susp_ind_FFlFr {X Y Z : Type}
  (f : Susp X -> Y) (g : Y -> Z) (h : Susp X -> Z)
  (HN : g (f North) = h North)
  (HS : g (f South) = h South)
  (Hmerid : forall x, ap g (ap f (merid x)) @ HS = HN @ ap h (merid x))
  : g o f == h.
Proof.
  snrapply (Susp_ind _ HN HS).
  intros x.
  snrapply (transport_paths_FFlFr' (f:=f) (g:=g) (h:=h)).
  exact (Hmerid x).
Defined.

(** A version of [Susp_ind] specifically for proving a composition square from a suspension. *)
Definition Susp_ind_FFlFFr {X Y Y' Z : Type}
  (f : Susp X -> Y) (f' : Susp X -> Y') (g : Y -> Z) (g' : Y' -> Z)
  (HN : g (f North) = g' (f' North)) (HS : g (f South) = g' (f' South))
  (Hmerid : forall x, ap g (ap f (merid x)) @ HS = HN @ ap g' (ap f' (merid x)))
  : g o f == g' o f'.
Proof.
  snrapply (Susp_ind _ HN HS).
  intros x.
  snrapply (transport_paths_FFlFFr' (f:=f) (f':=f') (g:=g) (g':=g')).
  exact (Hmerid x).
Defined.

(* ** Non-dependent eliminator. *)

Definition Susp_rec {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
  : Susp X -> Y
  := Pushout_rec (f:=const_tt X) (g:=const_tt X) Y (Unit_ind H_N) (Unit_ind H_S) H_merid.

Global Arguments Susp_rec {X Y}%_type_scope H_N H_S H_merid%_function_scope _.

Definition Susp_rec_beta_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
  : ap (Susp_rec H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  srapply Pushout_rec_beta_pglue.
Defined.

(** ** Eta-rule. *)

(** The eta-rule for suspension states that any function out of a suspension is equal to one defined by [Susp_ind] in the obvious way. We give it first in a weak form, producing just a pointwise equality, and then turn this into an actual equality using [Funext]. *)
Definition Susp_ind_eta_homotopic {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f == Susp_ind P (f North) (f South) (fun x => apD f (merid x)).
Proof.
  unfold pointwise_paths. refine (Susp_ind _ 1 1 _).
  intros x.
  refine (transport_paths_FlFr_D
    (g := Susp_ind P (f North) (f South) (fun x : X => apD f (merid x)))
    _ _ @ _); simpl.
  apply moveR_pM.
  apply equiv_p1_1q.
  apply ap, inverse. refine (Susp_ind_beta_merid _ _ _ _ _).
Defined.

Definition Susp_rec_eta_homotopic {X Y : Type} (f : Susp X -> Y)
  : f == Susp_rec (f North) (f South) (fun x => ap f (merid x)).
Proof.
  snrapply Susp_ind_FlFr.
  1, 2: reflexivity.
  intro x.
  apply equiv_p1_1q.
  exact (Susp_rec_beta_merid _)^.
Defined.

Definition Susp_ind_eta `{Funext}
  {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f = Susp_ind P (f North) (f South) (fun x => apD f (merid x))
  := path_forall _ _ (Susp_ind_eta_homotopic f).

Definition Susp_rec_eta `{Funext} {X Y : Type} (f : Susp X -> Y)
  : f = Susp_rec (f North) (f South) (fun x => ap f (merid x))
  := path_forall _ _ (Susp_rec_eta_homotopic f).

(** ** Functoriality *)

Definition functor_susp {X Y : Type} (f : X -> Y)
  : Susp X -> Susp Y.
Proof.
  srapply Susp_rec.
  - exact North.
  - exact South.
  - intros x; exact (merid (f x)).
Defined.

Definition functor_susp_beta_merid {X Y : Type} (f : X -> Y) (x : X)
  : ap (functor_susp f) (merid x) = merid (f x).
Proof.
  srapply Susp_rec_beta_merid.
Defined.

Definition functor_susp_compose {X Y Z}
  (f : X -> Y) (g : Y -> Z)
  : functor_susp (g o f) == functor_susp g o functor_susp f.
Proof.
  snrapply Susp_ind_FlFr.
  1,2: reflexivity.
  intro x.
  apply equiv_p1_1q.
  lhs nrapply functor_susp_beta_merid; symmetry.
  lhs nrefine (ap_compose (functor_susp f) _ (merid x)).
  lhs nrefine (ap _ (functor_susp_beta_merid _ _)).
  apply functor_susp_beta_merid.
Defined.

Definition functor_susp_idmap {X}
  : functor_susp idmap == (idmap : Susp X -> Susp X).
Proof.
  snrapply Susp_ind_FlFr.
  1,2: reflexivity.
  intro x.
  apply equiv_p1_1q.
  lhs nrapply functor_susp_beta_merid.
  symmetry; apply ap_idmap.
Defined.

Definition functor2_susp {X Y} {f g : X -> Y} (h : f == g)
  : functor_susp f == functor_susp g.
Proof.
  srapply Susp_ind_FlFr.
  1, 2: reflexivity.
  intro x.
  apply equiv_p1_1q.
  lhs nrapply (functor_susp_beta_merid f).
  rhs nrapply (functor_susp_beta_merid g).
  apply ap, h.
Defined.

Global Instance is0functor_susp : Is0Functor Susp
  := Build_Is0Functor _ _ _ _ Susp (@functor_susp).

Global Instance is1functor_susp : Is1Functor Susp
  := Build_Is1Functor _ _ _ _ _ _ _ _ _ _ Susp _
      (@functor2_susp) (@functor_susp_idmap) (@functor_susp_compose).

(** ** Universal property *)

Definition equiv_Susp_rec `{Funext} (X Y : Type)
  : (Susp X -> Y) <~> { NS : Y * Y & X -> fst NS = snd NS }.
Proof.
  snrapply equiv_adjointify.
  - intros f.
    exists (f North, f South).
    intros x; exact (ap f (merid x)).
  - intros [[N S] m].
    exact (Susp_rec N S m).
  - intros [[N S] m].
    apply ap, path_arrow.
    intros x; apply Susp_rec_beta_merid.
  - intros f.
    symmetry; apply Susp_rec_eta.
Defined.

(** Using wild 0-groupoids, the universal property can be proven without funext.  A simple equivalence of 0-groupoids between [Susp X -> Y] and [{ NS : Y * Y & X -> fst NS = snd NS }] would not carry all the higher-dimensional information, but if we generalize it to dependent functions, then it does suffice. *)
Section UnivProp.
  Context (X : Type) (P : Susp X -> Type).

  (** Here is the domain of the equivalence: sections of [P] over [Susp X]. *)
  Definition Susp_ind_type := forall z:Susp X, P z.

  (** [isgraph_paths] is not a global instance, so we define this by hand.  The fact that this is a 01cat and a 0gpd is obtained using global instances. *)
  Local Instance isgraph_Susp_ind_type : IsGraph Susp_ind_type.
  Proof. apply isgraph_forall; intros; apply isgraph_paths. Defined.

  (** The codomain is a sigma-groupoid of this family, consisting of input data for [Susp_ind]. *)
  Definition Susp_ind_data' (NS : P North * P South)
    := forall x:X, DPath P (merid x) (fst NS) (snd NS).

  (** Again, the rest of the wild category structure is obtained using global instances. *)
  Local Instance isgraph_Susp_ind_data' NS : IsGraph (Susp_ind_data' NS).
  Proof. apply isgraph_forall; intros; apply isgraph_paths. Defined.

  (** Here is the codomain itself.  This is a 01cat and a 0gpd via global instances. *)
  Definition Susp_ind_data := sig Susp_ind_data'.

  (** Here is the functor. *)
  Definition Susp_ind_inv : Susp_ind_type -> Susp_ind_data.
  Proof.
    intros f.
    exists (f North,f South).
    intros x.
    exact (apD f (merid x)).
  Defined.

  Local Instance is0functor_susp_ind_inv : Is0Functor Susp_ind_inv.
  Proof.
    constructor; unfold Susp_ind_type; cbn.
    intros f g p.
    unshelve econstructor.
    - apply path_prod; apply p.
    - intros x.
      rewrite transport_path_prod, !transport_forall_constant; cbn.
      apply ds_transport_dpath.
      exact (dp_apD_nat p (merid x)).
  Defined.

  (** And now we can prove that it's an equivalence of 0-groupoids, using the definition from WildCat/EquivGpd. *)
  Definition issurjinj_Susp_ind_inv : IsSurjInj Susp_ind_inv.
  Proof.
    constructor.
    - intros [[n s] g].
      exists (Susp_ind P n s g); cbn.
      exists idpath.
      intros x; cbn.
      apply Susp_ind_beta_merid.
    - intros f g [p q]; cbn in *.
      srapply Susp_ind; cbn.
      1: exact (ap fst p).
      1: exact (ap snd p).
      intros x; specialize (q x).
      apply ds_dp.
      apply ds_transport_dpath.
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

  (** We recall these instances from the previous section. *)
  Local Existing Instances isgraph_Susp_ind_type isgraph_Susp_ind_data'.

  (** Here is an intermediate family of groupoids that we have to use, since precomposition with [f] doesn't land in quite the right place. *)
  Definition Susp_ind_data'' (NS : P North * P South)
    := forall x:X, DPath P (merid (f x)) (fst NS) (snd NS).

  (** This is a 01cat and a 0gpd via global instances. *)
  Local Instance isgraph_Susp_ind_data'' NS : IsGraph (Susp_ind_data'' NS).
  Proof. apply isgraph_forall; intros; apply isgraph_paths. Defined.

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
    - nrapply (equiv_transport (fun p => DPath P p (fst NS) (snd NS))).
      symmetry; apply functor_susp_beta_merid.
    - symmetry. 
      apply (dp_compose (functor_susp f) P (merid x)).
  Defined.

  Definition functor_Susp_ind_data' (NS : P North * P South)
    : Susp_ind_data'' NS -> Susp_ind_data' X (P o functor_susp f) NS.
  Proof.
    srapply (functor_forall idmap); intros x.
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
  Local Instance issurjinj_functor_Susp_ind_data' NS
    : IsSurjInj (functor_Susp_ind_data' NS).
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
    change (apD (fun x0 : Susp X => g (functor_susp f x0)) (merid x) =
            (functor_Susp_ind_data (Susp_ind_inv Y P g)).2 x).
    refine (dp_apD_compose (functor_susp f) P (merid x) g @ _).
    cbn; apply ap.
    apply (moveL_transport_V (fun p => DPath P p (g North) (g South))).
    exact (apD (apD g) (functor_susp_beta_merid f x)).
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
      all:apply issurjinj_Susp_ind_inv. }
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
  (** It would be nice to be able to do this proof by chaining logical equivalences too, especially since the two parts seem very similar.  But I haven't managed to make that work. *)
  split.
  - intros [e1 en] [N S]; split.
    + apply extension_iff_functor_susp.
      exact e1.
    + cbn; intros h k.
      pose (h' := Susp_ind P N S h).
      pose (k' := Susp_ind P N S k).
      specialize (en h' k').
      assert (IH := fst (IHn _) en (1,1)); clear IHn en.
      cbn in IH.
      refine (extendable_postcompose' n _ _ f _ IH); clear IH.
      intros y.
      etransitivity.
      1: nrapply ds_dp.
      etransitivity.
      1: apply ds_transport_dpath.
      subst h' k'; cbn.
      apply equiv_concat_lr.
      * symmetry. exact (Susp_ind_beta_merid P N S h y).
      * exact (Susp_ind_beta_merid P N S k y).
  - intros e; split.
    + apply extension_iff_functor_susp.
      intros NS; exact (fst (e NS)).
    + intros h k.
      apply (IHn _).
      intros [p q].
      specialize (e (h North, k South)).
      cbn in *; apply snd in e.
      refine (extendable_postcompose' n _ _ f _ (e _ _)); intros y.
      symmetry.
      etransitivity.
      1: nrapply ds_dp.
      etransitivity.
      1: apply ds_transport_dpath.
      etransitivity.
      1: reflexivity.
      symmetry.
      apply (equiv_moveR_transport_p (fun y0 : P North => DPath P (merid y) y0 (k South))).
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

Definition nullhomot_susp_from_paths {X Z : Type} (f : Susp X -> Z)
  (n : NullHomotopy (fun x => ap f (merid x)))
: NullHomotopy f.
Proof.
  exists (f North).
  refine (Susp_ind _ 1 n.1^ _); intros x.
  refine (transport_paths_Fl _ _ @ _).
  apply (concat (concat_p1 _)), ap. apply n.2.
Defined.

Definition nullhomot_paths_from_susp {X Z : Type} (H_N H_S : Z) (f : X -> H_N = H_S)
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
    as [p0 allpath_p0] by (apply (isconnected_elim n); rapply H').
  apply (Susp_ind (fun a => f a = f North) 1 p0^).
  intros x.
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.

(** ** Negation map *)

(** The negation map on the suspension is defined by sending [North] to [South] and vice versa, and acting by flipping on the meridians. *)
Definition susp_neg (A : Type) : Susp A -> Susp A
  := Susp_rec South North (fun a => (merid a)^).

(** The negation map is an involution. *)
Definition susp_neg_inv (A : Type) : susp_neg A o susp_neg A == idmap.
Proof.
  snrapply Susp_ind_FFlr.
  1, 2: reflexivity.
  intro a.
  apply equiv_p1_1q.
  lhs nrapply ap.
  1: snrapply Susp_rec_beta_merid.
  lhs nrapply (ap_V _ (merid a)).
  lhs nrapply ap.
  1: snrapply Susp_rec_beta_merid.
  nrapply inv_V.
Defined.

Global Instance isequiv_susp_neg (A : Type) : IsEquiv (susp_neg A)
  := isequiv_involution (susp_neg A) (susp_neg_inv A).

Definition equiv_susp_neg (A : Type) : Susp A <~> Susp A
  := Build_Equiv _ _ (susp_neg A) _.

(** By using the suspension functor, we can also define another negation map on [Susp (Susp A))]. It turns out these are homotopic. *)
Definition susp_neg_stable (A : Type)
  : functor_susp (susp_neg A) == susp_neg (Susp A).
Proof.
  snrapply Susp_ind_FlFr; simpl.
  - exact (merid North).
  - exact (merid South)^.
  - intro x.
    lhs nrapply whiskerR.
    1: nrapply functor_susp_beta_merid.
    rhs nrapply whiskerL.
    2: nrapply Susp_rec_beta_merid.
    revert x; snrapply Susp_ind_FlFr; simpl.
    + exact (concat_pV _ @ (concat_pV _)^).
    + reflexivity.
    + intro a.
      lhs nrapply concat_p1.
      lhs nrapply (ap_compose _ (fun y => merid y @ _) (merid a)).
      lhs nrapply ap.
      1: nrapply Susp_rec_beta_merid.
      simpl.
      generalize (merid a) as p.
      generalize (@South A) as s.
      intros s p; destruct p.
      simpl.
      symmetry.
      lhs nrapply concat_p1.
      apply concat_pV.
Defined.

(** [susp_neg] is a natural equivalence on the suspension functor. *)
Definition susp_neg_natural {A B : Type} (f : A -> B)
  : susp_neg B o functor_susp f == functor_susp f o susp_neg A.
Proof.
  snrapply Susp_ind_FFlFFr.
  1, 2: reflexivity.
  intro a.
  apply equiv_p1_1q.
  lhs nrapply (ap _ (Susp_rec_beta_merid _)).
  rhs nrapply (ap _ (Susp_rec_beta_merid _)).
  rhs nrapply (ap_V _ (merid a)).
  rhs nrapply (ap _ (Susp_rec_beta_merid _)).
  nrapply Susp_rec_beta_merid.
Defined.
