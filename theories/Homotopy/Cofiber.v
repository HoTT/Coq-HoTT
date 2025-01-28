Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc Basics.Equivalences.
Require Import Types.Unit Types.Paths Types.Universe Types.Sigma.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Colimits.Pushout Homotopy.Suspension.
Require Import Homotopy.NullHomotopy.
Require Import HFiber Limits.Pullback BlakersMassey.

Set Universe Minimization ToSet.

(** * Homotopy Cofibers *)

(** ** Definition *)

(** Homotopy cofibers or mapping cones are spaces constructed from a map [f : X -> Y] by contracting the image of [f] inside [Y] to a point. They can be thought of as a kind of coimage or quotient. *)

Definition Cofiber {X Y : Type} (f : X -> Y)
  := Pushout (const_tt X) f.

(** *** Constructors *)

(** Any element of [Y] can be included in the cofiber. *)
Definition cofib {X Y : Type} (f : X -> Y) : Y -> Cofiber f
  := pushr.

(** We have a distinguised point in the cofiber, where the image of [f] is contracted to. *)
Definition cf_apex {X Y : Type} (f : X -> Y) : Cofiber f
  := pushl tt.

(** Given an element [x : X], we have the path [cfglue f x] from the [f x] to the [cf_apex]. *)
Definition cfglue {X Y : Type} (f : X -> Y) (x : X) : cofib f (f x) = cf_apex f
  := (pglue _)^.

(** *** Induction and recursion principles *)

(** The recursion principle for the cofiber of [f : X -> Y] requires a function [g : Y -> Z] such that [g o f] is null homotopic, i.e. constant. *)
Definition cofiber_rec {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
  (null : NullHomotopy (g o f))
  : Cofiber f -> Z.
Proof.
  snrapply Pushout_rec.
  - intros; exact null.1.
  - exact g.
  - intros a.
    exact (null.2 a)^.
Defined.

(** The induction principle is similar, although requries a dependent form of null homotopy. *)
Definition cofiber_ind {X Y : Type} (f : X -> Y) (P : Cofiber f -> Type)
  (g : forall y, P (cofib f y))
  (null : exists b, forall x, transport P (cfglue f x) (g (f x)) = b)
  : forall x, P x.
Proof.
  snrapply Pushout_ind.
  - intros []; exact null.1.
  - intros y; apply g.
  - intros x.
    simpl.
    apply moveR_transport_p.
    exact (null.2 x)^.
Defined.

(** ** Functoriality *)

Local Close Scope trunc_scope.

(** The homotopy cofiber can be thought of as a functor from the category of arrows in [Type] to [Type]. *)

(** 1-functorial action. *)
Definition functor_cofiber {X Y X' Y' : Type} {f : X -> Y} {f' : X' -> Y'}
  (g : X -> X') (h : Y -> Y') (p : h o f == f' o g)
  : Cofiber f -> Cofiber f'
  := functor_pushout g idmap h (fun _ => idpath) p.

(** 2-functorial action. *)
Definition functor_cofiber_homotopy {X Y X' Y' : Type} {f : X -> Y} {f' : X' -> Y'}
  {g g' : X -> X'} {h h' : Y -> Y'} {p : h o f == f' o g} {p' : h' o f == f' o g'}
  (u : g == g') (v : h == h') 
  (r : forall x, p x @ ap f' (u x) = v (f x) @ p' x)
  : functor_cofiber g h p == functor_cofiber g' h' p'
  := functor_pushout_homotopic
      (f := fun _ => _) (f' := fun _ => _) (k := idmap) (k' := idmap) (p' := fun _ => 1)
      u (fun _ => 1) v (fun x => concat_1p _ @ ap_const _ _) r.

(** The cofiber functor preserves the identity map. *) 
Definition functor_cofiber_idmap {X Y : Type} (f : X -> Y)
  : functor_cofiber (f:=f) idmap idmap (fun _ => 1) == idmap
  := functor_pushout_idmap.

(** The cofiber functor preserves composition of squares. (When mapping parallel edges). *)
Definition functor_cofiber_compose {X Y X' Y' X'' Y'' : Type}
  {f : X -> Y} {f' : X' -> Y'} {f'' : X'' -> Y''}
  {g : X -> X'} {g' : X' -> X''} {h : Y -> Y'} {h' : Y' -> Y''}
  (p : h o f == f' o g) (p' : h' o f' == f'' o g')
  : functor_cofiber (g' o g) (h' o h) (fun x => ap h' (p x) @ p' (g x))
    == functor_cofiber g' h' p' o functor_cofiber g h p
  := functor_pushout_compose g idmap h g' idmap h' (fun _ => 1) p (fun _ => 1) p'.

Local Open Scope trunc_scope.

(** ** Connectivity of cofibers *)

(** The cofiber of an [n]-conencted map is [n.+1]-connected. *)
Definition isconnnected_cofiber (n : trunc_index) {X Y : Type} (f : X -> Y)
  {fc : IsConnMap n f}
  : IsConnected n.+1 (Cofiber f).
Proof.
  apply isconnected_from_elim.
  intros C H' g.
  exists (g (cf_apex _)).
  snrapply cofiber_ind.
  - rapply (conn_map_elim n f).
    intros x.
    exact (ap g (cfglue f x)).
  - exists idpath.
    intros x.
    lhs snrapply transport_paths_Fl.
    apply moveR_Vp.
    rhs nrapply concat_p1.
    nrapply conn_map_comp.
Defined.

(** ** Comparison of fibers and cofibers *)

Definition fiber_to_path_cofiber {X Y : Type} (f : X -> Y) (y : Y)
  : hfiber f y -> cofib f y = cf_apex f.
Proof.
  intros [x p].
  lhs nrapply (ap (cofib f) p^).
  apply cfglue.
Defined.

(** Blakers-Massey implies that the comparison map is highly connected. *)
Definition isconnected_fiber_to_cofiber `{Univalence}
  (n m : trunc_index) {X Y : Type} {ac : IsConnected n.+1 X}
  (f : X -> Y) {fc : IsConnMap m.+1 f} (y : Y)
  : IsConnMap (m +2+ n) (fiber_to_path_cofiber f y).
Proof.
  snrapply conn_map_fiber.
  rapply (cancelR_conn_map _ (equiv_fibration_replacement _)).
  snrapply cancelL_equiv_conn_map.
  - exact (Pullback (pushl (f:=const_tt X) (g:=f)) pushr).
  - unfold Pullback.
    refine ((equiv_contr_sigma _)^-1 oE _).
    snrapply equiv_functor_sigma_id.
    intros y'.
    snrapply equiv_path_inverse.
  - snrapply conn_map_homotopic.
    3: rapply blakers_massey_po.
    intros x.
    snrapply path_sigma.
    1: reflexivity.
    snrapply path_sigma.
    1: reflexivity.
    unfold fiber_to_path_cofiber; simpl.
    lhs_V nrapply inv_V.
    nrapply ap; symmetry.
    apply concat_1p.
Defined.
