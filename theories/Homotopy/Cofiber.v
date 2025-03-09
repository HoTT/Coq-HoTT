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
  := Pushout f (const_tt X).

(** *** Constructors *)

(** Any element of [Y] can be included in the cofiber. *)
Definition cofib {X Y : Type} (f : X -> Y) : Y -> Cofiber f
  := pushl.

(** We have a distinguised point in the cofiber, where the image of [f] is contracted to. *)
Definition cf_apex {X Y : Type} (f : X -> Y) : Cofiber f
  := pushr tt.

(** Given an element [x : X], we have the path [cfglue f x] from the [f x] to the [cf_apex]. *)
Definition cfglue {X Y : Type} (f : X -> Y) (x : X) : cofib f (f x) = cf_apex f
  := pglue _.

(** *** Induction and recursion principles *)

(** The recursion principle for the cofiber of [f : X -> Y] requires a function [g : Y -> Z] such that [g o f] is null homotopic, i.e. constant. *)
Definition cofiber_rec {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
  (null : NullHomotopy (g o f))
  : Cofiber f -> Z.
Proof.
  snapply Pushout_rec.
  - exact g.
  - intros; exact null.1.
  - intros a.
    exact (null.2 a).
Defined.

(** The induction principle is similar, although requries a dependent form of null homotopy. *)
Definition cofiber_ind {X Y : Type} (f : X -> Y) (P : Cofiber f -> Type)
  (g : forall y, P (cofib f y))
  (null : exists b, forall x, transport P (cfglue f x) (g (f x)) = b)
  : forall x, P x.
Proof.
  snapply Pushout_ind.
  - intros y; apply g.
  - intros []; exact null.1.
  - exact null.2.
Defined.

(** ** Functoriality *)

Local Close Scope trunc_scope.

(** The homotopy cofiber can be thought of as a functor from the category of arrows in [Type] to [Type]. *)

(** 1-functorial action. *)
Definition functor_cofiber {X Y X' Y' : Type} {f : X -> Y} {f' : X' -> Y'}
  (g : X -> X') (h : Y -> Y') (p : h o f == f' o g)
  : Cofiber f -> Cofiber f'
  := functor_pushout g h idmap p (fun _ => idpath).

(** 2-functorial action. *)
Definition functor_cofiber_homotopy {X Y X' Y' : Type} {f : X -> Y} {f' : X' -> Y'}
  {g g' : X -> X'} {h h' : Y -> Y'} {p : h o f == f' o g} {p' : h' o f == f' o g'}
  (u : g == g') (v : h == h') 
  (r : forall x, p x @ ap f' (u x) = v (f x) @ p' x)
  : functor_cofiber g h p == functor_cofiber g' h' p'.
Proof.
  snapply (functor_pushout_homotopic u v (fun _ => 1) r).
  intro x; exact (concat_1p _ @ ap_const _ _).
Defined.

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
  := functor_pushout_compose g h idmap g' h' idmap p (fun _ => 1) p' (fun _ => 1).

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
  snapply cofiber_ind.
  - rapply (conn_map_elim n f).
    intros x.
    exact (ap g (cfglue f x)).
  - exists idpath.
    intros x.
    lhs snapply transport_paths_Fl.
    apply moveR_Vp.
    rhs napply concat_p1.
    napply conn_map_comp.
Defined.

(** ** Comparison of fibers and cofibers *)

Definition fiber_to_path_cofiber {X Y : Type} (f : X -> Y) (y : Y)
  : hfiber f y -> cofib f y = cf_apex f.
Proof.
  intros [x p].
  lhs_V napply (ap (cofib f) p).
  apply cfglue.
Defined.

(** Blakers-Massey implies that the comparison map is highly connected. *)
Definition isconnected_fiber_to_cofiber `{Univalence}
  (n m : trunc_index) {X Y : Type} {ac : IsConnected m.+1 X}
  (f : X -> Y) {fc : IsConnMap n.+1 f} (y : Y)
  : IsConnMap (m +2+ n) (fiber_to_path_cofiber f y).
Proof.
  (* It's enough to check the connectivity of [functor_sigma idmap (fiber_to_path_cofiber f)]. *)
  revert y; snapply conn_map_fiber.
  (* We precompose with the equivalence [X <~> { y : Y & hfiber f y }]. *)
  rapply (cancelR_conn_map _ (equiv_fibration_replacement _)).
  (* The Sigma-type [{ y : Y & cofib f y = cf_apex f}] in the codomain is the fiber of the map [cofib f], and so it is equivalent to the pullback of the cospan in the pushout square defining [Cofiber f].  We postcompose with this equivalence. *)
  snapply (cancelL_equiv_conn_map _ _ (equiv_pullback_unit_hfiber _ _)^-1%equiv).
  (* The composite is homotopic to the map from [blakers_massey_po], with the only difference being an extra [1 @ _]. *)
  snapply conn_map_homotopic.
  3: rapply blakers_massey_po.
  (* Use [compute.] to see the details of the goal. *)
  intros x.
  apply (ap (fun z => (f x; tt; z))).
  unfold fiber_to_path_cofiber; simpl.
  symmetry; apply concat_1p.
Defined.
