Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import Types.Unit Types.Paths.
Require Import Colimits.Pushout.
Require Import Homotopy.NullHomotopy.

Set Universe Minimization ToSet.

(** * Homotopy Cofibers *)

(** ** Definition *)

(** Homotopy cofibers or mapping cones are spaces constructed from a map [f : X -> Y] by contracting the image of [f] inside [Y] to a point. They can be thought of as a kind of coimage or quotient. *)

Definition cofiber {X Y : Type} (f : X -> Y)
  := Pushout (const_tt X) f.

(** *** Constructors *)

(** Any element of [Y] can be included in the cofiber. *)
Definition cofib {X Y : Type} (f : X -> Y) : Y -> cofiber f
  := pushr.

(** We have a distinguised point in the cofiber, where the image of [f] is contracted to. *)
Definition apex {X Y : Type} (f : X -> Y) : cofiber f
  := pushl tt.

(** Given an element [x : X], we have the path [leg] from the [f x] to the [apex]. *)
Definition leg {X Y : Type} (f : X -> Y) (x : X) : cofib f (f x) = apex f
  := (pglue _)^.

(** *** Induction and recursion principles *)

(** The recursion principle for the cofiber of [f : X -> Y] requires a function [g : Y -> Z] such that [g o f] is null homotopic, i.e. constant. *)
Definition cofiber_rec {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
  (null : NullHomotopy (g o f))
  : cofiber f -> Z.
Proof.
  snrapply Pushout_rec.
  - intros; exact null.1.
  - exact g.
  - intros a.
    exact (null.2 a)^.
Defined.

(** The induction principle is similar, although requries a dependent form of null homotopy. *)
Definition cofiber_ind {X Y : Type} (f : X -> Y) (P : cofiber f -> Type)
  (g : forall y, P (cofib f y))
  (null : exists b, forall x, transport P (leg f x) (g (f x)) = b)
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

(** The homotopy cofiber can be thought of as a functor from the category of arrows in [Type] to [Type]. *)

(** 1-functorial action. *)
Definition functor_cofiber {X Y X' Y' : Type} {f : X -> Y} {f' : X' -> Y'}
  (g : X -> X') (h : Y -> Y') (p : h o f == f' o g)
  : cofiber f -> cofiber f'
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
