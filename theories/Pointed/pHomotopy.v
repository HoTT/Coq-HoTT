Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import WildCat.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse.

Local Open Scope pointed_scope.

(** Some higher homotopies *)

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_p1.
Defined.

(** ** [phomotopy_path] respects 2-cells. *)
Definition phomotopy_path2 {A : pType} {P : pFam A}
  {f g : pForall A P} {p p' : f = g} (q : p = p')
  : phomotopy_path p ==* phomotopy_path p'.
Proof.
  induction q. reflexivity.
Defined.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V {A : pType} {P : pFam A}
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. exact gpd_rev_1.
Defined.

Notation "p @@* q" := (p $@@ q).

(** Pointed homotopies in a set form an HProp. *)
Global Instance ishprop_phomotopy_hset `{Funext} {X Y : pType} `{IsHSet Y} (f g : X ->* Y)
  : IsHProp (f ==* g)
  := inO_equiv_inO' (O:=Tr (-1)) _ (issig_phomotopy f g).
