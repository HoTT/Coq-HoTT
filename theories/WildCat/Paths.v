Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import WildCat.Core WildCat.TwoOneCat WildCat.NatTrans.

(** * Path groupoids as wild categories *)

(** Every type is a wild (2,1)-category. *)

(** Not global instances for now *)

(** These are written so that they can be augmented with an existing wildcat structure. For instance, you may partially define a wildcat and ask for paths for the higher cells. *)

(** Any type is a graph with morphisms given by the identity type. *)
Definition isgraph_paths (A : Type) : IsGraph A
  := {| Hom := paths |}.

(** Any graph is a 2-graph with 2-cells given by the identity type. *)
Definition is2graph_paths (A : Type) `{IsGraph A} : Is2Graph A
  := fun _ _ => isgraph_paths _.

(** Any 2-graph is a 3-graph with 3-cells given by the identity type. *)
Definition is3graph_paths (A : Type) `{Is2Graph A} : Is3Graph A
  := fun _ _ => is2graph_paths _.

(** We assume these as instances for the rest of the file with a low priority. *)
Local Existing Instances isgraph_paths is2graph_paths is3graph_paths | 10.

(** Any type has composition and identity morphisms given by path concatenation and reflexivity. *)
Instance is01cat_paths (A : Type) : Is01Cat A
  := {| Id := @idpath _ ; cat_comp := fun _ _ _ x y => concat y x |}.

(** Any type has a 0-groupoid structure with inverse morphisms given by path inversion. *)
Instance is0gpd_paths (A : Type) : Is0Gpd A
  := { gpd_rev := @inverse _ }.

(** Postcomposition is a 0-functor when the 2-cells are paths. *)
Instance is0functor_cat_postcomp_paths (A : Type) `{Is01Cat A}
  (a b c : A) (g : b $-> c)
  : Is0Functor (cat_postcomp a g).
Proof.
  snapply Build_Is0Functor.
  exact (@ap _ _ (cat_postcomp a g)).
Defined.

(** Precomposition is a 0-functor when the 2-cells are paths. *)
Instance is0functor_cat_precomp_paths (A : Type) `{Is01Cat A}
  (a b c : A) (f : a $-> b)
  : Is0Functor (cat_precomp c f).
Proof.
  snapply Build_Is0Functor.
  exact (@ap _ _ (cat_precomp c f)).
Defined.

(** Any type is a 1-category with n-morphisms given by paths. *)
Instance is1cat_paths {A : Type} : Is1Cat A.
Proof.
  snapply Build_Is1Cat.
  - exact _.
  - exact _.
  - exact _.
  - exact _.
  - exact (@concat_p_pp A).
  - exact (@concat_pp_p A).
  - exact (@concat_p1 A).
  - exact (@concat_1p A).
Defined.

(** Any type is a 1-groupoid with morphisms given by paths. *)
Instance is1gpd_paths {A : Type} : Is1Gpd A.
Proof.
  snapply Build_Is1Gpd.
  - exact (@concat_pV A).
  - exact (@concat_Vp A).
Defined.

(** Any type is a 2-category with higher morphisms given by paths. *)
Instance is21cat_paths {A : Type} : Is21Cat A.
Proof.
  snapply Build_Is21Cat.
  - exact _.
  - exact _.
  - intros x y z p.
    snapply Build_Is1Functor.
    + intros a b q r.
      exact (ap (fun x => whiskerR x _)).
    + reflexivity.
    + intros a b c.
      exact (whiskerR_pp p).
  - intros x y z p.
    snapply Build_Is1Functor.
    + intros a b q r.
      exact (ap (whiskerL p)).
    + reflexivity.
    + intros a b c.
      exact (whiskerL_pp p).
  - intros a b c q r s t h g.
    exact (concat_whisker q r s t h g)^.
  - intros a b c d q r.
    snapply Build_Is1Natural.
    intros s t h.
    apply concat_p_pp_nat_r.
  - intros a b c d q r.
    snapply Build_Is1Natural.
    intros s t h.
    apply concat_p_pp_nat_m.
  - intros a b c d q r.
    snapply Build_Is1Natural.
    intros s t h.
    apply concat_p_pp_nat_l.
  - intros a b.
    snapply Build_Is1Natural.
    intros p q h; cbn.
    apply moveL_Mp.
    lhs napply concat_p_pp.
    exact (whiskerR_p1 h).
  - intros a b.
    snapply Build_Is1Natural.
    intros p q h.
    apply moveL_Mp.
    lhs rapply concat_p_pp.
    exact (whiskerL_1p h).
  - intros a b c d e p q r s.
    lhs napply concat_p_pp.
    exact (pentagon p q r s).
  - intros a b c p q.
    exact (triangulator p q).
Defined.
