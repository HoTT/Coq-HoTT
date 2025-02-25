Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import WildCat.Core WildCat.TwoOneCat WildCat.NatTrans WildCat.Bifunctor.

(** * Path groupoids as wild categories *)

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
Global Instance is01cat_paths (A : Type) : Is01Cat A
  := {| Id := @idpath _ ; cat_comp := fun _ _ _ x y => concat y x |}.

(** Any type has a 0-groupoid structure with inverse morphisms given by path inversion. *)
Global Instance is0gpd_paths (A : Type) : Is0Gpd A
  := {| gpd_rev := @inverse _ |}.

(** Postcomposition is a 0-functor when the 2-cells are paths. *)
Global Instance is0functor_cat_postcomp_paths (A : Type) `{Is01Cat A}
  (a b c : A) (g : b $-> c)
  : Is0Functor (cat_postcomp a g).
Proof.
  snrapply Build_Is0Functor.
  exact (@ap _ _ (cat_postcomp a g)).
Defined.

(** Precomposition is a 0-functor when the 2-cells are paths. *)
Global Instance is0functor_cat_precomp_paths (A : Type) `{Is01Cat A}
  (a b c : A) (f : a $-> b)
  : Is0Functor (cat_precomp c f).
Proof.
  snrapply Build_Is0Functor.
  exact (@ap _ _ (cat_precomp c f)).
Defined.

(** Composition is a 0-bifunctor when the 2-cells are paths. *)
Instance is0bifunctor_cat_comp_paths (A :Type) `{Is01Cat A} (a b c :A)
    : Is0Bifunctor (cat_comp (a:=a) (b:=b) (c:=c))
    := Build_Is0Bifunctor'' _ .

(** Any type is a 1-category with n-morphisms given by paths. *)
Global Instance is1cat_paths {A : Type} : Is1Cat A.
Proof.
  snrapply Build_Is1Cat.
  - exact _.
  - exact _.
  - exact _.
  - exact _.
  - exact (@concat_p_pp A).
  - exact (@concat_pp_p A).
  - exact (@concat_p1 A).
  - exact (@concat_1p A).
Defined.

Instance IsTruncatedBicat_paths (A: Type) : IsTruncatedBicat A.
Proof.
  snrapply Build_IsTruncatedBicat.
  - exact _.
  - intros a b c. simpl. change concatR with (cat_comp (a:=a) (b:=b) (c:=c)).
    rapply is0bifunctor_cat_comp_paths.
  - intros a b c d; apply concat_p_pp.
  - intros a b c d; apply concat_pp_p.
  - intros a b f; apply concat_p1.
  - intros a b f; symmetry; apply concat_p1.
  - intros a b f; apply concat_1p.
  - intros a b f; symmetry; apply concat_1p.
Defined.

(** Any type is a 1-groupoid with morphisms given by paths. *)
Global Instance is1gpd_paths {A : Type} : Is1Gpd A.
Proof.
  snrapply Build_Is1Gpd.
  - exact (@concat_pV A).
  - exact (@concat_Vp A).
Defined.

Instance Is1Bifunctor_cat_comp_paths (A: Type) (a b c : A)
  : Is1Bifunctor (cat_comp (a:=a) (b:=b) (c:=c)).
Proof.
  apply Build_Is1Bifunctor''.
  - intro q. snrapply Build_Is1Functor.
    + intros ? ? ? ?. exact( (ap (fun x => whiskerR x _))).
    + reflexivity.
    + intros p0 p1 p2. apply whiskerR_pp.
  - intro p. snrapply Build_Is1Functor.
    + intros ? ? ? ?. exact (ap (whiskerL p)).
    + reflexivity.
    + intros p0 p1 p2. exact (whiskerL_pp p).
  - intros q q' beta p p' alpha. exact (concat_whisker _ _ _ _ _ _)^.
Defined.

(** Any type is a 2-category with higher morphisms given by paths. *)
Instance is21cat_paths {A : Type} : Is21Cat A.
Proof.
  snrapply Build_Is21Cat; [snrapply Build_IsBicategory | | ].
  1-3, 12-13: exact _.
  - (* assoc and assoc_opp are inverse *)
    intros a b c d f g h. constructor; simpl; destruct h, g, f; reflexivity.
  - (* idl and idl_opp are inverse *)
    intros a b f; constructor; destruct f; reflexivity.
  - (* idr and idr_opp are inverse *)
    intros a b f; constructor; destruct f; reflexivity.
  - (* assoc is natural *)
    intros a b c d.
    snrapply Build_Is1Natural.
    intros ((h, g), f) ((h', g'), f') ((s,r),q). simpl in s, r, q. simpl.
    destruct q, s, h, r, g, f; reflexivity.
  - (* idl is natural *)
    intros a b; snrapply Build_Is1Natural.
    intros f f' alpha; destruct alpha, f; reflexivity.
  - (* idr is natural *)
    intros a b; snrapply Build_Is1Natural.
    intros f f' alpha; destruct alpha, f; reflexivity.
  - (* Pentagon *)
    intros a b c d e p q r s.
    symmetry.
    lhs nrapply concat_p_pp.
    apply pentagon.
  - (* Triangle *)
    intros a b c p q.
    exact (triangulator p q).
Defined.
