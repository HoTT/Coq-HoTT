Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd.

(** * The wild 1-category of 0-groupoids. *)

(** Here we define a wild 1-category structure on the type of 0-groupoids.  We think of the 1-cells [g $== h] in a 0-groupoid [G] as a substitute for the paths [g = h], and so we closely follow the definitions used for the 1-category of types with [=] replaced by [$==].  In fact, the 1-category structure on types should be the pullback of the 1-category structure on 0-groupoids along a natural map [Type -> ZeroGpd] which sends [A] to [A] equipped with its path types.  A second motivating example is the 0-groupoid with underlying type [A -> B] and homotopies as the 1-cells.  The definitions chosen here exactly make the Yoneda lemma [opyon_equiv_0gpd] go through. *)

Record ZeroGpd := {
  carrier :> Type;
  isgraph_carrier : IsGraph carrier;
  is01cat_carrier : Is01Cat carrier;
  is0gpd_carrier : Is0Gpd carrier;  
}.

Global Existing Instance isgraph_carrier.
Global Existing Instance is01cat_carrier.
Global Existing Instance is0gpd_carrier.

(* The morphisms of 0-groupoids are the 0-functors.  This is the same as [Fun01], but we put a different graph and 01-category structure on it, so we give this a custom name. *)
Record Morphism_0Gpd (G H : ZeroGpd) := {
  fun_0gpd :> carrier G -> carrier H;
  is0functor_fun_0gpd : Is0Functor fun_0gpd;
}.

Global Existing Instance is0functor_fun_0gpd.

(** Now we show that the type [ZeroGpd] of 0-groupoids is itself a 1-category, with morphisms the 0-functors. *)
Global Instance isgraph_0gpd : IsGraph ZeroGpd.
Proof.
  apply Build_IsGraph.
  exact Morphism_0Gpd.
Defined.

Global Instance is01cat_0gpd : Is01Cat ZeroGpd.
Proof.
  srapply Build_Is01Cat.
  - intro G.
    exact (Build_Morphism_0Gpd G G idmap _).
  - intros G H K f g.
    exact (Build_Morphism_0Gpd _ _ (f o g) _).
Defined.

(* The 2-cells are unnatural transformations, and are analogous to homotopies. *)
Global Instance is2graph_0gpd : Is2Graph ZeroGpd.
Proof.
  intros G H.
  snrapply Build_IsGraph.
  intros f g.
  exact (forall x : G, f x $== g x).
Defined.

Global Instance is1cat_0gpd : Is1Cat ZeroGpd.
Proof.
  snrapply Build_Is1Cat.
  - intros G H.
    srapply Build_Is01Cat.
    + intro f. exact (fun x => Id (f x)).
    + intros f g h p q. exact (fun x => q x $@ p x).
  - intros G H.
    srapply Build_Is0Gpd.
    intros f g p. exact (fun x => (p x)^$).
  - intros G H K f.
    srapply Build_Is0Functor.
    intros g h p x.
    cbn.
    exact (fmap f (p x)).
  - intros G H K f.
    srapply Build_Is0Functor.
    intros g h p x.
    cbn.
    exact (p (f x)).
  - reflexivity. (* Associativity. *)
  - reflexivity. (* Left identity. *)
  - reflexivity. (* Right identity. *)
Defined.

(** We define equivalences of 0-groupoids.  The definition is chosen to provide what is needed for the Yoneda lemma, and to match the concept for types, with paths replaced by 1-cells.  We are able to match the biinvertible definition.  The half-adjoint definition doesn't work, as we can't prove adjointification.  We would need to be in a 1-groupoid for that to be possible.  We could also use the "wrong" definition, without the eisadj condition, and things would go through, but it wouldn't match the definition for types. *)
Class IsEquiv_0Gpd {G H : ZeroGpd} (f : G $-> H) := {
  equiv_inv_0gpd : H $-> G;
  eisretr_0gpd : f $o equiv_inv_0gpd $== Id H;
  equiv_inv_0gpd' : H $-> G;
  eissect_0gpd' : equiv_inv_0gpd' $o f $== Id G;
}.

Arguments equiv_inv_0gpd {G H}%type_scope f {_}.
Arguments eisretr_0gpd {G H}%type_scope f {_} _.
Arguments equiv_inv_0gpd' {G H}%type_scope f {_}.
Arguments eissect_0gpd' {G H}%type_scope f {_} _.

Record Equiv_0Gpd (G H : ZeroGpd) := {
  equiv_fun_0gpd :> Morphism_0Gpd G H;
  equiv_isequiv_0gpd : IsEquiv_0Gpd equiv_fun_0gpd;
}.

Global Existing Instance equiv_isequiv_0gpd.

(** The two inverses are necessarily homotopic. *)
Definition inverses_homotopic_0gpd {G H : ZeroGpd} (f : G $-> H) `{IsEquiv_0Gpd _ _ f}
  : equiv_inv_0gpd f $== equiv_inv_0gpd' f.
Proof.
  set (g := equiv_inv_0gpd f).
  set (g' := equiv_inv_0gpd' f).
  intro x.
  refine ((eissect_0gpd' f (g x))^$ $@ _); cbn.
  refine (fmap g' _).
  rapply eisretr_0gpd.
Defined.

(** Therefore we can prove [eissect] for the first inverse as well. *)
Definition eissect_0gpd {G H : ZeroGpd} (f : G $-> H) `{IsEquiv_0Gpd _ _ f}
  : equiv_inv_0gpd f $o f $== Id G
  := (inverses_homotopic_0gpd f $@R f) $@ eissect_0gpd' f.

Global Instance hasequivs_0gpd : HasEquivs ZeroGpd.
Proof.
  srapply Build_HasEquivs; intros G H.
  1: exact (Equiv_0Gpd G H).
  all:intros f; cbn beta in *.
  - exact (IsEquiv_0Gpd f).
  - exact f.
  - exact _.
  - apply Build_Equiv_0Gpd.
  - intros; reflexivity.
  - exact (equiv_inv_0gpd f).
  - apply eissect_0gpd.
  - apply eisretr_0gpd.
  - intros g r s.
    exact (Build_IsEquiv_0Gpd _ _ f g r g s).
Defined.

(** * We now give a different characterization of the equivalences of 0-groupoids, as the injective split essentially surjective 0-functors which are defined in EquivGpd. *)

(** Advantages of this logically equivalent formulation are that it tends to be easier to prove in examples and in some cases it is definitionally equal to [ExtensionAlong], which is convenient.  See Homotopy/Suspension.v and Algebra/AbGroups/Abelianization for examples. Advantages of the bi-invertible definition are that it reproduces a definition that is equivalent to [IsEquiv] when applied to types, assuming [Funext].  It also makes the proof of [HasEquivs] above easy. *)

(** Every equivalence is injective and essentially surjective. *)
Definition IsEquiv0Gpd_Equiv_0Gpd {G H : ZeroGpd} (f : G $<~> H)
  : IsEquiv0Gpd f.
Proof.
  econstructor.
  - intro y.
    exists (f^-1$ y).
    rapply eisretr_0gpd.
  - intros x1 x2 m.
    exact ((eissect_0gpd f x1)^$ $@ fmap f^-1$ m $@ eissect_0gpd f x2).
Defined.

(** Conversely, every injective essentially surjective 0-functor is an equivalence. *)
Global Instance IsEquiv_0Gpd_IsEquiv0Gpd {G H : ZeroGpd} (F : G $-> H)
  {e : IsEquiv0Gpd F}
  : IsEquiv_0Gpd F.
Proof.
  destruct e as [e0 e1]; unfold SplEssSurj in e0.
  srapply catie_adjointify.
  - snrapply Build_Morphism_0Gpd.
    1: exact (fun y => (e0 y).1).
    snrapply Build_Is0Functor; cbn beta.
    intros y1 y2 m.
    apply e1.
    exact ((e0 y1).2 $@ m $@ ((e0 y2).2)^$).
  - cbn.  apply e0.
  - cbn.  intro x.
    apply e1.
    apply e0.
Defined.
