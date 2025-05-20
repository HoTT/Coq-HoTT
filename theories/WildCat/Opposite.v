Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.

(** ** Opposite categories *)

Definition op (A : Type) := A.
Notation "A ^op" := (op A).

(** This stops typeclass search from trying to unfold op. *)
#[global] Typeclasses Opaque op.

Definition isgraph_op {A : Type} `{IsGraph A}
  : IsGraph A^op.
Proof.
  apply Build_IsGraph.
  unfold op; exact (fun a b => b $-> a).
Defined.

(** If [isgraph_op] is made an instance, typeclass search can loop if the typeclass goal is [IsGraph ?A] with [?A] unknown.  So we make it an immediate hint instead.  Since the later instances below all depend on [IsGraph A], this should also prevent most loops involving those instances. *)
Hint Immediate isgraph_op : typeclass_instances.

Instance is01cat_op {A : Type} `{Is01Cat A} : Is01Cat A^op.
Proof.
  apply Build_Is01Cat.
  + cbv; exact Id.
  + cbv; exact (fun a b c g f => f $o g).
Defined.

(** We don't invert 2-cells as this is op on the first level. *)
Instance is2graph_op {A : Type} `{Is2Graph A} : Is2Graph A^op.
Proof.
  intros a b; unfold op in *; cbn; exact _.
Defined.

Instance is1cat_op {A : Type} `{Is1Cat A} : Is1Cat A^op.
Proof.
  snapply Build_Is1Cat; unfold op in *; cbv in *.
  - intros a b.
    apply is01cat_hom.
  - intros a b.
    apply is0gpd_hom.
  - intros a b c h.
    srapply Build_Is0Functor.
    intros f g p.
    cbn in *.
    exact (p $@R h).
  - intros a b c h.
    srapply Build_Is0Functor.
    intros f g p.
    cbn in *.
    exact (h $@L p).
  - intros a b c d f g h; exact (cat_assoc_opp h g f).
  - intros a b c d f g h; exact (cat_assoc h g f).
  - intros a b f; exact (cat_idr f).
  - intros a b f; exact (cat_idl f).
Defined.

Instance is1cat_strong_op A `{Is1Cat_Strong A}
  : Is1Cat_Strong (A ^op).
Proof.
  snapply Build_Is1Cat_Strong.
  1-4: exact _.
  all: cbn.
  - intros a b c d f g h; exact (cat_assoc_opp_strong h g f).
  - intros a b c d f g h; exact (cat_assoc_strong h g f).
  - intros a b f.
    apply cat_idr_strong.
  - intros a b f.
    apply cat_idl_strong.
Defined.

(** Opposite groupoids *)

Instance is0gpd_op A `{Is0Gpd A} : Is0Gpd (A^op).
Proof.
  srapply Build_Is0Gpd; unfold op in *; cbn in *.
  intros a b.
  exact gpd_rev.
Defined.

Instance op0gpd_fun A `{Is0Gpd A} :
  Is0Functor( (fun x => x) : A^op -> A).
Proof.
  srapply Build_Is0Functor; unfold op in *; cbn.
  intros a b.
  exact (fun f => f^$).
Defined.

(** ** Opposite functors *)

Instance is0functor_op A B (F : A -> B)
  `{IsGraph A, IsGraph B, x : !Is0Functor F}
  : Is0Functor (F : A^op -> B^op).
Proof.
  apply Build_Is0Functor.
  intros a b; cbn.
  apply fmap.
  assumption.
Defined.

Instance is1functor_op A B (F : A -> B)
  `{Is1Cat A, Is1Cat B, !Is0Functor F, !Is1Functor F}
  : Is1Functor (F : A^op -> B^op).
Proof.
  apply Build_Is1Functor; cbn.
  - intros a b; rapply fmap2.
  - exact (fmap_id F).
  - intros a b c f g; exact (fmap_comp F g f).
Defined.

(** Since [Is01Cat] structures are definitionally involutive (see test/WildCat/Opposite.v), we can use [is0functor_op] to transform in the reverse direction as well.  This result makes that much easier to use in practice. *)
Instance is0functor_op' A B (F : A^op -> B^op)
  `{IsGraph A, IsGraph B, Fop : !Is0Functor (F : A^op -> B^op)}
  : Is0Functor (F : A -> B)
  := is0functor_op A^op B^op F.

(** [Is1Cat] structures are also definitionally involutive. *)
Instance is1functor_op' A B (F : A^op -> B^op)
  `{Is1Cat A, Is1Cat B, !Is0Functor (F : A^op -> B^op), Fop2 : !Is1Functor (F : A^op -> B^op)}
  : Is1Functor (F : A -> B)
  := is1functor_op A^op B^op F.

Instance hasmorext_op {A : Type} `{H0 : HasMorExt A}
  : HasMorExt A^op.
Proof.
  intros a b f g.
  exact (@isequiv_Htpy_path _ _ _ _ _ H0 b a f g).
Defined.

Instance isinitial_op_isterminal {A : Type} `{Is1Cat A} (x : A)
  {t : IsTerminal x} : IsInitial (A := A^op) x
  := t.

Instance isterminal_op_isinitial {A : Type} `{Is1Cat A} (x : A)
  {i : IsInitial x} : IsTerminal (A := A^op) x
  := i.
