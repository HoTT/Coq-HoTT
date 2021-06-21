(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.NatTrans.

(** ** Opposite categories *)

Definition op (A : Type) : Type := A.
Notation "A ^op" := (op A).

(** This stops typeclass search from trying to unfold op. *)
Typeclasses Opaque op.

Section Op.

  Context (A : Type) `{Is1Cat A}.

  Global Instance isgraph_op : IsGraph A^op.
  Proof.
    apply Build_IsGraph.
    unfold op; exact (fun a b => b $-> a).
  Defined.

  Global Instance is01cat_op : Is01Cat A^op.
  Proof.
    apply Build_Is01Cat.
    + cbv; exact Id.
    + cbv; exact (fun a b c g f => f $o g).
  Defined.

  (** We don't invert 2-cells as this is op on the first level. *)
  Global Instance is2graph_op : Is2Graph A^op.
  Proof.
    intros a b; unfold op in *; cbn; exact _.
  Defined.

  Global Instance is1cat_op : Is1Cat A^op.
  Proof.
    srapply Build_Is1Cat; unfold op in *; cbv in *.
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
    - intros a b f; exact (cat_idr f).
    - intros a b f; exact (cat_idl f).
   Defined.

End Op.

Global Instance is1cat_strong_op A `{Is1Cat_Strong A}
  : Is1Cat_Strong (A ^op).
Proof.
  srapply Build_Is1Cat_Strong; unfold op in *; cbn in *.
  - intros a b c d f g h; exact (cat_assoc_opp_strong h g f).
  - intros a b f.
    apply cat_idr_strong.
  - intros a b f. 
    apply cat_idl_strong.
Defined.

(* Opposites are (almost) definitionally involutive. You can test this by uncommenting the stuff below. *)

(*
Definition test1 A `{Is01Cat A} : A = (A^op)^op := 1.
Definition test2 A `{x : Is01Cat A} : x = is01cat_op (A^op) := 1.
Definition test3 A `{x : Is2Graph A} : x = is2graph_op (A^op) := 1.
(** Doesn't work *)
Definition test4 A `{x : Is1Cat A} : x = is1cat_op (A^op) := 1.
*)

(** Opposite groupoids *)

Global Instance is0gpd_op A `{Is0Gpd A} : Is0Gpd (A ^op).
Proof.
  srapply Build_Is0Gpd; unfold op in *; cbn in *.
  intros a b.
  apply gpd_rev.
Defined.

Global Instance op0gpd_fun A `{Is0Gpd A} :
  Is0Functor( (fun x => x) : A^op -> A).
Proof.
  srapply Build_Is0Functor; unfold op in *; cbn.
  intros a b.
  exact (fun f => f^$).
Defined.

(** Mike thought co-duals were unnecessary, so I'm commenting this out.

Definition co (A : Type) : Type := A.
(** I wasn't able to make "A ^co" a notation. *)

(** This stops typeclass search from trying to unfold co. *)
Typeclasses Opaque co.

Global Instance is01cat_co A `{Is01Cat A} : Is01Cat (co A)
  := Build_Is01Cat A (fun a b => (a $-> b)^op) Id (fun a b c g f => g $o f).

Global Instance is1cat_co A `{Is1Cat A} : Is1Cat (co A).
Proof.
  srapply Build_Is1Cat; unfold co in *; cbn.
  - intros a b.
    apply is01cat_op.
    apply is01cat_hom.
  - intros a b.
    apply is0coh1gpd_op.
    apply is0gpd_hom.
  - intros a b c.
    srapply Build_Is0Coh1Functor.
    intros [f g] [h k] [p q].
    cbn in *.
    exact (p $o@ q).
Defined.
*)

(** Opposite functors *)

Global Instance is0functor_op  A `{Is01Cat A} B `{Is01Cat B}
       (F : A -> B) `{x : !Is0Functor F}
  : Is0Functor (F : A ^op -> B ^op).
Proof.
  apply Build_Is0Functor.
  unfold op.
  cbn.
  intros a b.
  apply fmap.
  assumption.
Defined.

Global Instance is1functor_op A B `{Is1Cat A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  : Is1Functor (F : A^op -> B^op).
Proof.
  apply Build_Is1Functor; unfold op in *; cbn in *.
  - intros a b; rapply fmap2; assumption.
  - intros a; exact (fmap_id F a).
  - intros a b c f g; exact (fmap_comp F g f).
Defined.

(** Opposite natural transformations *)

Definition transformation_op {A} {B} `{Is01Cat B}
           (F : A -> B) (G : A -> B) (alpha : F $=> G)
  : @Transformation A^op B^op _
                     (G : A^op -> B^op) (F : A^op -> B^op).
Proof.
  unfold op in *.
  cbn in *.
  intro a.
  apply (alpha a).
Defined.

Global Instance is1nat_op A B `{Is01Cat A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F}
       (G : A -> B) `{!Is0Functor G}
       (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural (G : A^op -> B^op) (F : A^op -> B^op) (transformation_op F G alpha).
Proof.
  unfold op in *.
  unfold transformation_op.
  cbn.
  intros a b f.
  srapply isnat_tr.
Defined.

(** Opposite categories preserve having equivalences. *)
Global Instance hasequivs_op {A} `{HasEquivs A} : HasEquivs A^op.
Proof.
  srapply Build_HasEquivs; intros a b; unfold op in *; cbn.
  - exact (b $<~> a).
  - apply CatIsEquiv.
  - apply cate_fun'.
  - apply cate_isequiv'.
  - apply cate_buildequiv'.
  - rapply cate_buildequiv_fun'.
  - apply cate_inv'.
  - rapply cate_isretr'.
  - rapply cate_issect'.
  - intros f g s t.
    exact (catie_adjointify f g t s).
Defined.

Global Instance isequivs_op {A : Type} `{HasEquivs A}
       {a b : A} (f : a $-> b) {ief : CatIsEquiv f}
  : @CatIsEquiv A^op _ _ _ _ _ b a f.
Proof.
  assumption.
Defined.

Global Instance hasmorext_op {A : Type} `{H0 : HasMorExt A}
  : HasMorExt A^op.
Proof.
  snrapply Build_HasMorExt.
  intros a b f g.
  refine (@isequiv_Htpy_path _ _ _ _ _ H0 b a f g).
Defined.

