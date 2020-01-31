Require Import Basics.
Require Import WildCat.Core.

(** ** Natural transformations *)

Definition Transformation {A B : Type} `{IsGraph B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

(** A 1-natural transformation is natural up to a 2-cell, so its domain must be a 1-category. *)
Class Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
      (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
      (alpha : F $=> G) :=
{
  isnat : forall a a' (f : a $-> a'),
     (alpha a') $o (fmap F f) $== (fmap G f) $o (alpha a);
}.

Arguments isnat {_ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

(** The transposed natural square *)
Definition isnat_tr {A B : Type} `{IsGraph A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      (alpha : F $=> G) `{!Is1Natural F G alpha}
      {a a' : A} (f : a $-> a')
  : (fmap G f) $o (alpha a) $== (alpha a') $o (fmap F f)
  := (isnat alpha f)^$.

Definition id_transformation {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F
  := fun a => Id (F a).

Global Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (id_transformation F).
Proof.
  apply Build_Is1Natural; intros a b f; cbn.
  refine (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition comp_transformation {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K
  := fun a => gamma a $o alpha a.

Global Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
       {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
       (gamma : G $=> K) `{!Is1Natural G K gamma}
       (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (comp_transformation gamma alpha).
Proof.
  apply Build_Is1Natural; intros a b f; unfold comp_transformation; cbn.
  refine (cat_assoc _ _ _ $@ (_ $@L isnat alpha f) $@ _).
  refine (cat_assoc_opp _ _ _ $@ (isnat gamma f $@R _) $@ _).
  apply cat_assoc.
Defined.

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is01Cat A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      {alpha : F $=> G} (gamma : F $=> G) `{!Is1Natural F G gamma}
      (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  constructor; intros a b f.
  exact ((p b $@R _) $@ isnat gamma f $@ (_ $@L (p a)^$)).
Defined.
