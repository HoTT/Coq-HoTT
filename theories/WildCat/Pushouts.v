Require Import Basics.Equivalences Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd.
Require Import WildCat.Yoneda WildCat.ZeroGroupoid.
Require Import WildCat.Induced WildCat.Opposite WildCat.NatTrans WildCat.FunctorCat.
Require Import WildCat.Pullbacks.

(** * Categories with pushouts *)

(** When [po] is the target object in a commuting square, then for any object [z] we get a commuting square of 0-groupoids by applying the functor [- $-> z], which is [yon_0gpd z].  Thus there is a natural map of 0-groupoids from [po $-> z] to the 0-groupoid pullback of
<<
        (c $-> z) --> (a $-> z)
            |             |
            |             |
            v             v
        (b $-> z) -> (po $-> z)
>>
In this diagram, the hom sets are regarded as 0-groupoids and the top-level arrows are morphisms of 0-groupoids (0-functors). *)

Definition cat_po_rec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> b) (g : a $-> c)
  (po : A) (in1 : b $-> po) (in2 : c $-> po) (glue : in1 $o f $== in2 $o g)
  (z : A)
  : yon_0gpd z po $-> pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
  := cat_pb_corec_inv (A:=A^op) (a:=b) (b:=c) (c:=a) f g po in1 in2 glue z.

(** A pushout is an object completing [f] and [g] to a commuting square such that the map above is an equivalence of 0-groupoids for each [z]. We record this as the object being a pullback in the opposite category and deduce the relevant structure. *)
Class IsCatPushout {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c) (cat_po : A)
  := iscatpushout :: IsCatPullback (A:=A^op) (a:=b) (b:=c) (c:=a) f g cat_po.

Definition cat_po_in1 {A : Type} `{Is1Cat A} {a b c : A} {f : a $-> b} {g : a $-> c}
  {cat_po : A} `{!IsCatPushout f g cat_po}
  : b $-> cat_po
  := cat_pb_pr1 (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) (cat_pb:=cat_po).

Definition cat_po_in2 {A : Type} `{Is1Cat A} {a b c : A} {f : a $-> b} {g : a $-> c}
  {cat_po : A} `{!IsCatPushout f g cat_po}
  : c $-> cat_po
  := cat_pb_pr2 (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) (cat_pb:=cat_po).

Definition cat_po_glue {A : Type} `{Is1Cat A} {a b c : A} {f : a $-> b} {g : a $-> c}
  {cat_po : A} `{!IsCatPushout f g cat_po}
  : cat_po_in1 $o f $== cat_po_in2 $o g
  := cat_pb_glue (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) (cat_pb:=cat_po).

Instance catie_cat_po_rec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> b) (g : a $-> c)
  (cat_po : A) `{!IsCatPushout f g cat_po}
  : forall z : A, CatIsEquiv (cat_po_rec_inv f g cat_po cat_po_in1 cat_po_in2 cat_po_glue z)
  := catie_cat_pb_corec_inv (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) (cat_pb:=cat_po).

Definition Build_IsCatPushout' {A : Type} `{Is1Cat A} {a b c : A}
  (f : a $-> b) (g : a $-> c) (cat_po : A)
  (cat_po_in1 : b $-> cat_po) (cat_po_in2 : c $-> cat_po)
  (cat_po_glue : cat_po_in1 $o f $== cat_po_in2 $o g)
  (eq : forall z : A, CatIsEquiv (cat_po_rec_inv f g cat_po cat_po_in1 cat_po_in2 cat_po_glue z))
  : IsCatPushout f g cat_po
  := Build_IsCatPullback' (A:=A^op) (a:=b) (b:=c) (c:=a)
       f g cat_po cat_po_in1 cat_po_in2 cat_po_glue eq.

Class CatPushout {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c)
  := po : CatPullback (A:=A^op) (a:=b) (b:=c) (c:=a) f g.

Definition cat_po {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c)
  `{!CatPushout f g} : A
  := po.(cat_pb (A:=A^op) (a:=b) (b:=c) (c:=a) f g).

Arguments cat_po {A IsGraph Is2Graph Is01Cat H a b c} f g {po} : rename.

Instance cat_ispo {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c)
  `{!CatPushout f g}
  : IsCatPushout f g (cat_po f g)
  := po.(cat_ispb).

Arguments cat_ispo {A IsGraph Is2Graph Is01Cat H a b c} f g {po} : rename.

Definition Build_CatPushout' {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c)
  (cat_po : A) (cat_ispo : IsCatPushout f g cat_po)
  : CatPushout f g
  := Build_CatPullback' (A:=A^op) (a:=b) (b:=c) (c:=a) f g cat_po cat_ispo.

Arguments Build_CatPushout' {A IsGraph Is2Graph Is01Cat H a b c}
  f g : rename.

Section PushoutConstructors.

  Context {A : Type} `{Is1Cat A} {a b c : A} (f : a $-> b) (g : a $-> c)
    (cat_po : A) (cat_po_in1 : b $-> cat_po) (cat_po_in2 : c $-> cat_po)
    (cat_po_glue : cat_po_in1 $o f $== cat_po_in2 $o g)
    (cat_po_rec : forall (z : A) (h : b $-> z) (k : c $-> z)
      (sq : h $o f $== k $o g), (cat_po $-> z))
    (cat_po_beta_in1 : forall z h k p, cat_po_rec z h k p $o cat_po_in1 $== h)
    (cat_po_beta_in2 : forall z h k p, cat_po_rec z h k p $o cat_po_in2 $== k)
    (cat_po_eta : forall z (k h : cat_po $-> z)
      (p1 : k $o cat_po_in1 $== h $o cat_po_in1)
      (p2 : k $o cat_po_in2 $== h $o cat_po_in2), k $== h).

  (** A convenience wrapper for building [IsCatPushout]. *)
  Definition Build_IsCatPushout : IsCatPushout f g cat_po
    := Build_IsCatPullback (A:=A^op) (a:=b) (b:=c) (c:=a) f g cat_po
        cat_po_in1 cat_po_in2 cat_po_glue
        cat_po_rec cat_po_beta_in1 cat_po_beta_in2 cat_po_eta.

  (** A convenience wrapper for building pushouts. *)
  Definition Build_CatPushout : CatPushout f g
    := Build_CatPushout' f g cat_po Build_IsCatPushout.

End PushoutConstructors.

Section Lemmata.

  Context {A : Type} `{Is1Cat A}
    {a b c : A} (f : a $-> b) (g : a $-> c)
    {cat_po : A}
    `{!IsCatPushout f g cat_po}
    (z : A).

  Definition cate_po_rec_inv
    : yon_0gpd z cat_po $<~>
        pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
    := cate_pb_corec_inv (A:=A^op) (a:=b) (b:=c) (c:=a) f g z.

  Definition cate_po_rec
    : pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
      $<~> yon_0gpd z cat_po
    := cate_pb_corec (A:=A^op) (a:=b) (b:=c) (c:=a) f g z.

  Definition cat_po_rec
    (h : b $-> z) (k : c $-> z) (p : h $o f $== k $o g)
    : cat_po $-> z
    := cat_pb_corec (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h k p.

  Definition cat_po_rec_beta_in1
    (h : b $-> z) (k : c $-> z) (p : h $o f $== k $o g)
    : cat_po_rec h k p $o cat_po_in1 $== h
    := cat_pb_corec_beta_pr1 (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h k p.

  Definition cat_po_rec_beta_in2
    (h : b $-> z) (k : c $-> z) (p : h $o f $== k $o g)
    : cat_po_rec h k p $o cat_po_in2 $== k
    := cat_pb_corec_beta_pr2 (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h k p.

  Definition cat_po_precomp_glue (h : cat_po $-> z)
    : (h $o cat_po_in1) $o f $== (h $o cat_po_in2) $o g
    := cat_pb_postcomp_glue (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h.

  Definition cat_po_rec_eta_in (h : cat_po $-> z)
    : cat_po_rec (h $o cat_po_in1) (h $o cat_po_in2) (cat_po_precomp_glue h) $== h
    := cat_pb_corec_eta_pr (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h.

  Definition cat_po_rec_eta (h h' : b $-> z) (k k' : c $-> z)
    (glue_hk : h $o f $== k $o g) (glue_h'k' : h' $o f $== k' $o g)
    (p1 : h $== h') (p2 : k $== k')
    : cat_po_rec h k glue_hk $== cat_po_rec h' k' glue_h'k'
    := cat_pb_corec_eta (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h h' k k' glue_hk glue_h'k' p1 p2.

  Definition cat_po_in_eta (h h' : cat_po $-> z)
    (p1 : h $o cat_po_in1 $== h' $o cat_po_in1)
    (p2 : h $o cat_po_in2 $== h' $o cat_po_in2)
    : h $== h'
    := cat_pb_pr_eta (A:=A^op) (a:=b) (b:=c) (c:=a) f g z h h' p1 p2.

End Lemmata.

Local Instance is0functor_pushout_0gpd_helper {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> b) (g : a $-> c)
  : Is0Functor (A:=A)
    (fun z : A => pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := is0functor_pullback_0gpd_helper (A:=A^op) (a:=b) (b:=c) (c:=a) f g.

Local Instance is1functor_pushout_0gpd_helper {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> b) (g : a $-> c)
  : Is1Functor (A:=A)
    (fun z : A => pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := is1functor_pullback_0gpd_helper (A:=A^op) (a:=b) (b:=c) (c:=a) f g.

Definition natequiv_cat_po_rec_inv {A : Type} `{Is1Cat A}
  {a b c : A} (f : a $-> b) (g : a $-> c) (cat_po : A) `{!IsCatPushout f g cat_po}
  : NatEquiv (A:=A) (opyon_0gpd cat_po)
    (fun z : A => pullback_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := natequiv_cat_pb_corec_inv (A:=A^op) (a:=b) (b:=c) (c:=a) f g cat_po.

(** ** Uniqueness of pushouts *)

Definition cat_po_unique {A : Type} `{HasEquivs A}
  {a b c : A} (f : a $-> b) (g : a $-> c)
  (po1 : A) `{!IsCatPushout f g po1}
  (po2 : A) `{!IsCatPushout f g po2}
  : po1 $<~> po2
  := cat_pb_unique (A:=A^op) (a:=b) (b:=c) (c:=a) f g po2 po1.

(** ** Induced pushouts *)

Section InducedFromEquiv.

  Context {A : Type} `{HasEquivs A} {a b c : A} {f : a $-> b} {g : a $-> c}
    (cat_po : A) `{!IsCatPushout f g cat_po}
    (y : A) (h : cat_po $<~> y).

  (** A categorical equivalence out of a pushout induces a pushout structure on the codomain. *)
  Local Instance cat_po_equiv_po : IsCatPushout f g y
    := cat_pb_equiv_pb (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) cat_po y h.

  (** The induced first inclusion is given by the equivalence. *)
  Definition cat_po_in1_comp
    : cat_po_in1 (cat_po:=y) $== h $o cat_po_in1
    := cat_pb_pr1_comp (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) cat_po y h.

  (** The induced second inclusion is given by the equivalence. *)
  Definition cat_po_in2_comp
    : cat_po_in2 (cat_po:=y) $== h $o cat_po_in2
    := cat_pb_pr2_comp (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) cat_po y h.

  (** The induced recursion is given by the equivalence. *)
  Definition cat_po_rec_comp {z : A} (k1 : b $-> z) (k2 : c $-> z) (p : k1 $o f $== k2 $o g)
    : cat_po_rec (cat_po:=y) f g z k1 k2 p $o h $== cat_po_rec f g z k1 k2 p
    := cat_pb_corec_comp (A:=A^op) (he:=hasequivs_op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) cat_po y h k1 k2 p.

End InducedFromEquiv.

(** ** Symmetry of pushouts *)

Definition iscatpushout_sym {A : Type} `{Is1Cat A}
  {a b c : A} {f : a $-> b} {g : a $-> c}
  (cat_po : A) `{!IsCatPushout f g cat_po}
  : IsCatPushout g f cat_po
  := iscatpullback_sym (A:=A^op) (a:=b) (b:=c) (c:=a) (f:=f) (g:=g) cat_po.

(** ** Categories with pushouts *)

Class HasPushouts (A : Type) `{Is1Cat A}
  := has_pushouts :: forall {a b c} (f : a $-> b) (g : a $-> c), CatPushout f g.

Local Instance haspullbacks_haspushouts_op {A : Type} `{HasPushouts A}
  : HasPullbacks A^op
  := fun b c a f g => has_pushouts (A:=A) (a:=a) (b:=b) (c:=c) f g.

(** ** Pushouts in induced wild categories *)

Section Induced.

  (** If the 1-category structure on [A] is induced from that on [B] along a map [F], the pushout of [F f] and [F g] exists in [B], and that pushout object is in the image of [F] up to categorical equivalence, then the preimage is also a pushout.  Typically this will be applied with [h] being an identity equivalence (or [reflexivity]), but it would be awkward to state this lemma assuming that. *)
  Instance cat_po_induced {A B} `{Is1Cat B} `{!HasEquivs B}
    (F : A -> B)
    {a b c : A} (f : F a $-> F b) (g : F a $-> F c)
    {cat_po_b : B} `{!IsCatPushout f g cat_po_b}
    (cat_po_a : A) (h : cat_po_b $<~> F cat_po_a)
    : CatPushout (A:=A) (H:=is1cat_induced F) f g
    := cat_pb_induced (A:=A^op) (B:=B^op) (a:=b) (b:=c) (c:=a) F f g cat_po_a h.

  Instance haspushouts_induced {A B} `{HasPushouts B} `{!HasEquivs B}
    (F : A -> B)
    (K : forall (a b c : A) (f : F a $-> F b) (g : F a $-> F c), exists q, cat_po f g $<~> F q)
    : HasPushouts A (H:=is1cat_induced F)
    := fun a b c f g =>
         haspullbacks_induced (A:=A^op) (B:=B^op) F
           (fun b c a f g => K a b c f g) b c a f g.

End Induced.
