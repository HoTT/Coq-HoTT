From HoTT.Basics Require Import Equivalences Overture Tactics.
From HoTT.WildCat Require Import Core Equiv EquivGpd NatTrans
  Yoneda ZeroGroupoid Induced Opposite Equalizers.

(** * Categories with coequalizers *)

(** When [cat_coeq] is the target object in a double arrow diagram, then for any object [z] we get a commuting diagram of 0-groupoids by applying the functor [- $-> z], which is [yon_0gpd z].  Thus there is a natural map of 0-groupoids from [cat_coeq $-> z] to the 0-groupoid equalizer of

<<
                  -->
        (b $-> z)     (a $-> z)
                  -->
>>
In this diagram, the hom sets are regarded as 0-groupoids and the top-level arrows are morphisms of 0-groupoids (0-functors).*)

Definition cat_coeq_rec_inv {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  (cat_coeq : A) (proj : b $-> cat_coeq) (glue : proj $o f $== proj $o g)
  (z : A)
  : yon_0gpd z cat_coeq $-> equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
  := cat_eq_corec_inv (A:=A^op) (a:=b) f g cat_coeq proj glue z.

(** A coequalizer is an object completing [f] and [g] to a commuting diagram such that the map above is an equivalence of 0-groupoids for each [z]. We record this as the object being an equalizer in the opposite category and deduce the relevant structure. *)
Class IsCatCoequalizer {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b) (cat_coeq : A)
  := iscatcoequalizer :: IsCatEqualizer (A:=A^op) (a:=b) f g cat_coeq.

Definition Build_IsCatCoequalizer' {A : Type} `{Is1Cat A} {a b : A}
  (f g : a $-> b) (cat_coeq : A) (cat_coeq_proj : b $-> cat_coeq)
  (cat_coeq_glue : cat_coeq_proj $o f $== cat_coeq_proj $o g)
  (catie_cat_coeq_rec_inv : forall z : A, CatIsEquiv (cat_coeq_rec_inv f g cat_coeq cat_coeq_proj cat_coeq_glue z))
  : IsCatCoequalizer f g cat_coeq
  := Build_IsCatEqualizer' (A:=A^op) (a:=b) f g cat_coeq cat_coeq_proj cat_coeq_glue catie_cat_coeq_rec_inv.

Definition cat_coeq_proj {A : Type} `{Is1Cat A} {a b : A} {f g : a $-> b}
  {cat_coeq : A} `{!IsCatCoequalizer f g cat_coeq}
  : b $-> cat_coeq
  := cat_eq_inj (A:=A^op) (a:=b) (f:=f) (g:=g) (cat_eq:=cat_coeq).

Definition cat_coeq_glue {A : Type} `{Is1Cat A} {a b : A} {f g : a $-> b}
  {cat_coeq : A} `{!IsCatCoequalizer f g cat_coeq}
  : cat_coeq_proj $o f $== cat_coeq_proj $o g
  := cat_eq_glue (A:=A^op) (a:=b) (f:=f) (g:=g) (cat_eq:=cat_coeq).

Instance catie_cat_coeq_rec_inv {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
  (cat_coeq : A) `{!IsCatCoequalizer f g cat_coeq}
  : forall z : A, CatIsEquiv (cat_coeq_rec_inv f g cat_coeq cat_coeq_proj cat_coeq_glue z)
  := catie_cat_eq_corec_inv (A:=A^op) (a:=b) (f:=f) (g:=g) (cat_eq:=cat_coeq).

(** A coequalizer in a category is an equalizer in the opposite category. *)
Class CatCoequalizer {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
  := cat_coequalizer : CatEqualizer (A:=A^op) (a:=b) f g.

Definition cat_coeq {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b) `{!CatCoequalizer f g} : A
  := cat_coequalizer.(cat_eq (A:=A^op) (a:=b) f g).

Arguments cat_coeq {A _ _ _ _ _ _} f g {cat_coequalizer} : rename.

(** We derive that a coequalizer is also a coequalizer in the sense above. *)
Instance cat_iscoeq {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b) `{!CatCoequalizer f g}
  : IsCatCoequalizer f g (cat_coeq f g)
  := cat_coequalizer.(cat_iseq).

Arguments cat_iscoeq {A _ _ _ _ _ _} f g {cat_coequalizer} : rename.

(** A wrapper for building coequalizers with less typechecking. *)
Definition Build_CatCoequalizer' {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
  (cat_coeq : A) (cat_iscoeq : IsCatCoequalizer f g cat_coeq)
  : CatCoequalizer f g
  := Build_CatEqualizer' (A:=A^op) (a:=b) f g cat_coeq cat_iscoeq.

Section CoequalizerConstructors.

  Context {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
    (cat_coeq : A) (cat_coeq_proj : b $-> cat_coeq)
    (cat_coeq_glue : cat_coeq_proj $o f $== cat_coeq_proj $o g)
    (cat_coeq_rec : forall (z : A) (h : b $-> z) (p : h $o f $== h $o g),
      cat_coeq $-> z)
    (cat_coeq_beta_proj : forall z h p, cat_coeq_rec z h p $o cat_coeq_proj $== h)
    (cat_coeq_eta : forall z (k h : cat_coeq $-> z)
      (p : k $o cat_coeq_proj $== h $o cat_coeq_proj), k $== h).

  (** A convenience wrapper for building [IsCatCoequalizer]. *)
  Definition Build_IsCatCoequalizer : IsCatCoequalizer f g cat_coeq
    := Build_IsCatEqualizer (A:=A^op) (a:=b) f g cat_coeq cat_coeq_proj cat_coeq_glue
        cat_coeq_rec cat_coeq_beta_proj cat_coeq_eta.

  (** A convenience wrapper for building coequalizers. *)
  Definition Build_CatCoequalizer : CatCoequalizer f g
    := Build_CatCoequalizer' f g cat_coeq Build_IsCatCoequalizer.

End CoequalizerConstructors.

Section Lemmata.

  Context {A : Type} `{Is1Cat A}
    {a b : A} {f g : a $-> b}
    {cat_coeq : A}
    `{!IsCatCoequalizer f g cat_coeq}
    {z : A}.

  Definition cate_coeq_rec_inv
    : yon_0gpd z cat_coeq $<~>
        equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
    := cate_eq_corec_inv (A:=A^op) (a:=b).

  Definition cate_coeq_rec
    : equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g)
      $<~> yon_0gpd z cat_coeq
    := cate_eq_corec (A:=A^op) (a:=b).

  Definition cat_coeq_rec
    (h : b $-> z) (p : h $o f $== h $o g)
    : cat_coeq $-> z
    := cat_eq_corec (A:=A^op) (a:=b) (f:=f) (g:=g) h p.

  Definition cat_coeq_rec_beta_proj
    (h : b $-> z) (p : h $o f $== h $o g)
    : cat_coeq_rec h p $o cat_coeq_proj $== h
    := cat_eq_corec_beta_inj (A:=A^op) (a:=b) (f:=f) (g:=g) h p.

  Definition cat_coeq_proj_precomp_glue (h : cat_coeq $-> z)
    : (h $o cat_coeq_proj) $o f $== (h $o cat_coeq_proj) $o g
    := cat_eq_inj_postcomp_glue (A:=A^op) (a:=b) (f:=f) (g:=g) h.

  Definition cat_coeq_rec_eta_proj (h : cat_coeq $-> z)
    : cat_coeq_rec (h $o cat_coeq_proj) (cat_coeq_proj_precomp_glue h) $== h
    := cat_eq_corec_eta_inj (A:=A^op) (a:=b) (f:=f) (g:=g) h.

  Definition cat_coeq_rec_eta (h h' : b $-> z)
    (glue_h : h $o f $== h $o g) (glue_h' : h' $o f $== h' $o g)
    (p : h $== h')
    : cat_coeq_rec h glue_h $== cat_coeq_rec h' glue_h'
    := cat_eq_corec_eta (A:=A^op) (a:=b) (f:=f) (g:=g) h h' glue_h glue_h' p.

End Lemmata.

Local Instance is0functor_coequalizer_0gpd_helper {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  : Is0Functor (A:=A)
    (fun z : A => equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := is0functor_equalizer_0gpd_helper (A:=A^op) (a:=b) f g.

Local Instance is1functor_coequalizer_0gpd_helper {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  : Is1Functor (A:=A)
    (fun z : A => equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := is1functor_equalizer_0gpd_helper (A:=A^op) (a:=b) f g.

Definition natequiv_cat_coeq_rec_inv {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b) (cat_coeq : A) `{!IsCatCoequalizer f g cat_coeq}
  : NatEquiv (A:=A) (opyon_0gpd cat_coeq)
    (fun z : A => equalizer_0gpd ((is0functor_yon_0gpd z).(fmap _) f) ((is0functor_yon_0gpd z).(fmap _) g))
  := natequiv_cat_eq_corec_inv (A:=A^op) (a:=b) f g cat_coeq.

(** ** Uniqueness of coequalizers *)

Definition cat_coeq_unique {A : Type} `{HasEquivs A}
  {a b : A} (f g : a $-> b)
  (coeq1 : A) `{!IsCatCoequalizer f g coeq1}
  (coeq2 : A) `{!IsCatCoequalizer f g coeq2}
  : coeq1 $<~> coeq2
  := cat_eq_unique (A:=A^op) (a:=b) f g coeq2 coeq1.

(** ** Induced Coequalizers *)

Section InducedFromEquiv.

  Context {A : Type} `{HasEquivs A} {a b : A} {f g : a $-> b}
    (cat_coeq : A) `{!IsCatCoequalizer f g cat_coeq}
    (y : A) (h : cat_coeq $<~> y).

  (** A categorical equivalence out of a coequalizer induces a coequalizer structure on the codomain. *)
  Local Instance cat_coeq_coeq_equiv : IsCatCoequalizer f g y
    := cat_eq_equiv_eq (A:=A^op) (a:=b) (f:=f) (g:=g) cat_coeq y h.

  (** The induced projection is given by the equivalence. *)
  Definition cat_coeq_proj_comp
    : cat_coeq_proj $== h $o cat_coeq_proj
    := cat_eq_inj_comp (A:=A^op) (a:=b) (f:=f) (g:=g) cat_coeq y h.

  (** The induced recursion is given by the equivalence. *)
  Definition cat_coeq_rec_comp {z : A} (k : b $-> z) (p : k $o f $== k $o g)
    : cat_coeq_rec (cat_coeq:=y) k p $o h $== cat_coeq_rec k p
    := cat_eq_corec_comp (A:=A^op) (he:=hasequivs_op) (a:=b) (f:=f) (g:=g) cat_coeq y h k p.

End InducedFromEquiv.

(** ** Symmetry *)

(** A coequalizer of [f] and [g] is also a coequalizer of [g] and [f]. *)
Definition iscatcoequalizer_sym {A : Type} `{Is1Cat A}
  {a b : A} {f g : a $-> b}
  (cat_coeq : A) `{!IsCatCoequalizer f g cat_coeq}
  : IsCatCoequalizer g f cat_coeq
  := iscatequalizer_sym (A:=A^op) (a:=b) (f:=f) (g:=g) cat_coeq.

(** ** Categories with coequalizers *)

Class HasCoequalizers (A : Type) `{Is1Cat A}
  := has_coequalizers :: forall {a b} (f g : a $-> b), CatCoequalizer f g.

(** * Epis *)

(** The coequalizer map is an epimorphism. *)

#[export] Instance epic_cat_coequalizer {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b) {cat_coeq : A} `{!IsCatCoequalizer f g cat_coeq}
  : Epic cat_coeq_proj
  := monic_cat_equalizer (A:=A^op) (a:=b) f g.

(** Coequalizers define a subclass of strong epimorphisms, namely epis which have the left lifting property against monics. *)

Class StrongEpic {A : Type} `{Is1Cat A} {a b : A} (e : a $-> b)
  := isstrongepic :: StrongMonic (A:=A^op) (a:=b) e.

Instance isepic_strongepic {A : Type} `{Is1Cat A} {a b : A} (e : a $-> b) `{!StrongEpic e}
  : Epic e
  := ismonic_strongmonic (A:=A^op) (a:=b) (m:=e).

Definition llp_strongepic {A : Type} `{Is1Cat A} {a b : A} {e : a $-> b} `{!StrongEpic e}
  {a' b' : A} {m : a' $>-> b'} {u : a $-> a'} {v : b $-> b'}
  (sq : m $o u $== v $o e) : b $-> a'
  := rlp_strongmonic (A:=A^op) (a:=b) (m:=e) (a':=b') (b':=a') sq.

Definition llp_ucomm_strongepic {A : Type} `{Is1Cat A} {a b : A} {e : a $-> b} `{!StrongEpic e}
  {a' b' : A} {m : a' $>-> b'} {u : a $-> a'} {v : b $-> b'}
  (sq : m $o u $== v $o e) : llp_strongepic sq $o e $== u
  := rlp_lcomm_strongmonic (A:=A^op) (a:=b) (m:=e) (a':=b') (b':=a') sq.

Definition llp_lcomm_strongepic {A : Type} `{Is1Cat A} {a b : A} (e : a $-> b) `{!StrongEpic e}
  {a' b' : A} {m : a' $>-> b'} {u : a $-> a'} {v : b $-> b'} (sq : m $o u $== v $o e)
  : m $o llp_strongepic sq $== v
  := rlp_ucomm_strongmonic (A:=A^op) (a:=b) (m:=e) (a':=b') (b':=a') sq.

Definition llp_unique_strongepic {A : Type} `{Is1Cat A} {a b : A} (e : a $-> b) `{!StrongEpic e}
  {a' b' : A} {m : a' $>-> b'} {u : a $-> a'} {v : b $-> b'} (sq : m $o u $== v $o e)
  {h : b $-> a'} (utr : h $o e $== u)
  : llp_strongepic sq $== h
  := rlp_unique_strongmonic (A:=A^op) (a:=b) (m:=e) (a':=b') (b':=a') sq utr.

(** The map [cat_coeq_proj] is a strong epic. *)
#[export] Instance strongepic_coequalizer {A : Type} `{Is1Cat A} {c a : A}
  (f g : c $-> a) {cat_coeq : A} `{!IsCatCoequalizer f g cat_coeq}
  : StrongEpic cat_coeq_proj
  := strongmonic_equalizer (A:=A^op) (b:=a) f g.
