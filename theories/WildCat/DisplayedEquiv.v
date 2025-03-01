Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.Equivalences.
Require Import Types.Sigma.
Require Import WildCat.Core.
Require Import WildCat.Displayed.
Require Import WildCat.Equiv.

(** Equivalences in displayed wild categories *)
Class DHasEquivs {A : Type} `{HasEquivs A}
  (D : A -> Type) `{!IsDGraph D, !IsD2Graph D, !IsD01Cat D, !IsD1Cat D} :=
{
  DCatEquiv : forall {a b}, (a $<~> b) -> D a -> D b -> Type;
  DCatIsEquiv : forall {a b} {f : a $-> b} {fe : CatIsEquiv f} {a'} {b'},
    DHom f a' b' -> Type;
  dcate_fun : forall {a b} {f : a $<~> b} {a'} {b'},
    DCatEquiv f a' b' -> DHom f a' b';
  dcate_isequiv : forall {a b} {f : a $<~> b} {a'} {b'}
    (f' : DCatEquiv f a' b'), DCatIsEquiv (dcate_fun f');
  dcate_buildequiv : forall {a b} {f : a $-> b} `{!CatIsEquiv f} {a'} {b'}
    (f' : DHom f a' b') {fe' : DCatIsEquiv f'},
    DCatEquiv (Build_CatEquiv f) a' b';
  dcate_buildequiv_fun : forall {a b} {f : a $-> b} `{!CatIsEquiv f}
    {a'} {b'} (f' : DHom f a' b') {fe' : DCatIsEquiv f'},
    DGpdHom (cate_buildequiv_fun f)
    (dcate_fun (dcate_buildequiv f' (fe':=fe'))) f';
  dcate_inv' : forall {a b} {f : a $<~> b} {a'} {b'} (f' : DCatEquiv f a' b'),
    DHom (cate_inv' _ _ f) b' a';
  dcate_issect' : forall {a b} {f : a $<~> b} {a'} {b'} (f' : DCatEquiv f a' b'),
    DGpdHom (cate_issect' _ _ f) (dcate_inv' f' $o' dcate_fun f') (DId a');
  dcate_isretr' : forall {a b} {f : a $<~> b} {a'} {b'} (f' : DCatEquiv f a' b'),
    DGpdHom (cate_isretr' _ _ f) (dcate_fun f' $o' dcate_inv' f') (DId b');
  dcatie_adjointify : forall {a b} {f : a $-> b} {g : b $-> a}
    {r : f $o g $== Id b} {s : g $o f $== Id a} {a'} {b'} (f' : DHom f a' b')
    (g' : DHom g b' a') (r' : DGpdHom r (f' $o' g') (DId b'))
    (s' : DGpdHom s (g' $o' f') (DId a')),
    @DCatIsEquiv _ _ _ (catie_adjointify f g r s) _ _ f';
}.

(** Being an equivalence is a typeclass. *)
Existing Class DCatIsEquiv.
Global Existing Instance dcate_isequiv.

Coercion dcate_fun : DCatEquiv >-> DHom.

Definition Build_DCatEquiv {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $-> b} `{!CatIsEquiv f} {a' : D a} {b' : D b}
  (f' : DHom f a' b') {fe' : DCatIsEquiv f'}
  : DCatEquiv (Build_CatEquiv f) a' b'
  := dcate_buildequiv f' (fe':=fe').

(** Construct [DCatEquiv] via adjointify. *)
Definition dcate_adjointify {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $-> b} {g : b $-> a}
  {r : f $o g $== Id b} {s : g $o f $== Id a} {a'} {b'}
  (f' : DHom f a' b') (g' : DHom g b' a') (r' : DHom r (f' $o' g') (DId b'))
  (s' : DHom s (g' $o' f') (DId a'))
  : DCatEquiv (cate_adjointify f g r s) a' b'
  := Build_DCatEquiv f' (fe':=dcatie_adjointify f' g' r' s').

(** Construct the entire inverse equivalence *)
Definition dcate_inv {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {a' : D a} {b' : D b} (f' : DCatEquiv f a' b')
  : DCatEquiv (f^-1$) b' a'.
Proof.
  snrapply dcate_adjointify.
  - exact (dcate_inv' f').
  - exact f'.
  - exact (dcate_issect' f').
  - exact (dcate_isretr' f').
Defined.

Notation "f ^-1$'" := (dcate_inv f).

(** Witness that [f'] is a section of [dcate_inv f'] in addition to [dcate_inv' f']. *)
Definition dcate_issect {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {a' : D a} {b' : D b} (f' : DCatEquiv f a' b')
  : DGpdHom (cate_issect f) (dcate_fun f'^-1$' $o' f') (DId a').
Proof.
  refine (_ $@' dcate_issect' f').
  refine (_ $@R' (dcate_fun f')).
  apply dcate_buildequiv_fun.
Defined.

(** Witness that [f'] is a retraction of [dcate_inv f'] in addition to [dcate_inv' f']. *)
Definition dcate_isretr {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {a' : D a} {b' : D b} (f' : DCatEquiv f a' b')
  : DGpdHom (cate_isretr f) (dcate_fun f' $o' f'^-1$') (DId b').
Proof.
  refine (_ $@' dcate_isretr' f').
  refine (dcate_fun f' $@L' _).
  apply dcate_buildequiv_fun.
Defined.

(** If [g'] is a section of an equivalence, then it is the inverse. *)
Definition dcate_inverse_sect {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {g : b $-> a} {p : f $o g $== Id b}
  {a' : D a} {b' : D b} (f' : DCatEquiv f a' b') (g' : DHom g b' a')
  (p' : DGpdHom p (dcate_fun f' $o' g') (DId b'))
  : DGpdHom (cate_inverse_sect f g p) (dcate_fun f'^-1$') g'.
Proof.
  refine ((dcat_idr _)^$' $@' _).
  refine ((_ $@L' p'^$') $@' _).
  1: exact isd0gpd_hom.
  refine (dcat_assoc_opp _ _ _ $@' _).
  refine (dcate_issect f' $@R' _ $@' _).
  apply dcat_idl.
Defined.

(** If [g'] is a retraction of an equivalence, then it is the inverse. *)
Definition dcate_inverse_retr {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {g : b $-> a} {p : g $o f $== Id a}
  {a' : D a} {b' : D b} (f' : DCatEquiv f a' b') (g' : DHom g b' a')
  (p' : DGpdHom p (g' $o' f') (DId a'))
  : DGpdHom (cate_inverse_retr f g p) (dcate_fun f'^-1$') g'.
Proof.
  refine ((dcat_idl _)^$' $@' _).
  refine ((p'^$' $@R' _) $@' _).
  1: exact isd0gpd_hom.
  refine (dcat_assoc _ _ _ $@' _).
  refine (_ $@L' dcate_isretr f' $@' _).
  apply dcat_idr.
Defined.

(** It follows that the inverse of the equivalence you get by adjointification is homotopic to the inverse [g'] provided. *)
Definition dcate_inv_adjointify {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $-> b} {g : b $-> a} {r : f $o g $== Id b}
  {s : g $o f $== Id a} {a' : D a} {b' : D b} (f' : DHom f a' b')
  (g' : DHom g b' a') (r' : DGpdHom r (f' $o' g') (DId b'))
  (s' : DGpdHom s (g' $o' f') (DId a'))
  : DGpdHom (cate_inv_adjointify f g r s)
    (dcate_fun (dcate_adjointify f' g' r' s')^-1$') g'.
Proof.
  apply dcate_inverse_sect.
  exact ((dcate_buildequiv_fun f' $@R' _) $@' r').
Defined.

(** If the base category has equivalences and the displayed category has displayed equivalences, then the total category has equivalences. *)
Global Instance hasequivs_total {A} (D : A -> Type) `{DHasEquivs A D}
  : HasEquivs (sig D).
Proof.
  snrapply Build_HasEquivs.
  1:{ intros [a a'] [b b']. exact {f : a $<~> b & DCatEquiv f a' b'}. }
  all: intros aa' bb' [f f'].
  - exact {fe : CatIsEquiv f & DCatIsEquiv f'}.
  - exists f. exact f'.
  - exact (cate_isequiv f; dcate_isequiv f').
  - intros [fe fe'].
    exact (Build_CatEquiv f (fe:=fe); Build_DCatEquiv f' (fe':=fe')).
  - intros ?; exists (cate_buildequiv_fun f).
    exact (dcate_buildequiv_fun f').
  - exists (f^-1$). exact (f'^-1$').
  - exact (cate_issect f; dcate_issect f').
  - exact (cate_isretr f; dcate_isretr f').
  - intros [g g'] [r r'] [s s'].
    exact (catie_adjointify f g r s; dcatie_adjointify f' g' r' s').
Defined.

(** The identity morphism is an equivalence *)
Global Instance dcatie_id {A} {D : A -> Type} `{DHasEquivs A D}
  {a : A} (a' : D a)
  : DCatIsEquiv (DId a')
  := dcatie_adjointify (DId a') (DId a') (dcat_idl (DId a')) (dcat_idr (DId a')).

Definition did_cate {A} {D : A -> Type} `{DHasEquivs A D}
  {a : A} (a' : D a)
  : DCatEquiv (id_cate a) a' a'
  := Build_DCatEquiv (DId a').

Global Instance reflexive_dcate {A} {D : A -> Type} `{DHasEquivs A D} {a : A}
  : Reflexive (DCatEquiv (id_cate a))
  := did_cate.

(** Anything homotopic to an equivalence is an equivalence. This should not be an instance. *)
Definition dcatie_homotopic {A} {D : A -> Type} `{DHasEquivs A D} {a b : A}
  {f : a $-> b} `{!CatIsEquiv f} {g : a $-> b} {p : f $== g} {a' : D a}
  {b' : D b} (f' : DHom f a' b') `{fe' : !DCatIsEquiv f'} {g' : DHom g a' b'}
  (p' : DGpdHom p f' g')
  : DCatIsEquiv (fe:=catie_homotopic f p) g'.
Proof.
  snrapply dcatie_adjointify.
  - exact (Build_DCatEquiv (fe':=fe') f')^-1$'.
  - refine (p'^$' $@R' _ $@' _).
    1: exact isd0gpd_hom.
    refine ((dcate_buildequiv_fun f')^$' $@R' _ $@' _).
    1: exact isd0gpd_hom.
    apply dcate_isretr.
  - refine (_ $@L' p'^$' $@' _).
    1: exact isd0gpd_hom.
    refine (_ $@L' (dcate_buildequiv_fun f')^$' $@' _).
    1: exact isd0gpd_hom.
    apply dcate_issect.
Defined.

(** Equivalences can be composed. *)
Global Instance dcompose_catie {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {g : b $<~> c} {f : a $<~> b} {a' : D a} {b' : D b} {c' : D c}
  (g' : DCatEquiv g b' c') (f' : DCatEquiv f a' b')
  : DCatIsEquiv (dcate_fun g' $o' f').
Proof.
  snrapply dcatie_adjointify.
  - exact (dcate_fun f'^-1$' $o' g'^-1$').
  - refine (dcat_assoc _ _ _ $@' _).
    refine (_ $@L' dcat_assoc_opp _ _ _ $@' _).
    refine (_ $@L' (dcate_isretr _ $@R' _) $@' _).
    refine (_ $@L' dcat_idl _ $@' _).
    apply dcate_isretr.
  - refine (dcat_assoc_opp _ _ _ $@' _).
    refine (dcat_assoc _ _ _ $@R' _ $@' _).
    refine (((_ $@L' dcate_issect _) $@R' _) $@' _).
    refine ((dcat_idr _ $@R' _) $@' _).
    apply dcate_issect.
Defined.

Global Instance dcompose_catie' {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {g : b $-> c} `{!CatIsEquiv g} {f : a $-> b} `{!CatIsEquiv f}
  {a' : D a} {b' : D b} {c' : D c}
  (g' : DHom g b' c') `{ge' : !DCatIsEquiv g'}
  (f' : DHom f a' b') `{fe' : !DCatIsEquiv f'}
  : DCatIsEquiv (fe:=compose_catie' g f) (g' $o' f').
Proof.
  pose (ff:=Build_DCatEquiv (fe':=fe') f').
  pose (gg:=Build_DCatEquiv (fe':=ge') g').
  nrefine (dcatie_homotopic (fe':=dcompose_catie gg ff) _ _).
  exact (dcate_buildequiv_fun _ $@@' dcate_buildequiv_fun _).
Defined.

Definition dcompose_cate {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {g : b $<~> c} {f : a $<~> b} {a' : D a} {b' : D b} {c' : D c}
  (g' : DCatEquiv g b' c') (f' : DCatEquiv f a' b')
  : DCatEquiv (compose_cate g f) a' c'
  := Build_DCatEquiv (dcate_fun g' $o' f').

Notation "g $oE' f" := (dcompose_cate g f).

(** Composing equivalences commutes with composing the underlying maps. *)
Definition dcompose_cate_fun {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {g : b $<~> c} {f : a $<~> b} {a' : D a} {b' : D b} {c' : D c}
  (g' : DCatEquiv g b' c') (f' : DCatEquiv f a' b')
  : DGpdHom (compose_cate_fun g f)
    (dcate_fun (g' $oE' f')) (dcate_fun g' $o' f')
  := dcate_buildequiv_fun _.

Definition dcompose_cate_funinv {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {g : b $<~> c} {f : a $<~> b} {a' : D a} {b' : D b} {c' : D c}
  (g' : DCatEquiv g b' c') (f' : DCatEquiv f a' b')
  : DGpdHom (compose_cate_funinv g f)
    (dcate_fun g' $o' f') (dcate_fun (g' $oE' f')).
Proof.
  apply dgpd_rev.
  apply dcate_buildequiv_fun.
Defined.

(** The underlying map of the identity equivalence is homotopic to the identity. *)
Definition did_cate_fun {A} {D : A -> Type} `{DHasEquivs A D} {a : A} (a' : D a)
  : DGpdHom (id_cate_fun a) (dcate_fun (did_cate a')) (DId a')
  := dcate_buildequiv_fun _.

(** Composition of equivalences is associative. *)
Definition dcompose_cate_assoc {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c d : A} {f : a $<~> b} {g : b $<~> c} {h : c $<~> d} {a'} {b'} {c'} {d'}
  (f' : DCatEquiv f a' b') (g' : DCatEquiv g b' c') (h' : DCatEquiv h c' d')
  : DGpdHom (compose_cate_assoc f g h) (dcate_fun ((h' $oE' g') $oE' f'))
    (dcate_fun (h' $oE' (g' $oE' f'))).
Proof.
  refine (dcompose_cate_fun _ f' $@' _ $@' dcat_assoc (dcate_fun f') g' h'
          $@' _ $@' dcompose_cate_funinv h' _).
  - apply (dcompose_cate_fun h' g' $@R' _).
  - apply (_ $@L' dcompose_cate_funinv g' f').
Defined.

Definition dcompose_cate_idl {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b}  {a' : D a} {b' : D b} (f' : DCatEquiv f a' b')
  : DGpdHom (compose_cate_idl f) (dcate_fun (did_cate b' $oE' f'))
    (dcate_fun f').
Proof.
  refine (dcompose_cate_fun _ f' $@' _ $@' dcat_idl (dcate_fun f')).
  apply (dcate_buildequiv_fun _ $@R' _).
Defined.

Definition dcompose_cate_idr {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {f : a $<~> b} {a' : D a} {b' : D b} (f' : DCatEquiv f a' b')
  : DGpdHom (compose_cate_idr f) (dcate_fun (f' $oE' did_cate a'))
    (dcate_fun f').
Proof.
  refine (dcompose_cate_fun f' _ $@' _ $@' dcat_idr (dcate_fun f')).
  rapply (_ $@L' dcate_buildequiv_fun _).
Defined.

(** Some more convenient equalities for equivalences. The naming scheme is similar to [PathGroupoids.v].*)

Definition dcompose_V_hh {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {f : b $<~> c} {g : a $-> b} {a' : D a} {b' : D b} {c' : D c}
  (f' : DCatEquiv f b' c') (g' : DHom g a' b')
  : DGpdHom (compose_V_hh f g) (dcate_fun f'^-1$' $o' (dcate_fun f' $o' g')) g'
  := (dcat_assoc_opp _ _ _) $@' (dcate_issect f' $@R' g') $@' dcat_idl g'.

Definition dcompose_h_Vh {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {f : c $<~> b} {g : a $-> b} {a' : D a} {b' : D b} {c' : D c}
  (f' : DCatEquiv f c' b') (g' : DHom g a' b')
  : DGpdHom (compose_h_Vh f g) (dcate_fun f' $o' (dcate_fun f'^-1$' $o' g')) g'
  := (dcat_assoc_opp _ _ _) $@' (dcate_isretr f' $@R' g') $@' dcat_idl g'.

Definition dcompose_hh_V {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {f : b $-> c} {g : a $<~> b} {a' : D a} {b' : D b} {c' : D c}
  (f' : DHom f b' c') (g' : DCatEquiv g a' b')
  : DGpdHom (compose_hh_V f g) ((f' $o' g') $o' g'^-1$') f'
  := dcat_assoc _ _ _ $@' (f' $@L' dcate_isretr g') $@' dcat_idr f'.

Definition dcompose_hV_h {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {f : b $-> c} {g : b $<~> a} {a' : D a} {b' : D b} {c' : D c}
  (f' : DHom f b' c') (g' : DCatEquiv g b' a')
  : DGpdHom (compose_hV_h f g) ((f' $o' g'^-1$') $o' g') f'
  := dcat_assoc _ _ _ $@' (f' $@L' dcate_issect g') $@' dcat_idr f'.

(** Equivalences are both monomorphisms and epimorphisms (but not the converse). *)

Definition dcate_monic_equiv {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {a' : D a} {b' : D b} (e' : DCatEquiv e a' b')
  : DMonic (mon:=cate_monic_equiv e) (dcate_fun e').
Proof.
  intros c f g p c' f' g' p'.
  refine ((dcompose_V_hh e' _)^$' $@' _ $@' dcompose_V_hh e' _).
  1: exact isd0gpd_hom.
  exact (_ $@L' p').
Defined.

Definition dcate_epic_equiv {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {a' : D a} {b' : D b} (e' : DCatEquiv e a' b')
  : DEpic (epi:=cate_epic_equiv e) (dcate_fun e').
Proof.
  intros c f g p c' f' g' p'.
  refine ((dcompose_hh_V _ e')^$' $@' _ $@' dcompose_hh_V _ e').
  1: exact isd0gpd_hom.
  exact (p' $@R' _).
Defined.

(** Some lemmas for moving equivalences around.  Naming based on EquivGroupoids.v. *)

Definition dcate_moveR_eM {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {e : b $<~> a} {f : a $-> c} {g : b $-> c}
  {p : f $== g $o e^-1$} {a' : D a} {b' : D b} {c' : D c}
  (e' : DCatEquiv e b' a') (f' : DHom f a' c') (g' : DHom g b' c')
  (p' : DGpdHom p f' (g' $o' e'^-1$'))
  : DGpdHom (cate_moveR_eM e f g p) (f' $o' e') g'.
Proof.
  apply (dcate_epic_equiv e'^-1$').
  exact (dcompose_hh_V _ _ $@' p').
Defined.

Definition dcate_moveR_Ve {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {e : b $<~> c} {f : a $-> c} {g : a $-> b}
  {p : f $== e $o g} {a' : D a} {b' : D b} {c' : D c}
  (e' : DCatEquiv e b' c') (f' : DHom f a' c') (g' : DHom g a' b')
  (p' : DGpdHom p f' (dcate_fun e' $o' g'))
  : DGpdHom (cate_moveR_Ve e f g p) (dcate_fun e'^-1$' $o' f') g'.
Proof.
  apply (dcate_monic_equiv e').
  exact (dcompose_h_Vh _ _ $@' p').
Defined.

Definition dcate_moveL_V1 {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {f : b $-> a} {p : e $o f $== Id b}
  {a' : D a} {b' : D b} {e' : DCatEquiv e a' b'}
  (f' : DHom f b' a') (p' : DGpdHom p (dcate_fun e' $o' f') (DId b'))
  : DGpdHom (cate_moveL_V1 f p) f' (dcate_fun e'^-1$').
Proof.
  apply (dcate_monic_equiv e').
  nrapply (p' $@' (dcate_isretr e')^$').
  exact isd0gpd_hom.
Defined.

Definition dcate_moveL_1V {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {f : b $-> a} {p : f $o e $== Id a}
  {a' : D a} {b' : D b} {e' : DCatEquiv e a' b'}
  (f' : DHom f b' a') (p' : DGpdHom p (f' $o' e') (DId a'))
  : DGpdHom (cate_moveL_1V f p) f' (dcate_fun e'^-1$').
Proof.
  apply (dcate_epic_equiv e').
  nrapply (p' $@' (dcate_issect e')^$').
  exact isd0gpd_hom.
Defined.

Definition dcate_moveR_V1 {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {f : b $-> a} {p : Id b $== e $o f}
  {a' : D a} {b' : D b} {e' : DCatEquiv e a' b'}
  (f' : DHom f b' a') (p' : DGpdHom p (DId b') (dcate_fun e' $o' f'))
  : DGpdHom (cate_moveR_V1 f p) (dcate_fun e'^-1$') f'.
Proof.
  apply (dcate_monic_equiv e').
  exact (dcate_isretr e' $@' p').
Defined.

Definition dcate_moveR_1V {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {f : b $-> a} {p : Id a $== f $o e}
  {a' : D a} {b' : D b} {e' : DCatEquiv e a' b'}
  (f' : DHom f b' a') (p' : DGpdHom p (DId a') (f' $o' e'))
  : DGpdHom (cate_moveR_1V f p) (dcate_fun e'^-1$') f'.
Proof.
  apply (dcate_epic_equiv e').
  exact (dcate_issect e' $@' p').
Defined.

(** Lemmas about the underlying map of an equivalence. *)

Definition dcate_inv2 {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e f : a $<~> b} {p : cate_fun e $== cate_fun f}
  {a' : D a} {b' : D b} {e' : DCatEquiv e a' b'} {f' : DCatEquiv f a' b'}
  (p' : DGpdHom p (dcate_fun e') (dcate_fun f'))
  : DGpdHom (cate_inv2 p) (dcate_fun e'^-1$') (dcate_fun f'^-1$').
Proof.
  apply dcate_moveL_V1.
  rapply ((p'^$' $@R' _) $@' dcate_isretr _).
  2: exact isd0gpd_hom.
Defined.

Definition dcate_inv_compose {A} {D : A -> Type} `{DHasEquivs A D}
  {a b c : A} {e : a $<~> b} {f : b $<~> c} {a' : D a} {b' : D b} {c' : D c}
  (e' : DCatEquiv e a' b') (f' : DCatEquiv f b' c')
  : DGpdHom (cate_inv_compose e f)
    (dcate_fun (f' $oE' e')^-1$') (dcate_fun (e'^-1$' $oE' f'^-1$')).
Proof.
  refine (_ $@' (dcompose_cate_fun e'^-1$' f'^-1$')^$').
  - snrapply dcate_inv_adjointify.
  - exact isd0gpd_hom.
Defined.

Definition dcate_inv_V {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} {e : a $<~> b} {a' : D a} {b' : D b}
  (e' : DCatEquiv e a' b')
  : DGpdHom (cate_inv_V e) (dcate_fun (e'^-1$')^-1$') (dcate_fun e').
Proof.
  apply dcate_moveR_V1.
  apply dgpd_rev.
  apply dcate_issect.
Defined.

(** Any sufficiently coherent displayed functor preserves displayed equivalences. *)
Global Instance diemap {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', !IsD1Functor F F'}
  {a b : A} {f : a $<~> b} {a' : DA a} {b' : DA b} (f' : DCatEquiv f a' b')
  : DCatIsEquiv (fe:=iemap F f) (dfmap F F' (dcate_fun f')).
Proof.
  refine (dcatie_adjointify
           (dfmap F F' (dcate_fun f')) (dfmap F F' (dcate_fun f'^-1$')) _ _).
  - refine ((dfmap_comp F F' (dcate_fun f'^-1$') f')^$' $@' _ $@' _).
    + exact (dfmap2 F F' (dcate_isretr _)).
    + exact (dfmap_id F F' _).
  - refine ((dfmap_comp F F' (dcate_fun f') f'^-1$')^$' $@' _ $@' _).
    + exact (dfmap2 F F' (dcate_issect _)).
    + exact (dfmap_id F F' _).
Defined.

Definition demap {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', !IsD1Functor F F'}
  {a b : A} {f : a $<~> b} {a' : DA a} {b' : DA b} (f' : DCatEquiv f a' b')
  : DCatEquiv (emap F f) (F' a a') (F' b b')
  := Build_DCatEquiv (dfmap F F' (dcate_fun f')).

Definition demap_id {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', !IsD1Functor F F'}
  {a : A} {a' : DA a}
  : DGpdHom (emap_id F)
    (dcate_fun (demap F F' (did_cate a'))) (dcate_fun (did_cate (F' a a'))).
Proof.
  refine (dcate_buildequiv_fun _ $@' _).
  refine (dfmap2 F F' (did_cate_fun a') $@' _ $@' _).
  - rapply dfmap_id.
  - apply dgpd_rev.
    exact (did_cate_fun (F' a a')).
Defined.

Definition demap_compose {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', isd1f : !IsD1Functor F F'}
  {a b c : A} {f : a $<~> b} {g : b $<~> c} {a' : DA a} {b' : DA b} {c' : DA c}
  (f' : DCatEquiv f a' b') (g' : DCatEquiv g b' c')
  : DGpdHom (emap_compose F f g) (dcate_fun (demap F F' (g' $oE' f')))
    (dfmap F F' (dcate_fun g') $o' dfmap F F' (dcate_fun f')).
Proof.
  refine (dcate_buildequiv_fun _ $@' _).
  refine (dfmap2 F F' (dcompose_cate_fun _ _) $@' _).
  nrapply dfmap_comp; exact isd1f.
Defined.

(** A variant. *)
Definition demap_compose' {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', !IsD1Functor F F'}
  {a b c : A} {f : a $<~> b} {g : b $<~> c} {a' : DA a} {b' : DA b} {c' : DA c}
  (f' : DCatEquiv f a' b') (g' : DCatEquiv g b' c')
  : DGpdHom (emap_compose' F f g) (dcate_fun (demap F F' (g' $oE' f')))
    (dcate_fun ((demap F F' g') $oE' (demap F F' f'))).
Proof.
  refine (demap_compose F F' f' g' $@' _).
  apply dgpd_rev.
  refine (dcompose_cate_fun _ _ $@' _).
  exact (dcate_buildequiv_fun _ $@@' dcate_buildequiv_fun _).
Defined.

Definition demap_inv {A B : Type}
  {DA : A -> Type} `{DHasEquivs A DA} {DB : B -> Type} `{DHasEquivs B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F', !IsD1Functor F F'}
  {a b : A} {e : a $<~> b} {a' : DA a} {b' : DA b} (e' : DCatEquiv e a' b')
  : DGpdHom (emap_inv F e)
    (dcate_fun (demap F F' e')^-1$') (dcate_fun (demap F F' e'^-1$')).
Proof.
  refine (dcate_inv_adjointify _ _ _ _ $@' _).
  apply dgpd_rev.
  exact (dcate_buildequiv_fun _).
Defined.

(** When we have equivalences, we can define what it means for a displayed category to be univalent. *)
Definition dcat_equiv_path {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} (p : a = b) (a' : D a) (b' : D b)
  : transport D p a' = b' -> DCatEquiv (cat_equiv_path a b p) a' b'.
Proof.
  intro p'. destruct p, p'. reflexivity.
Defined.

Class IsDUnivalent1Cat {A} (D : A -> Type) `{DHasEquivs A D} :=
{
  isequiv_dcat_equiv_path : forall {a b : A} (p : a = b) a' b',
    IsEquiv (dcat_equiv_path p a' b')
}.
Global Existing Instance isequiv_dcat_equiv_path.

Definition dcat_path_equiv {A} {D : A -> Type} `{IsDUnivalent1Cat A D}
  {a b : A} (p : a = b) (a' : D a) (b' : D b)
  : DCatEquiv (cat_equiv_path a b p) a' b' -> transport D p a' = b'
  := (dcat_equiv_path p a' b')^-1.

(** If [IsUnivalent1Cat A] and [IsDUnivalent1Cat D], then this is an equivalence by [isequiv_functor_sigma]. *)
Definition dcat_equiv_path_total {A} {D : A -> Type} `{DHasEquivs A D}
  {a b : A} (a' : D a) (b' : D b)
  : {p : a = b & p # a' = b'} -> {e : a $<~> b & DCatEquiv e a' b'}
  := functor_sigma (cat_equiv_path a b) (fun p => dcat_equiv_path p a' b').

(** If the base category and the displayed category are both univalent, then the total category is univalent. *)
Global Instance isunivalent1cat_total {A} `{IsUnivalent1Cat A} (D : A -> Type)
  `{!IsDGraph D, !IsD2Graph D, !IsD01Cat D, !IsD1Cat D, !DHasEquivs D}
  `{!IsDUnivalent1Cat D}
  : IsUnivalent1Cat (sig D).
Proof.
  snrapply Build_IsUnivalent1Cat.
  intros aa' bb'.
  apply (isequiv_homotopic
          (dcat_equiv_path_total _ _ o (path_sigma_uncurried D aa' bb')^-1)).
  intros []; reflexivity.
Defined.
