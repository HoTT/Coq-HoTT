(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture Basics.PathGroupoids Basics.Notations Basics.Contractible Basics.Equivalences.
Local Open Scope path_scope.

(** * Wild categories, functors, and transformations *)

(** ** Unbundled definitions of categories *)

Class Is1Cat (A : Type) :=
  { Hom : A -> A -> Type where "a $-> b" := (Hom a b)
    ; Id : forall (a : A), a $-> a
    ; Comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c)
  }.

Notation "a $-> b" := (Hom a b).
Arguments Comp {A _ a b c} _ _.
Notation "g $o f" := (Comp g f).

Class Is2Cat (A : Type) `{Is1Cat A} :=
  { Htpy : forall (a b : A), (a $-> b) -> (a $-> b) -> Type where "f $== g" := (Htpy _ _ f g)
    ; Id_Htpy : forall a b (f : a $-> b), f $== f
    ; Opp_Htpy : forall a b (f g : a $-> b), (f $== g) -> (g $== f)
    ; Concat_Htpy : forall a b (f : a $-> b) (g : a $-> b) (h : a $-> b), (f $== g) -> (g $== h) -> (f $== h)
    ; WhiskerL_Htpy : forall a b c (f g : a $-> b) (h : b $-> c) (p : f $== g), (h $o f $== h $o g)
    ; WhiskerR_Htpy : forall a b c (f g : b $-> c) (p : f $== g) (h : a $-> b), (f $o h $== g $o h)
  }.

Arguments Htpy {_ _ _ _ _} _ _.
Notation "f $== g" := (Htpy f g).
Arguments Id_Htpy {_ _ _ _ _} f.
Arguments Concat_Htpy {_ _ _ _ _ _ _ _} p q.
Notation "p $@ q" := (Concat_Htpy p q).
Arguments WhiskerL_Htpy {_ _ _ _ _ _ _ _} h p.
Notation "h $@L p" := (WhiskerL_Htpy h p).
Arguments WhiskerR_Htpy {_ _ _ _ _ _ _ _} p h.
Notation "p $@R h" := (WhiskerR_Htpy p h).
Arguments Opp_Htpy {_ _ _ _ _ _ _} p.
Notation "p ^$" := (Opp_Htpy p).

Global Instance Reflexive_Htpy A `{Is2Cat A} (a b : A) : Reflexive (@Htpy A _ _ a b)
  := fun f => Id_Htpy f.

Global Instance Symmetric_Htpy A `{Is2Cat A} (a b : A) : Symmetric (@Htpy A _ _ a b)
  := fun f g p => p^$.

Global Instance Transitive_Htpy A `{Is2Cat A} (a b : A) : Transitive (@Htpy A _ _ a b)
  := fun f g h p q => p $@ q.

Definition Htpy_path {A} `{Is2Cat A} {a b : A} {f g : a $-> b} (p : f = g) : f $== g.
Proof.
  destruct p; apply Id_Htpy.
Defined.

Class Is1Cat1 (A : Type) `{Is2Cat A} :=
  Build_Is1Cat1'
  { cat_assoc : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), (h $o g) $o f $== h $o (g $o f)
    ; cat_assoc_opp : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), h $o (g $o f) $== (h $o g) $o f
    ; cat_idl : forall a b (f : a $-> b), Id b $o f $== f
    ; cat_idr : forall a b (f : a $-> b), f $o Id a $== f
    ; cat_idlr : forall a, Id a $o Id a $== Id a
  }.

Definition Build_Is1Cat1 (A : Type) `{Is2Cat A}
           (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), (h $o g) $o f $== h $o (g $o f))
           (cat_idl' : forall a b (f : a $-> b), Id b $o f $== f)
           (cat_idr' : forall a b (f : a $-> b), f $o Id a $== f)
  : Is1Cat1 A
  := Build_Is1Cat1' A _ _ cat_assoc' (fun a b c d f g h => (cat_assoc' a b c d f g h)^$) cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc [_ _ _ _ _ _ _ _] f g h.
Arguments cat_assoc_opp [_ _ _ _ _ _ _ _] f g h.
Arguments cat_idl [_ _ _ _ _ _] f.
Arguments cat_idr [_ _ _ _ _ _] f.

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Cat1_Strong (A : Type) `{Is2Cat A} :=
  Build_Is1Cat1_Strong'
  { cat_assoc_strong : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), (h $o g) $o f = h $o (g $o f)
    ; cat_assoc_opp_strong : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), h $o (g $o f) = (h $o g) $o f
    ; cat_idl_strong : forall a b (f : a $-> b), Id b $o f = f
    ; cat_idr_strong : forall a b (f : a $-> b), f $o Id a = f
    ; cat_idlr_strong : forall a, Id a $o Id a = Id a
  }.

Definition Build_Is1Cat1_Strong (A : Type) `{Is2Cat A}
           (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d), (h $o g) $o f = h $o (g $o f))
           (cat_idl' : forall a b (f : a $-> b), Id b $o f = f)
           (cat_idr' : forall a b (f : a $-> b), f $o Id a = f)
  : Is1Cat1_Strong A
  := Build_Is1Cat1_Strong' A _ _ cat_assoc' (fun a b c d f g h => (cat_assoc' a b c d f g h)^) cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc_strong [_ _ _ _ _ _ _ _] f g h.
Arguments cat_assoc_opp_strong [_ _ _ _ _ _ _ _] f g h.
Arguments cat_idl_strong [_ _ _ _ _ _] f.
Arguments cat_idr_strong [_ _ _ _ _ _] f.

Global Instance is1cat1_strong A `{Is1Cat1_Strong A} : Is1Cat1 A.
Proof.
  srapply Build_Is1Cat1'; intros; apply Htpy_path.
  - rapply cat_assoc_strong.
  - rapply cat_assoc_opp_strong.
  - rapply cat_idl_strong.
  - rapply cat_idr_strong.
  - rapply cat_idlr_strong.
Defined.


(** ** Unbundled definitions of functors *)

Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B} (F : A -> B) :=
  { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap [_ _ _ _] F [_ _ _] f.

(* We can't write `{Is1Functor A B F} since that would duplicate the instances of Is1Cat. *)
Class Is2Functor {A B : Type} `{Is2Cat A} `{Is2Cat B} (F : A -> B) {ff : Is1Functor F} :=
  { fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) }.

Arguments fmap2 [_ _ _ _ _ _] F [_ _ _ _ _ _] p.

Class Is1Functor1 {A B : Type} `{Is2Cat A} `{Is2Cat B} (F : A -> B) {ff : Is1Functor F} :=
  { fmap_id : forall a, fmap F (Id a) $== Id (F a)
    ; fmap_comp : forall a b c (f : a $-> b) (g : b $-> c), fmap F (g $o f) $== fmap F g $o fmap F f
  }.

Arguments fmap_id [_ _ _ _ _ _] F [_ _] a.
Arguments fmap_comp [_ _ _ _ _ _] F [_ _ _ _ _] f g.


(** ** Unbundled definitions of natural transformations *)

Definition Transformation {A B : Type} `{Is1Cat B} (F : A -> B) (G : A -> B)
  := forall (a:A), F a $-> G a.

Notation "F $--> G" := (Transformation F G).

Class Is1Natural {A B : Type} `{Is2Cat A} `{Is2Cat B}
      (F : A -> B) {ff1 : Is1Functor F} (G : A -> B) {fg1 : Is1Functor G}
      (alpha : F $--> G) := Build_Is1Natural'
  { isnat : forall a b (f : a $-> b), alpha b $o fmap F f $== fmap G f $o alpha a
  ; isnat_opp : forall a b (f : a $-> b), fmap G f $o alpha a $== alpha b $o fmap F f }.

Arguments isnat [_ _ _ _ _ _ _ _ _ _] alpha [alnat _ _] f : rename.

Definition Build_Is1Natural {A B : Type} `{Is2Cat A} `{Is2Cat B}
           (F : A -> B) {ff1 : Is1Functor F} (G : A -> B) {fg1 : Is1Functor G} (alpha : F $--> G)
           (isnat' : forall a b (f : a $-> b), alpha b $o fmap F f $== fmap G f $o alpha a)
  : Is1Natural F G alpha
  := Build_Is1Natural' _ _ _ _ _ _ F _ G _ alpha
                       isnat' (fun a b f => (isnat' a b f)^$).


(** ** Opposite categories *)

Definition op (A : Type) : Type := A.
Notation "A ^op" := (op A).
Typeclasses Opaque op.

Global Instance is1cat_op A `{Is1Cat A} : Is1Cat (A ^op)
  := Build_Is1Cat A (fun a b => b $-> a) Id (fun a b c g f => f $o g).

Global Instance is2cat_op A `{Is2Cat A} : Is2Cat (A ^op).
Proof.
  srapply Build_Is2Cat; unfold op in *; cbn in *.
  1:intros a b f g; exact (f $== g).
  all:cbn.
  - intros a b; apply Id_Htpy.
  - intros a b f g; apply Opp_Htpy.
  - intros a b f g h; apply Concat_Htpy.
  - intros a b c f g h p; exact (p $@R h).
  - intros a b c f g p h; exact (h $@L p).
Defined.

Global Instance is1cat1_op A `{Is1Cat1 A} : Is1Cat1 (A ^op).
Proof.
  srapply Build_Is1Cat1'; unfold op in *; cbn in *.
  - intros a b c d f g h; exact (cat_assoc_opp h g f).
  - intros a b c d f g h; exact (cat_assoc h g f).
  - intros a b f; exact (cat_idr f).
  - intros a b f; exact (cat_idl f).
  - intros a; exact (cat_idlr a).
Defined.

Global Instance is1cat1_strong_op A `{Is1Cat1_Strong A} : Is1Cat1_Strong (A ^op).
Proof.
  srapply Build_Is1Cat1_Strong'; unfold op in *; cbn in *.
  - intros a b c d f g h; exact (cat_assoc_opp_strong h g f).
  - intros a b c d f g h; exact (cat_assoc_strong h g f).
  - intros a b f; exact (cat_idr_strong f).
  - intros a b f; exact (cat_idl_strong f).
  - intros a; exact (cat_idlr_strong a).
Defined.

(* Opposites are definitionally involutive. *)
(*
Definition test1 A {ac : Is1Cat A} : A = (A^op)^op := 1.
Definition test2 A {ac : Is1Cat A} : ac = is1cat_op (A^op) := 1.
Definition test3 A {ac : Is1Cat A} {ac2 : Is2Cat A} : ac2 = is2cat_op (A^op) := 1.
Definition test4 A {ac : Is1Cat A} {ac2 : Is2Cat A} {ac11 : Is1Cat1 A} : ac11 = is1cat1_op (A^op) := 1.
*)

(* TODO: Opposite functors and natural transformations *)


(** ** Equivalences *)

(** We could define equivalences in any wild 2-category as bi-invertible maps, or in a wild 3-category as half-adjoint equivalences.  However, in concrete cases there is often an equivalent definition of equivalences that we want to use instead, and the important property we need is that it's logically equivalent to quasi-isomorphism. *)

Record CatIso {A : Type} `{Is2Cat A} {a b : A} :=
  { catiso_fun : a $-> b
    ; catiso_inv : b $-> a
    ; catiso_retr : catiso_fun $o catiso_inv $== Id b
    ; catiso_sect : catiso_inv $o catiso_fun $== Id a
  }.

Arguments CatIso [_ _ _] a b.

Definition issig_CatIso {A : Type} `{Is2Cat A} (a b : A)
  : _ <~> CatIso a b := ltac:(issig).

Class HasEquivs (A : Type) `{Is2Cat A} :=
  { cat_equiv : A -> A -> Type
    ; cat_unadjointify : forall a b, cat_equiv a b -> CatIso a b
    ; cat_adjointify : forall a b, CatIso a b -> cat_equiv a b
    (** In fully coherent examples, [cat_adjointify] and [cat_unadjointify] are inverses.  But proving that generally requires funext, and it may not be true in incoherent examples.  So we assert only one inversion property on underlying maps, on the side where that makes sense. *)
    ; cat_adj_fun : forall a b (f : CatIso a b), catiso_fun (cat_unadjointify a b (cat_adjointify a b f)) $== catiso_fun f
  }.

Notation "a $<~> b" := (cat_equiv a b).

Arguments cat_unadjointify [_ _ _ _ _ _] _.
Arguments cat_adjointify [_ _ _ _ _ _] _.

(** Equivalences can be composed. *)
Definition compose_cate {A : Type} `{HasEquivs A} {c1 : Is1Cat1 A} {a b c : A} (g : b $<~> c) (f : a $<~> b)
  : a $<~> c.
Proof.
  apply cat_adjointify; apply cat_unadjointify in g; apply cat_unadjointify in f.
  destruct f as [f fi retrf sectf]; destruct g as [g gi retrg sectg].
  refine (Build_CatIso _ _ _ a c (g $o f) (fi $o gi) _ _).
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (retrf $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply retrg.
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (sectg $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply sectf.
Defined.

Notation "g $oE f" := (compose_cate g f).

(** Any sufficiently coherent functor preserves equivalences.  *)
Definition emap {A B : Type} `{HasEquivs A} `{HasEquivs B} (F : A -> B)
           {ff1 : Is1Functor F} {ff2 : Is2Functor F} {ff11 : Is1Functor1 F}
           {a b : A} (f : a $<~> b) : F a $<~> F b.
Proof.
  apply cat_adjointify; apply cat_unadjointify in f; destruct f as [f fi isretr issect].
  srapply Build_CatIso.
  - exact (fmap F f).
  - exact (fmap F fi).
  - refine ((fmap_comp F fi f)^$ $@ fmap2 F isretr $@ fmap_id F _).
  - refine ((fmap_comp F f fi)^$ $@ fmap2 F issect $@ fmap_id F _).
Defined.

Global Instance hasequivs_op {A} `{HasEquivs A} : HasEquivs A^op.
Proof.
  srapply Build_HasEquivs; intros a b; unfold op in *; cbn in *.
  - exact (b $<~> a).
  - intros f; serapply Build_CatIso; unfold op; cbn.
    + exact (catiso_fun (cat_unadjointify f)).
    + exact (catiso_inv (cat_unadjointify f)).
    + apply catiso_sect.
    + apply catiso_retr.
  - intros [f fi r s]; apply cat_adjointify; serapply Build_CatIso;
      unfold op in *; cbn in *; assumption.
  - intros [f fi r s]; cbn.
    apply cat_adj_fun.
Defined.

(** ** The category of types *)

Global Instance is1cat_type : Is1Cat Type
  := Build_Is1Cat Type (fun a b => a -> b) (fun a => idmap) (fun a b c g f => g o f).

Global Instance is2cat_type : Is2Cat Type.
Proof.
  srefine (Build_Is2Cat Type _ (fun a b f g => f == g) _ _ _ _ _); cbn.
  - intros a b f x; reflexivity.
  - intros a b f g p x; exact ((p x)^).
  - intros a b f g h p q x; exact (p x @ q x).
  - intros a b c f g h p x; exact (ap h (p x)).
  - intros a b c f g p h x; exact (p (h x)).
Defined.

Global Instance is1cat1_strong_type : Is1Cat1_Strong Type.
Proof.
  srapply Build_Is1Cat1_Strong'; cbn; intros; reflexivity.
Defined.

(* Note that this passes back and forth through bi-invertible maps (see EquivalenceVarieties for more), which has the effect of adjointification.  We could avoid that by using 3-categories, but it doesn't seem worth the effort. *)
Global Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ Equiv _ _ _); intros A B.
  - intros [f ?].
    exact (Build_CatIso _ _ _ A B f f^-1 (eisretr f) (eissect f)).
  - intros [f fi issect isretr]; cbn in *.
    exact (equiv_adjointify f fi issect isretr).
  - reflexivity.
Defined.


(** ** Product categories *)

Global Instance is1cat_prod A B `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (A * B).
Proof.
  refine (Build_Is1Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

Global Instance is2cat_prod A B `{Is2Cat A} `{Is2Cat B}
  : Is2Cat (A * B).
Proof.
  srefine (Build_Is2Cat (A * B) _ _ _ _ _ _ _).
  - intros x y f g.
    exact ((fst f $== fst g) * (snd f $== snd g)).
  - intros [a1 b1] [a2 b2] [f g]; split; reflexivity.
  - intros [a1 b1] [a2 b2] [f1 g1] [f2 g2] [p q]; cbn in *.
    exact (p^$, q^$).
  - intros [a1 b1] [a2 b2] [f1 g1] [f2 g2] [f3 g3] [p1 q1] [p2 q2]; cbn in *.
    exact (p1 $@ p2, q1 $@ q2).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2] [f3 g3] [p q]; cbn in *.
    exact (f3 $@L p , g3 $@L q).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2] [p q] [f3 g3]; cbn in *.
    exact (p $@R f3, q $@R g3).
Defined.

Global Instance is1cat1_prod A B `{Is1Cat1 A} `{Is1Cat1 B}
  : Is1Cat1 (A * B).
Proof.
Admitted.


(** ** Sum categories *)

(* TODO? *)


(** ** Wild functor categories *)

Definition Fun1 (A B : Type) `{Is1Cat A} `{Is1Cat B}
  := { F : A -> B & Is1Functor F }.

Definition NatTrans {A B : Type} `{Is2Cat A} `{Is2Cat B} (F G : A -> B) {ff : Is1Functor F} {fg : Is1Functor G}
  := { alpha : F $--> G & Is1Natural F G alpha }.

(** Note that even if [A] and [B] are fully coherent oo-categories, the objects of our "functor category" are not fully coherent.  Thus we cannot in general expect this "functor category" to itself be fully coherent.  However, it is at least a wild 1-category.  *)

Global Instance is1cat_fun (A B : Type) `{Is1Cat1 A} `{Is1Cat1 B} : Is1Cat (Fun1 A B).
Proof.
  srapply Build_Is1Cat.
  - intros [F ?] [G ?].
    exact (NatTrans F G).
  - intros [F ?]; cbn.
    exists (fun a => Id (F a)); apply Build_Is1Natural; intros a b f; cbn.
    refine (cat_idl (fmap F f) $@ (cat_idr (fmap F f))^$).
  - intros [F ?] [G ?] [K ?] [gamma ?] [alpha ?]; cbn in *.
    exists (fun a => gamma a $o alpha a).
    apply Build_Is1Natural; intros a b f; cbn.
    refine (cat_assoc _ _ _ $@ _).
    refine ((gamma b $@L isnat alpha f) $@ _).
    refine (cat_assoc_opp _ _ _ $@ _).
    refine ((isnat gamma f) $@R alpha a $@ _).
    exact (cat_assoc _ _ _).
Defined.

(** In fact, it is automatically also a wild 2-category, with a totally incoherent notion of 2-cell between 1-coherent natural transformations. *)

Global Instance is2cat_fun (A B : Type) `{Is1Cat1 A} `{Is1Cat1 B} : Is2Cat (Fun1 A B).
Proof.
  srapply Build_Is2Cat.
  - intros [F ?] [G ?] [alpha ?] [gamma ?].
    exact (forall a, alpha a $== gamma a).
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    reflexivity.
  - intros [F ?] [G ?] [alpha ?] [gamma ?] mu a.
    exact ((mu a)^$).
  - intros [F ?] [G ?] [alpha ?] [gamma ?] [phi ?] mu nu a.
    exact (mu a $@ nu a).
  - intros [F ?] [G ?] [K ?] [alpha ?] [gamma ?] [phi ?] mu a; cbn.
    exact (phi a $@L mu a).
  - intros [F ?] [G ?] [K ?] [alpha ?] [gamma ?] mu [phi ?] a; cbn.
    exact (mu a $@R phi a).
Defined.

Global Instance is1cat1_fun (A B : Type) `{Is1Cat1 A} `{Is1Cat1 B} : Is1Cat1 (Fun1 A B).
Proof.
  srapply Build_Is1Cat1'.
  1,2:intros [F ?] [G ?] [K ?] [L ?] [alpha ?] [gamma ?] [phi ?] a; cbn.
  3,4:intros [F ?] [G ?] [alpha ?] a; cbn.
  5:intros [F ?] a; cbn.
  - rapply cat_assoc.
  - rapply cat_assoc_opp.
  - rapply cat_idl.
  - rapply cat_idr.
  - rapply cat_idlr.
Defined.

(** It also inherits a notion of equivalence, namely a natural transformation that is a pointwise equivalence.  Note that due to incoherence, in this case we do *not* expect [cat_unadjointify] and [cat_adjointify] to actually be inverses. *)

Definition NatEquiv {A B : Type} `{Is2Cat A} `{HasEquivs B} (F G : A -> B) {ff : Is1Functor F} {fg : Is1Functor G}
  := { alpha : forall a, F a $<~> G a & Is1Natural F G (fun a => catiso_fun (cat_unadjointify (alpha a))) }.

Global Instance hasequivs_fun (A B : Type) `{Is1Cat1 A} `{Is1Cat1 B} {eB : HasEquivs B} : HasEquivs (Fun1 A B).
Proof.
  srapply Build_HasEquivs.
  - intros [F ?] [G ?]. exact (NatEquiv F G).
  - intros [F ?] [G ?] [alpha alnat]. 
    srapply Build_CatIso; cbn.
    + exists (fun a => catiso_fun (cat_unadjointify (alpha a))); assumption.
    + exists (fun a => catiso_inv (cat_unadjointify (alpha a))).
      apply Build_Is1Natural; intros a b f.
      pose (alpha' := fun a => catiso_fun (cat_unadjointify (alpha a)) : F a $-> G a).
      change (Is1Natural F G alpha') in alnat.
      refine ((cat_idr _)^$ $@ _).
      refine ((_ $@L (catiso_retr (cat_unadjointify (alpha a)))^$) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L (cat_assoc_opp _ _ _)) $@ _).
      refine ((_ $@L ((isnat alpha' f)^$ $@R _)) $@ _).
      refine ((_ $@L (cat_assoc _ _ _)) $@ _).
      refine (cat_assoc_opp _ _ _ $@ _).
      refine ((catiso_sect (cat_unadjointify (alpha b)) $@R _) $@ _).
      exact (cat_idl _).
    + intros a; apply catiso_retr.
    + intros a; apply catiso_sect.
  - intros [F ?] [G ?] [[alpha ?] [gamma ?] r s]; cbn in *.
    srefine (exist _ _ _).
    + intros a; apply cat_adjointify.
      exact (Build_CatIso _ _ _ _ _ (alpha a) (gamma a) (r a) (s a)).
    + cbn; apply Build_Is1Natural; intros a b f.
      refine ((cat_adj_fun _ _ _ $@R _) $@ _); cbn.
      refine (_ $@ (_ $@L cat_adj_fun _ _ _)^$); cbn.
      exact (isnat alpha f).
  - intros [F ?] [G ?] [[alpha ?] [gamma ?] r s] a; cbn in *.
    apply cat_adj_fun.
Defined.


(** ** The covariant Yoneda lemma *)

(** This is easier than the contravariant version because it doesn't involve any "op"s. *)

Definition opyon {A : Type} `{Is1Cat A} (a : A) : A -> Type
  := fun b => (a $-> b).

Global Instance is1functor_opyon {A : Type} `{Is1Cat A} (a : A) : @Is1Functor A Type _ _ (opyon a).
Proof.
  apply Build_Is1Functor.
  unfold opyon; intros b c f g; cbn in *.
  exact (f $o g).
Defined.

Definition opyoneda {A : Type} `{Is1Cat A} (a : A) (F : A -> Type) {ff : Is1Functor F} 
  : F a -> (opyon a $--> F).
Proof.
  intros x b f.
  exact (fmap F f x).
Defined.

Definition un_opyoneda {A : Type} `{Is1Cat A} (a : A) (F : A -> Type) {ff : Is1Functor F}
  : (opyon a $--> F) -> F a
  := fun alpha => alpha a (Id a).

Global Instance is1natural_opyoneda {A : Type} `{Is2Cat A} (a : A) (F : A -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F} (x : F a)
  : Is1Natural (opyon a) F (opyoneda a F x).
Proof.
  apply Build_Is1Natural.
  unfold op, opyon, opyoneda; intros b c f g; cbn in *.
  exact (fmap_comp F g f x).
Defined.

Definition opyoneda_issect {A : Type} `{Is2Cat A} (a : A) (F : A -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F} (x : F a)
  : un_opyoneda a F (opyoneda a F x) = x
  := fmap_id F a x.

(** We assume for the converse that the coherences in [A] are equalities (this is a weak funext-type assumption).  Note that we do not in general recover the witness of 1-naturality.  Indeed, if [A] is fully coherent, then a transformation of the form [yoneda a F x] is always also fully coherently natural, so an incoherent witness of 1-naturality could not be recovered in this way.  *)
Definition opyoneda_isretr {A : Type} `{Is1Cat1_Strong A} (a : A)
           (F : A -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F}
           (alpha : opyon a $--> F) {alnat : Is1Natural (opyon a) F alpha}
           (b : A)
  : opyoneda a F (un_opyoneda a F alpha) b $== alpha b.
Proof.
  unfold opyoneda, un_opyoneda, opyon; intros f.
  refine ((isnat alpha f (Id a))^ @ _).
  cbn.
  apply ap.
  exact (cat_idr_strong f).
Defined.

(** Specialization to "full-faithfulness" of the Yoneda embedding.  (In quotes because, again, incoherence means we can't recover the witness of naturality.)  *)
Definition opyon_cancel {A : Type} `{Is1Cat A} (a b : A)
  : (opyon a $--> opyon b) -> (b $-> a)
  := un_opyoneda a (opyon b).

Definition opyon1 {A : Type} `{Is1Cat A} (a : A) : Fun1 A Type
  := (opyon a ; is1functor_opyon a).

(** We can also deduce "full-faithfulness" on equivalences. *)
Definition opyon_equiv {A : Type} `{Is1Cat1_Strong A} {eA : HasEquivs A} (a b : A)
  : (opyon1 a $<~> opyon1 b) -> (b $<~> a).
Proof.
  intros f; apply cat_adjointify; apply cat_unadjointify in f.
  destruct f as [[f ?] [g ?] r s]. cbn in *; unfold opyon in *.
  refine (Build_CatIso _ _ _ b a (f a (Id a)) (g b (Id b)) _ _); apply Htpy_path.
  - refine ((isnat g (f a (Id a)) (Id b))^ @ _); cbn.
    refine (_ @ s a (Id a)).
    apply ap. 
    rapply cat_idr_strong.
  - refine ((isnat f (g b (Id b)) (Id a))^ @ _); cbn.
    refine (_ @ r b (Id b)).
    apply ap. 
    rapply cat_idr_strong.
Defined.

(** ** The contravariant Yoneda lemma *)

(** We can deduce this from the covariant version with some boilerplate. *)

Definition yon {A : Type} `{Is1Cat A} (a : A) : A^op -> Type
  := @opyon (A^op) _ a.

Global Instance is1functor_yon {A : Type} `{Is1Cat A} (a : A)
  : Is1Functor (yon a)
  := @is1functor_opyon A _ a.

Definition yoneda {A : Type} `{Is1Cat A} (a : A)
           (F : A^op -> Type) {ff : Is1Functor F} 
  : F a -> (yon a $--> F)
  := @opyoneda (A^op) _ a F _.

Definition un_yoneda {A : Type} `{Is1Cat A} (a : A)
           (F : A^op -> Type) {ff : Is1Functor F}
  : (yon a $--> F) -> F a
  := @un_opyoneda (A^op) _ a F _.

Global Instance is1natural_yoneda {A : Type} `{Is2Cat A} (a : A)
       (F : A^op -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F} (x : F a)
  : Is1Natural (yon a) F (yoneda a F x)
  := @is1natural_opyoneda (A^op) _ _ a F _ _ x.

Definition yoneda_issect {A : Type} `{Is2Cat A} (a : A) (F : A^op -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F} (x : F a)
  : un_yoneda a F (yoneda a F x) = x
  := @opyoneda_issect (A^op) _ _ a F _ _ x.

Definition yoneda_isretr {A : Type} `{Is1Cat1_Strong A} (a : A)
           (F : A^op -> Type) {ff : Is1Functor F} {ff1 : Is1Functor1 F}
           (alpha : yon a $--> F) {alnat : Is1Natural (yon a) F alpha}
           (b : A)
  : yoneda a F (un_yoneda a F alpha) b $== alpha b
  := @opyoneda_isretr A^op _ _ _ a F _ _ alpha alnat b.

Definition yon_cancel {A : Type} `{Is1Cat A} (a b : A)
  : (yon a $--> yon b) -> (a $-> b)
  := un_yoneda a (yon b).

Definition yon1 {A : Type} `{Is1Cat A} (a : A) : Fun1 A^op Type
  := opyon1 a.

Definition yon_equiv {A : Type} `{Is1Cat1_Strong A} {eA : HasEquivs A} (a b : A)
  : (yon1 a $<~> yon1 b) -> (a $<~> b)
  := (@opyon_equiv A^op _ _ _ _ a b).


(** ** Wild category of wild categories *)

Record WildCat :=
  { cat_carrier : Type
    ; cat_is1cat : Is1Cat cat_carrier
    (* TODO: How much should we include here? *)
  }.
Coercion cat_carrier : WildCat >-> Sortclass.
Global Existing Instance cat_is1cat.

Global Instance is1cat_wildcat : Is1Cat WildCat.
Proof.
  refine (Build_Is1Cat WildCat (fun A B => Fun1 A B) _ _).
Admitted.

Global Instance is2cat_wildcat : Is2Cat WildCat.
Proof.
Admitted.

(* TODO: is1cat1_wildcat *)

(** ** Grothendieck constructions *)

(* How much coherence do we need? *)
