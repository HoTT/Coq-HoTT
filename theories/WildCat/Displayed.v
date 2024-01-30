Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Tactics.
Require Import Types.Sigma.
Require Import WildCat.Core.

Class IsDGraph (A : Type) `{IsGraph A} (D : A -> Type)
  := DHom : forall {a b : A}, (a $-> b) -> D a -> D b -> Type.

Class Is01DCat (A : Type) `{Is01Cat A} (D : A -> Type) `{!IsDGraph A D} :=
{
  DId : forall {a : A} (a' : D a), DHom (Id a) a' a';
  dcat_comp : forall {a b c : A} {g : b $-> c} {f : a $-> b}
              {a' : D a} {b' : D b} {c' : D c},
              DHom g b' c' -> DHom f a' b' -> DHom (g $o f) a' c';
}.

Notation "g '$o'' f" := (dcat_comp g f).

Definition dcat_postcomp {A : Type} {D : A -> Type} `{Is01DCat A D} {a b c : A}
  {g : b $-> c} {a' : D a} {b' : D b} {c' : D c} (g' : DHom g b' c')
  : forall (f : a $-> b), DHom f a' b' -> DHom (g $o f) a' c'
  := fun _ f' => g' $o' f'.

Definition dcat_precomp {A : Type} {D : A -> Type} `{Is01DCat A D} {a b c : A}
  {f : a $-> b} {a' : D a} {b' : D b} {c' : D c} (f' : DHom f a' b')
  : forall (g : b $-> c), DHom g b' c' -> DHom (g $o f) a' c'
  := fun _ g' => g' $o' f'.

Class Is0DGpd (A : Type) `{Is0Gpd A} (D : A -> Type)
  `{!IsDGraph A D, !Is01DCat A D}
  := dgpd_rev : forall {a b : A} {f : a $== b} {a' : D a} {b' : D b},
                DHom f a' b' -> DHom (f^$) b' a'.

Notation "p ^$'" := (dgpd_rev p).

Definition DGpdHom {A : Type} {D : A -> Type} `{Is0DGpd A D} {a b : A}
  (f : a $== b) (a' : D a) (b' : D b)
  := DHom f a' b'.

(** Diagrammatic order to match gpd_comp *)
Definition dgpd_comp {A : Type} {D : A -> Type} `{Is0DGpd A D} {a b c : A}
  {f : a $== b} {g : b $== c} {a' : D a} {b' : D b} {c' : D c}
  : DGpdHom f a' b' -> DGpdHom g b' c' -> DGpdHom (g $o f) a' c'
  := fun f' g' => g' $o' f'.

Notation "p '$@'' q" := (dgpd_comp p q).

Definition DGpdHom_path {A : Type} {D : A -> Type} `{Is0DGpd A D} {a b : A}
  (p : a = b) {a' : D a} {b': D b} (p' : transport D p a' = b')
  : DGpdHom (GpdHom_path p) a' b'.
Proof.
  destruct p, p'.
  apply DId.
Defined.

(** A displayed 0-functor [F'] over a 0-functor [F] acts on displayed objects and 1-cells and satisfies no axioms. *)
Class Is0DFunctor {A : Type} {B : Type}
  (DA : A -> Type) `{IsDGraph A DA} (DB : B -> Type) `{IsDGraph B DB}
  (F : A -> B) `{!Is0Functor F} (F' : forall (a : A), DA a -> DB (F a))
  := dfmap : forall {a b : A} {f : a $-> b} {a' : DA a} {b' : DA b},
              DHom f a' b' -> DHom (fmap F f) (F' a a') (F' b b').

Arguments dfmap {A B DA _ _ DB _ _} F {_} F' {_ _ _ _ _ _} f'.

Class Is2DGraph (A : Type) `{IsGraph A, !Is2Graph A}
  (D : A -> Type) `{!IsDGraph A D}
  := isdgraph_dhom : forall {a b} {a'} {b'},
                    IsDGraph (a $-> b) (fun f => DHom f a' b').

Global Existing Instance isdgraph_dhom.
#[global] Typeclasses Transparent Is2DGraph.

Class Is1DCat (A : Type) `{IsGraph A, !Is2Graph A, !Is01Cat A, !Is1Cat A}
  (D : A -> Type) `{!IsDGraph A D, !Is2DGraph A D, !Is01DCat A D} := {
    is01dcat_dhom : forall {a b : A} {a' : D a} {b' : D b},
                    Is01DCat (a $-> b) (fun f => DHom f a' b');
    is0dgpd_dhom : forall {a b : A} {a' : D a} {b' : D b},
                    Is0DGpd (a $-> b) (fun f => DHom f a' b');
    is0dfunctor_postcomp : forall {a b c : A} {g : b $-> c} {a' : D a}
                            {b' : D b} {c' : D c} (g' : DHom g b' c'),
                            Is0DFunctor (fun f => DHom f a' b')
                                        (fun gf => DHom gf a' c')
                                        (cat_postcomp a g) (dcat_postcomp g');
    is0dfunctor_precomp : forall {a b c : A} {f : a $-> b} {a' : D a}
                          {b' : D b} {c' : D c} (f' : DHom f a' b'),
                          Is0DFunctor (fun g => DHom g b' c')
                                      (fun gf => DHom gf a' c')
                                      (cat_precomp c f) (dcat_precomp f');
    dcat_assoc : forall {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d}
                  {a' : D a} {b' : D b} {c' : D c} {d' : D d}
                  (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d'),
                  DHom (cat_assoc f g h)
                        ((h' $o' g') $o' f') (h' $o' (g' $o' f'));
    dcat_idl : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
                (f' : DHom f a' b'), DHom (cat_idl f) (DId b' $o' f') f';
    dcat_idr : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
                (f' : DHom f a' b'), DHom (cat_idr f) (f' $o' DId a') f';
}.

Global Existing Instance is01dcat_dhom.
Global Existing Instance is0dgpd_dhom.
Global Existing Instance is0dfunctor_postcomp.
Global Existing Instance is0dfunctor_precomp.

Definition dcat_assoc_opp {A : Type} (D : A -> Type) `{Is1DCat A D}
  {a b c d : A}  {f : a $-> b} {g : b $-> c} {h : c $-> d}
  {a' : D a} {b' : D b} {c' : D c} {d' : D d}
  (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d')
  : DHom (cat_assoc_opp f g h) (h' $o' (g' $o' f')) ((h' $o' g') $o' f')
  := (dcat_assoc f' g' h')^$'.

Definition dcat_postwhisker {A : Type} {D : A -> Type} `{Is1DCat A D}
  {a b c : A} {f g : a $-> b} {h : b $-> c} {p : f $== g}
  {a' : D a} {b' : D b} {c' : D c} {f' : DHom f a' b'} {g' : DHom g a' b'}
  (h' : DHom h b' c') (p' : DHom p f' g')
  : DHom (h $@L p) (h' $o' f') (h' $o' g')
  := dfmap (cat_postcomp a h) (dcat_postcomp h') p'.

Notation "h $@L' p" := (dcat_postwhisker h p).

Definition dcat_prewhisker {A : Type} {D : A -> Type} `{Is1DCat A D}
  {a b c : A} {f : a $-> b} {g h : b $-> c} {p : g $== h}
  {a' : D a} {b' : D b} {c' : D c} {g' : DHom g b' c'} {h' : DHom h b' c'}
  (p' : DHom p g' h') (f' : DHom f a' b')
  : DHom (p $@R f) (g' $o' f') (h' $o' f')
  := dfmap (cat_precomp c f) (dcat_precomp f') p'.

Notation "p $@R' f" := (dcat_prewhisker p f).

Definition dcat_comp2 {A : Type} {D : A -> Type} `{Is1DCat A D} {a b c : A}
  {f g : a $-> b} {h k : b $-> c} {p : f $== g} {q : h $== k}
  {a' : D a} {b' : D b} {c' : D c} {f' : DHom f a' b'} {g' : DHom g a' b'}
  {h' : DHom h b' c'} {k' : DHom k b' c'}
  (p' : DHom p f' g') (q' : DHom q h' k')
  : DHom (p $@@ q) (h' $o' f') (k' $o' g')
  :=  (k' $@L' p') $o' (q' $@R' f').

Global Instance isgraph_sigma {A : Type} (D : A -> Type) `{IsDGraph A D}
  : IsGraph (sig D).
Proof.
  srapply Build_IsGraph.
  intros [a a'] [b b'].
  exact {f : a $-> b & DHom f a' b'}.
Defined.

Global Instance is01cat_sigma {A : Type} (D : A -> Type) `{Is01DCat A D}
  : Is01Cat (sig D).
Proof.
  srapply Build_Is01Cat.
  - intros [a a'].
    exact (Id a; DId a').
  - intros [a a'] [b b'] [c c'] [g g'] [f f'].
    exact (g $o f; g' $o' f').
Defined.

Global Instance is0gpd_sigma {A : Type} (D : A -> Type) `{Is0DGpd A D}
  : Is0Gpd (sig D).
Proof.
  srapply Build_Is0Gpd.
  intros [a a'] [b b'] [f f'].
  exact (f^$; dgpd_rev f').
Defined.

Global Instance is0functor_pr1 {A : Type} (D : A -> Type) `{IsDGraph A D}
  : Is0Functor (pr1 : (sig D) -> A).
Proof.
  srapply Build_Is0Functor.
  intros [a a'] [b b'] [f f'].
  exact f.
Defined.

Global Instance is2graph_sigma {A : Type} (D : A -> Type) `{Is2DGraph A D}
  : Is2Graph (sig D).
Proof.
  intros [a a'] [b b'].
  srapply Build_IsGraph.
  intros [f f'] [g g'].
  exact ({p : f $-> g & DHom p f' g'}).
Defined.

Global Instance is0functor_sigma {A : Type} (DA : A -> Type) `{Is01DCat A DA}
  {B : Type} (DB : B -> Type) `{Is01DCat B DB} (F : A -> B) `{!Is0Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!Is0DFunctor DA DB F F'}
  : Is0Functor (functor_sigma F F').
Proof.
  srapply Build_Is0Functor.
  intros [a a'] [b b'].
  intros [f f'].
  exact (fmap F f; dfmap F F' f').
Defined.

Global Instance is1cat_sigma {A : Type} (D : A -> Type) `{Is1DCat A D}
  : Is1Cat (sig D).
Proof.
  srapply Build_Is1Cat.
  - intros [a a'] [b b'] [c c'] [f f'].
    apply Build_Is0Functor.
    intros [g g'] [h h'] [p p'].
    exact (f $@L p; f' $@L' p').
  - intros [a a'] [b b'] [c c'] [f f'].
    apply Build_Is0Functor.
    intros [g g'] [h h'] [p p'].
    exact (p $@R f; p' $@R' f').
  - intros [a a'] [b b'] [c c'] [d d'] [f f'] [g g'] [h h'].
    exact (cat_assoc f g h; dcat_assoc f' g' h').
  - intros [a a'] [b b'] [f f'].
    exact (cat_idl f; dcat_idl f').
  - intros [a a'] [b b'] [f f'].
    exact (cat_idr f; dcat_idr f').
Defined.

Global Instance is1functor_pr1 {A : Type} {D : A -> Type} `{Is1DCat A D}
  : Is1Functor (pr1 : (sig D) -> A).
Proof.
  srapply Build_Is1Functor.
  - intros [a a'] [b b'] [f f'] [g g'] [p p'].
    exact p.
  - intros [a a'].
    apply Id.
  - intros [a a'] [b b'] [c c'] [f f'] [g g'].
    apply Id.
Defined.

Class Is1DCat_Strong (A : Type) `{IsGraph A, !Is2Graph A, !Is01Cat A, !Is1Cat_Strong A}
  (D : A -> Type)
  `{!IsDGraph A D, !Is2DGraph A D, !Is01DCat A D} :=
{
  is01dcat_dhom_strong : forall {a b : A} {a' : D a} {b' : D b},
                          Is01DCat (a $-> b) (fun f => DHom f a' b');
  is0dgpd_dhom_strong : forall {a b : A} {a' : D a} {b' : D b},
                        Is0DGpd (a $-> b) (fun f => DHom f a' b');
  is0dfunctor_postcomp_strong : forall {a b c : A} {g : b $-> c} {a' : D a}
                                {b' : D b} {c' : D c} (g' : DHom g b' c'),
                                Is0DFunctor (fun f => DHom f a' b')
                                            (fun gf => DHom gf a' c')
                                            (cat_postcomp a g)
                                            (dcat_postcomp g');
  is0dfunctor_precomp_strong : forall {a b c : A} {f : a $-> b} {a' : D a}
                                {b' : D b} {c' : D c} (f' : DHom f a' b'),
                                Is0DFunctor (fun g => DHom g b' c')
                                            (fun gf => DHom gf a' c')
                                            (cat_precomp c f)
                                            (dcat_precomp f');
  dcat_assoc_strong : forall {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d}
                      {a' : D a} {b' : D b} {c' : D c} {d' : D d}
                      (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d'),
                      (transport (fun k => DHom k a' d') (cat_assoc_strong f g h)
                      ((h' $o' g') $o' f')) = h' $o' (g' $o' f');
  dcat_idl_strong : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
                    (f' : DHom f a' b'),
                    (transport (fun k => DHom k a' b') (cat_idl_strong f)
                    (DId b' $o' f')) = f';
  dcat_idr_strong : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
                    (f' : DHom f a' b'),
                    (transport (fun k => DHom k a' b') (cat_idr_strong f)
                    (f' $o' DId a')) = f';
}.

Global Existing Instance is01dcat_dhom_strong.
Global Existing Instance is0dgpd_dhom_strong.
Global Existing Instance is0dfunctor_postcomp_strong.
Global Existing Instance is0dfunctor_precomp_strong.

Definition dcat_assoc_opp_strong {A : Type} (D : A -> Type) `{Is1DCat_Strong A D}
  {a b c d : A}  {f : a $-> b} {g : b $-> c} {h : c $-> d}
  {a' : D a} {b' : D b} {c' : D c} {d' : D d}
  (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d')
  : (transport (fun k => DHom k a' d') (cat_assoc_opp_strong f g h)
                      (h' $o' (g' $o' f'))) = (h' $o' g') $o' f'.
Proof.
  apply (moveR_transport_V (fun k => DHom k a' d') (cat_assoc_strong f g h) _ _).
  exact ((dcat_assoc_strong f' g' h')^).
Defined.

Global Instance is1dcat_is1dcatstrong {A : Type} (D : A -> Type)
  `{Is1DCat_Strong A D} : Is1DCat A D.
Proof.
  srapply Build_Is1DCat.
  - intros a b c d f g h a' b' c' d' f' g' h'.
    exact (DGpdHom_path (cat_assoc_strong f g h) (dcat_assoc_strong f' g' h')).
  - intros a b f a' b' f'.
    exact (DGpdHom_path (cat_idl_strong f) (dcat_idl_strong f')).
  - intros a b f a' b' f'.
    exact (DGpdHom_path (cat_idr_strong f) (dcat_idr_strong f')).
Defined.

Class Is1DFunctor
  {A B : Type} (DA : A -> Type) `{Is1DCat A DA} (DB : B -> Type) `{Is1DCat B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!Is0DFunctor DA DB F F'} :=
{
  dfmap2 : forall {a b : A} {f g : a $-> b} {p : f $== g} {a' : DA a}
            {b' : DA b} (f' : DHom f a' b') (g' : DHom g a' b'),
            DHom p f' g' -> DHom (fmap2 F p) (dfmap F F' f') (dfmap F F' g');
  dfmap_id : forall {a : A} (a' : DA a),
              DHom (fmap_id F a) (dfmap F F' (DId a')) (DId (F' a a'));
  dfmap_comp : forall {a b c : A} {f : a $-> b} {g : b $-> c} {a' : DA a}
                {b' : DA b} {c' : DA c} (f' : DHom f a' b') (g' : DHom g b' c'),
                DHom (fmap_comp F f g) (dfmap F F' (g' $o' f'))
                (dfmap F F' g' $o' dfmap F F' f');
}.

Global Instance is1functor_sigma {A B : Type} (DA : A -> Type) (DB : B -> Type)
  (F : A -> B) (F' : forall (a : A), DA a -> DB (F a)) `{Is1DFunctor A B DA DB F F'}
  : Is1Functor (functor_sigma F F').
Proof.
  srapply Build_Is1Functor.
  - intros [a a'] [b b'] [f f'] [g g'] [p p'].
    exists (fmap2 F p).
    exact (dfmap2 f' g' p').
  - intros [a a'].
    exact (fmap_id F a; dfmap_id a').
  - intros [a a'] [b b'] [c c'] [f f'] [g g'].
    exact (fmap_comp F f g; dfmap_comp f' g').
Defined.

Section IdentityFunctor.
  Global Instance is0dfunctor_idmap {A : Type} `{Is01Cat A}
    (DA : A -> Type) `{!IsDGraph A DA, !Is01DCat A DA}
    : Is0DFunctor DA DA (idmap) (fun a a' => a').
  Proof.
    intros a b f a' b' f'.
    assumption.
  Defined.

  Global Instance is1dfunctor_idmap {A : Type} `{Is1Cat A} (DA : A -> Type)
    `{!IsDGraph A DA, !Is2DGraph A DA, !Is01DCat A DA, !Is1DCat A DA}
    : Is1DFunctor DA DA (idmap) (fun a a' => a').
  Proof.
    apply Build_Is1DFunctor.
    - intros a b f g p a' b' f' g' p'.
      assumption.
    - intros a a'.
      apply DId.
    - intros a b c f g a' b' c' f' g'.
      apply DId.
  Defined.
End IdentityFunctor.

Section ConstantFunctor.
  Global Instance is0dfunctor_const {A : Type} `{IsGraph A}
    {B : Type} `{Is01Cat B} (DA : A -> Type) `{!IsDGraph A DA}
    (DB : B -> Type) `{!IsDGraph B DB, !Is01DCat B DB} (x : B) (x' : DB x)
    : Is0DFunctor DA DB (fun _ : A => x) (fun _ _ => x').
  Proof.
    intros a b f a' b' f'.
    apply DId.
  Defined.

  Global Instance is1dfunctor_const {A : Type} `{Is1Cat A} {B : Type} `{Is1Cat B}
    (DA : A -> Type)
    `{!IsDGraph A DA, !Is2DGraph A DA, !Is01DCat A DA, !Is1DCat A DA}
    (DB : B -> Type)
    `{!IsDGraph B DB, !Is2DGraph B DB, !Is01DCat B DB, !Is1DCat B DB}
    (x : B) (x' : DB x)
    : Is1DFunctor DA DB (fun _ : A => x) (fun _ _ => x').
  Proof.
    srapply Build_Is1DFunctor.
    - intros a b f g p a' b' f' g' p'.
      apply DId.
    - intros a a'.
      apply DId.
    - intros a b c f g a' b' c' f' g'.
      apply dgpd_rev.
      apply dcat_idl.
  Defined.
End ConstantFunctor.

Section CompositeFunctor.
  Context {A B C : Type} {DA : A -> Type} {DB : B -> Type} {DC : C -> Type}
  (F : A -> B) (G : B -> C)
  (F' : forall (a : A), DA a -> DB (F a))
  (G' : forall (b : B), DB b -> DC (G b)).

  Global Instance is0dfunctor_compose
    `{IsDGraph A DA} `{IsDGraph B DB} `{IsDGraph C DC}
    `{!Is0Functor F} `{!Is0Functor G}
    `{!Is0DFunctor DA DB F F'} `{!Is0DFunctor DB DC G G'}
    : Is0DFunctor DA DC (G o F) (fun a a' => (G' (F a) o (F' a)) a').
  Proof.
    intros a b f a' b' f'.
    exact (dfmap G G' (dfmap F F' f')).
  Defined.

  Global Instance is1dfunctor_compose
    `{Is1DCat A DA} `{Is1DCat B DB} `{Is1DCat C DC}
    `{!Is0Functor F, !Is1Functor F} `{!Is0Functor G, !Is1Functor G}
    `{!Is0DFunctor DA DB F F', !Is1DFunctor DA DB F F'}
    `{!Is0DFunctor DB DC G G', !Is1DFunctor DB DC G G'}
    : Is1DFunctor DA DC (G o F) (fun a a' => (G' (F a) o (F' a)) a').
  Proof.
    srapply Build_Is1DFunctor.
    - intros a b f g p a' b' f' g' p'.
      apply (dfmap2 _ _ (dfmap2 f' g' p')).
    - intros a a'.
      apply (dfmap2 _ _ (dfmap_id a') $@' dfmap_id _).
    - intros a b c f g a' b' c' f' g'.
      apply (dfmap2 _ _ (dfmap_comp f' g') $@' dfmap_comp _ _).
  Defined.
End CompositeFunctor.
