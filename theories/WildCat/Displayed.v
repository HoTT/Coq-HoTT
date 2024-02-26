Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Tactics.
Require Import Types.Sigma.
Require Import WildCat.Core.
Require Import WildCat.Prod.

Class IsDGraph {A : Type} `{IsGraph A} (D : A -> Type)
  := DHom : forall {a b : A}, (a $-> b) -> D a -> D b -> Type.

Class IsD01Cat {A : Type} `{Is01Cat A} (D : A -> Type) `{!IsDGraph D} :=
{
  DId : forall {a : A} (a' : D a), DHom (Id a) a' a';
  dcat_comp : forall {a b c : A} {g : b $-> c} {f : a $-> b}
              {a' : D a} {b' : D b} {c' : D c},
              DHom g b' c' -> DHom f a' b' -> DHom (g $o f) a' c';
}.

Notation "g '$o'' f" := (dcat_comp g f).

Definition dcat_postcomp {A : Type} {D : A -> Type} `{IsD01Cat A D} {a b c : A}
  {g : b $-> c} {a' : D a} {b' : D b} {c' : D c} (g' : DHom g b' c')
  : forall (f : a $-> b), DHom f a' b' -> DHom (g $o f) a' c'
  := fun _ f' => g' $o' f'.

Definition dcat_precomp {A : Type} {D : A -> Type} `{IsD01Cat A D} {a b c : A}
  {f : a $-> b} {a' : D a} {b' : D b} {c' : D c} (f' : DHom f a' b')
  : forall (g : b $-> c), DHom g b' c' -> DHom (g $o f) a' c'
  := fun _ g' => g' $o' f'.

Class IsD0Gpd {A : Type} `{Is0Gpd A} (D : A -> Type)
  `{!IsDGraph D, !IsD01Cat D}
  := dgpd_rev : forall {a b : A} {f : a $== b} {a' : D a} {b' : D b},
                DHom f a' b' -> DHom (f^$) b' a'.

Notation "p ^$'" := (dgpd_rev p).

Definition DGpdHom {A : Type} {D : A -> Type} `{IsD0Gpd A D} {a b : A}
  (f : a $== b) (a' : D a) (b' : D b)
  := DHom f a' b'.

(** Diagrammatic order to match gpd_comp *)
Definition dgpd_comp {A : Type} {D : A -> Type} `{IsD0Gpd A D} {a b c : A}
  {f : a $== b} {g : b $== c} {a' : D a} {b' : D b} {c' : D c}
  : DGpdHom f a' b' -> DGpdHom g b' c' -> DGpdHom (g $o f) a' c'
  := fun f' g' => g' $o' f'.

Notation "p '$@'' q" := (dgpd_comp p q).

Definition DHom_path {A : Type} {D : A -> Type} `{IsD01Cat A D} {a b : A}
  (p : a = b) {a' : D a} {b': D b} (p' : transport D p a' = b')
  : DHom (Hom_path p) a' b'.
Proof.
  destruct p, p'; apply DId.
Defined.

Definition DGpdHom_path {A : Type} {D : A -> Type} `{IsD0Gpd A D} {a b : A}
  (p : a = b) {a' : D a} {b': D b} (p' : transport D p a' = b')
  : DGpdHom (GpdHom_path p) a' b'
  := DHom_path p p'.

Global Instance reflexive_DHom {A} {D : A -> Type} `{IsD01Cat A D} {a : A}
  : Reflexive (DHom (Id a))
  := fun a' => DId a'.

Global Instance reflexive_DGpdHom {A} {D : A -> Type} `{IsD0Gpd A D} {a : A}
  : Reflexive (DGpdHom (Id a))
  := fun a' => DId a'.

(** A displayed 0-functor [F'] over a 0-functor [F] acts on displayed objects and 1-cells and satisfies no axioms. *)
Class IsD0Functor {A : Type} {B : Type}
  {DA : A -> Type} `{IsDGraph A DA} {DB : B -> Type} `{IsDGraph B DB}
  (F : A -> B) `{!Is0Functor F} (F' : forall (a : A), DA a -> DB (F a))
  := dfmap : forall {a b : A} {f : a $-> b} {a' : DA a} {b' : DA b},
              DHom f a' b' -> DHom (fmap F f) (F' a a') (F' b b').

Arguments dfmap {A B DA _ _ DB _ _} F {_} F' {_ _ _ _ _ _} f'.

Class IsD2Graph {A : Type} `{Is2Graph A}
  (D : A -> Type) `{!IsDGraph D}
  := isdgraph_hom : forall {a b} {a'} {b'},
                      IsDGraph (fun (f:a $-> b) => DHom f a' b').

Global Existing Instance isdgraph_hom.
#[global] Typeclasses Transparent IsD2Graph.

Class IsD1Cat {A : Type} `{Is1Cat A}
  (D : A -> Type) `{!IsDGraph D, !IsD2Graph D, !IsD01Cat D} :=
{
  isd01cat_hom : forall {a b : A} {a' : D a} {b' : D b},
                 IsD01Cat (fun f => DHom f a' b');
  isd0gpd_hom : forall {a b : A} {a' : D a} {b' : D b},
                IsD0Gpd (fun f => DHom f a' b');
  isd0functor_postcomp : forall {a b c : A} {g : b $-> c} {a' : D a}
                         {b' : D b} {c' : D c} (g' : DHom g b' c'),
                         @IsD0Functor _ _ (fun f => DHom f a' b')
                         _ _ (fun gf => DHom gf a' c')
                         _ _ (cat_postcomp a g) _ (dcat_postcomp g');
  isd0functor_precomp : forall {a b c : A} {f : a $-> b} {a' : D a}
                        {b' : D b} {c' : D c} (f' : DHom f a' b'),
                        @IsD0Functor _ _ (fun g => DHom g b' c')
                        _ _ (fun gf => DHom gf a' c')
                        _ _ (cat_precomp c f) _ (dcat_precomp f');
  dcat_assoc : forall {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d}
               {a' : D a} {b' : D b} {c' : D c} {d' : D d}
               (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d'),
               DHom (cat_assoc f g h) ((h' $o' g') $o' f')
               (h' $o' (g' $o' f'));
  dcat_idl : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
             (f' : DHom f a' b'), DHom (cat_idl f) (DId b' $o' f') f';
  dcat_idr : forall {a b : A} {f : a $-> b} {a' : D a} {b' : D b}
             (f' : DHom f a' b'), DHom (cat_idr f) (f' $o' DId a') f';
}.

Global Existing Instance isd01cat_hom.
Global Existing Instance isd0gpd_hom.
Global Existing Instance isd0functor_postcomp.
Global Existing Instance isd0functor_precomp.

Definition dcat_assoc_opp {A : Type} {D : A -> Type} `{IsD1Cat A D}
  {a b c d : A}  {f : a $-> b} {g : b $-> c} {h : c $-> d}
  {a' : D a} {b' : D b} {c' : D c} {d' : D d}
  (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d')
  : DHom (cat_assoc_opp f g h) (h' $o' (g' $o' f')) ((h' $o' g') $o' f')
  := (dcat_assoc f' g' h')^$'.

Definition dcat_postwhisker {A : Type} {D : A -> Type} `{IsD1Cat A D}
  {a b c : A} {f g : a $-> b} {h : b $-> c} {p : f $== g}
  {a' : D a} {b' : D b} {c' : D c} {f' : DHom f a' b'} {g' : DHom g a' b'}
  (h' : DHom h b' c') (p' : DHom p f' g')
  : DHom (h $@L p) (h' $o' f') (h' $o' g')
  := dfmap (cat_postcomp a h) (dcat_postcomp h') p'.

Notation "h $@L' p" := (dcat_postwhisker h p).

Definition dcat_prewhisker {A : Type} {D : A -> Type} `{IsD1Cat A D}
  {a b c : A} {f : a $-> b} {g h : b $-> c} {p : g $== h}
  {a' : D a} {b' : D b} {c' : D c} {g' : DHom g b' c'} {h' : DHom h b' c'}
  (p' : DHom p g' h') (f' : DHom f a' b')
  : DHom (p $@R f) (g' $o' f') (h' $o' f')
  := dfmap (cat_precomp c f) (dcat_precomp f') p'.

Notation "p $@R' f" := (dcat_prewhisker p f).

Definition dcat_comp2 {A : Type} {D : A -> Type} `{IsD1Cat A D} {a b c : A}
  {f g : a $-> b} {h k : b $-> c} {p : f $== g} {q : h $== k}
  {a' : D a} {b' : D b} {c' : D c} {f' : DHom f a' b'} {g' : DHom g a' b'}
  {h' : DHom h b' c'} {k' : DHom k b' c'}
  (p' : DHom p f' g') (q' : DHom q h' k')
  : DHom (p $@@ q) (h' $o' f') (k' $o' g')
  :=  (k' $@L' p') $o' (q' $@R' f').

Notation "q $@@' p" := (dcat_comp2 q p).

(** Monomorphisms and epimorphisms. *)

Definition DMonic {A} {D : A -> Type} `{IsD1Cat A D} {b c : A}
  {f : b $-> c} {mon : Monic f} {b' : D b} {c' : D c} (f' : DHom f b' c')
  := forall (a : A) (g h : a $-> b) (p : f $o g $== f $o h) (a' : D a)
      (g' : DHom g a' b') (h' : DHom h a' b'),
      DGpdHom p (f' $o' g') (f' $o' h') -> DGpdHom (mon a g h p) g' h'.

Definition DEpic {A} {D : A -> Type} `{IsD1Cat A D} {a b : A}
  {f : a $-> b} {epi : Epic f} {a' : D a} {b' : D b} (f' : DHom f a' b')
  := forall (c : A) (g h : b $-> c) (p : g $o f $== h $o f) (c' : D c)
      (g' : DHom g b' c') (h' : DHom h b' c'),
      DGpdHom p (g' $o' f') (h' $o' f') -> DGpdHom (epi c g h p) g' h'.

Global Instance isgraph_sigma {A : Type} (D : A -> Type) `{IsDGraph A D}
  : IsGraph (sig D).
Proof.
  srapply Build_IsGraph.
  intros [a a'] [b b'].
  exact {f : a $-> b & DHom f a' b'}.
Defined.

Global Instance is01cat_sigma {A : Type} (D : A -> Type) `{IsD01Cat A D}
  : Is01Cat (sig D).
Proof.
  srapply Build_Is01Cat.
  - intros [a a'].
    exact (Id a; DId a').
  - intros [a a'] [b b'] [c c'] [g g'] [f f'].
    exact (g $o f; g' $o' f').
Defined.

Global Instance is0gpd_sigma {A : Type} (D : A -> Type) `{IsD0Gpd A D}
  : Is0Gpd (sig D).
Proof.
  srapply Build_Is0Gpd.
  intros [a a'] [b b'] [f f'].
  exact (f^$; dgpd_rev f').
Defined.

Global Instance is0functor_pr1 {A : Type} (D : A -> Type) `{IsDGraph A D}
  : Is0Functor (pr1 : sig D -> A).
Proof.
  srapply Build_Is0Functor.
  intros [a a'] [b b'] [f f'].
  exact f.
Defined.

Global Instance is2graph_sigma {A : Type} (D : A -> Type) `{IsD2Graph A D}
  : Is2Graph (sig D).
Proof.
  intros [a a'] [b b'].
  srapply Build_IsGraph.
  intros [f f'] [g g'].
  exact ({p : f $-> g & DHom p f' g'}).
Defined.

Global Instance is0functor_sigma {A : Type} (DA : A -> Type) `{IsD01Cat A DA}
  {B : Type} (DB : B -> Type) `{IsD01Cat B DB} (F : A -> B) `{!Is0Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F'}
  : Is0Functor (functor_sigma F F').
Proof.
  srapply Build_Is0Functor.
  intros [a a'] [b b'].
  intros [f f'].
  exact (fmap F f; dfmap F F' f').
Defined.

Global Instance is1cat_sigma {A : Type} (D : A -> Type) `{IsD1Cat A D}
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

Global Instance is1functor_pr1 {A : Type} {D : A -> Type} `{IsD1Cat A D}
  : Is1Functor (pr1 : sig D -> A).
Proof.
  srapply Build_Is1Functor.
  - intros [a a'] [b b'] [f f'] [g g'] [p p'].
    exact p.
  - intros [a a'].
    apply Id.
  - intros [a a'] [b b'] [c c'] [f f'] [g g'].
    apply Id.
Defined.

Class IsD1Cat_Strong {A : Type} `{Is1Cat_Strong A}
  (D : A -> Type)
  `{!IsDGraph D, !IsD2Graph D, !IsD01Cat D} :=
{
  isd01cat_hom_strong : forall {a b : A} {a' : D a} {b' : D b},
                        IsD01Cat (fun f => DHom f a' b');
  isd0gpd_hom_strong : forall {a b : A} {a' : D a} {b' : D b},
                       IsD0Gpd (fun f => DHom f a' b');
  isd0functor_postcomp_strong : forall {a b c : A} {g : b $-> c} {a' : D a}
                                {b' : D b} {c' : D c} (g' : DHom g b' c'),
                                @IsD0Functor _ _ (fun f => DHom f a' b')
                                _ _ (fun gf => DHom gf a' c')
                                _ _ (cat_postcomp a g) _ (dcat_postcomp g');
  isd0functor_precomp_strong : forall {a b c : A} {f : a $-> b} {a' : D a}
                                {b' : D b} {c' : D c} (f' : DHom f a' b'),
                                @IsD0Functor _ _ (fun g => DHom g b' c')
                                _ _ (fun gf => DHom gf a' c')
                                _ _ (cat_precomp c f) _ (dcat_precomp f');
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

Global Existing Instance isd01cat_hom_strong.
Global Existing Instance isd0gpd_hom_strong.
Global Existing Instance isd0functor_postcomp_strong.
Global Existing Instance isd0functor_precomp_strong.

Definition dcat_assoc_opp_strong {A : Type} {D : A -> Type} `{IsD1Cat_Strong A D}
  {a b c d : A}  {f : a $-> b} {g : b $-> c} {h : c $-> d}
  {a' : D a} {b' : D b} {c' : D c} {d' : D d}
  (f' : DHom f a' b') (g' : DHom g b' c') (h' : DHom h c' d')
  : (transport (fun k => DHom k a' d') (cat_assoc_opp_strong f g h)
    (h' $o' (g' $o' f'))) = (h' $o' g') $o' f'.
Proof.
  apply (moveR_transport_V (fun k => DHom k a' d') (cat_assoc_strong f g h) _ _).
  exact ((dcat_assoc_strong f' g' h')^).
Defined.

Global Instance isd1cat_isd1catstrong {A : Type} (D : A -> Type)
  `{IsD1Cat_Strong A D} : IsD1Cat D.
Proof.
  srapply Build_IsD1Cat.
  - intros a b c d f g h a' b' c' d' f' g' h'.
    exact (DHom_path (cat_assoc_strong f g h) (dcat_assoc_strong f' g' h')).
  - intros a b f a' b' f'.
    exact (DHom_path (cat_idl_strong f) (dcat_idl_strong f')).
  - intros a b f a' b' f'.
    exact (DHom_path (cat_idr_strong f) (dcat_idr_strong f')).
Defined.

Global Instance is1catstrong_sigma {A : Type}
  (D : A -> Type) `{IsD1Cat_Strong A D}
  : Is1Cat_Strong (sig D).
Proof.
  srapply Build_Is1Cat_Strong.
  - intros aa' bb' cc' dd' [f f'] [g g'] [h h'].
    exact (path_sigma' _
            (cat_assoc_strong f g h) (dcat_assoc_strong f' g' h')).
  - intros aa' bb' [f f'].
    exact (path_sigma' _ (cat_idl_strong f) (dcat_idl_strong f')).
  - intros aa' bb' [f f'].
    exact (path_sigma' _ (cat_idr_strong f) (dcat_idr_strong f')).
Defined.

Class IsD1Functor
  {A B : Type} {DA : A -> Type} `{IsD1Cat A DA} {DB : B -> Type} `{IsD1Cat B DB}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (F' : forall (a : A), DA a -> DB (F a)) `{!IsD0Functor F F'} :=
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

Arguments dfmap2 {A B DA _ _ _ _ _ _ _ _ DB _ _ _ _ _ _ _ _}
  F {_ _} F' {_ _ a b f g p a' b' f' g'} p'.
Arguments dfmap_id {A B DA _ _ _ _ _ _ _ _ DB _ _ _ _ _ _ _ _}
  F {_ _} F' {_ _ a} a'.
Arguments dfmap_comp {A B DA _ _ _ _ _ _ _ _ DB _ _ _ _ _ _ _ _}
  F {_ _} F' {_ _ a b c f g a' b' c'} f' g'.

Global Instance is1functor_sigma {A B : Type} (DA : A -> Type) (DB : B -> Type)
  (F : A -> B) (F' : forall (a : A), DA a -> DB (F a)) `{IsD1Functor A B DA DB F F'}
  : Is1Functor (functor_sigma F F').
Proof.
  srapply Build_Is1Functor.
  - intros [a a'] [b b'] [f f'] [g g'] [p p'].
    exists (fmap2 F p).
    exact (dfmap2 F F' p').
  - intros [a a'].
    exact (fmap_id F a; dfmap_id F F' a').
  - intros [a a'] [b b'] [c c'] [f f'] [g g'].
    exact (fmap_comp F f g; dfmap_comp F F' f' g').
Defined.

Section IdentityFunctor.
  Global Instance isd0functor_idmap {A : Type} `{Is01Cat A}
    (DA : A -> Type) `{!IsDGraph DA, !IsD01Cat DA}
    : IsD0Functor (idmap) (fun a a' => a').
  Proof.
    intros a b f a' b' f'.
    assumption.
  Defined.

  Global Instance isd1functor_idmap {A : Type} (DA : A -> Type)
    `{IsD1Cat A DA}
    : IsD1Functor (idmap) (fun a a' => a').
  Proof.
    apply Build_IsD1Functor.
    - intros a b f g p a' b' f' g' p'.
      assumption.
    - intros a a'.
      apply DId.
    - intros a b c f g a' b' c' f' g'.
      apply DId.
  Defined.
End IdentityFunctor.

Section ConstantFunctor.
  Global Instance isd0functor_const {A : Type} `{IsGraph A}
    {B : Type} `{Is01Cat B} (DA : A -> Type) `{!IsDGraph DA}
    (DB : B -> Type) `{!IsDGraph DB, !IsD01Cat DB} (x : B) (x' : DB x)
    : IsD0Functor (fun _ : A => x) (fun _ _ => x').
  Proof.
    intros a b f a' b' f'.
    apply DId.
  Defined.

  Global Instance isd1functor_const {A : Type} {B : Type}
    (DA : A -> Type)
    `{IsD1Cat A DA}
    (DB : B -> Type)
    `{IsD1Cat B DB}
    (x : B) (x' : DB x)
    : IsD1Functor (fun _ => x) (fun _ _ => x').
  Proof.
    snrapply Build_IsD1Functor.
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

  Global Instance isd0functor_compose
    `{IsDGraph A DA} `{IsDGraph B DB} `{IsDGraph C DC}
    `{!Is0Functor F} `{!Is0Functor G}
    `{!IsD0Functor F F'} `{!IsD0Functor G G'}
    : IsD0Functor (G o F) (fun a a' => (G' (F a) o (F' a)) a').
  Proof.
    intros a b f a' b' f'.
    exact (dfmap G G' (dfmap F F' f')).
  Defined.

  Global Instance isd1functor_compose
    `{IsD1Cat A DA} `{IsD1Cat B DB} `{IsD1Cat C DC}
    `{!Is0Functor F, !Is1Functor F} `{!Is0Functor G, !Is1Functor G}
    `{!IsD0Functor F F', !IsD1Functor F F'}
    `{!IsD0Functor G G', !IsD1Functor G G'}
    : IsD1Functor (G o F) (fun a a' => (G' (F a) o (F' a)) a').
  Proof.
    snrapply Build_IsD1Functor.
    - intros a b f g p a' b' f' g' p'.
      apply (dfmap2 _ _ (dfmap2 F F' p')).
    - intros a a'.
      apply (dfmap2 _ _ (dfmap_id F F' a') $@' dfmap_id G G' _).
    - intros a b c f g a' b' c' f' g'.
      apply (dfmap2 _ _ (dfmap_comp F F' f' g') $@' dfmap_comp G G' _ _).
  Defined.
End CompositeFunctor.

Local Definition pointwise_prod {A B : Type} (DA : A -> Type) (DB : B -> Type)
  (x : A * B) := DA (fst x) * DB (snd x).

Global Instance isdgraph_prod {A B : Type} (DA : A -> Type) `{IsDGraph A DA}
  (DB : B -> Type) `{IsDGraph B DB}
  : IsDGraph (pointwise_prod DA DB).
Proof.
  intros [a1 b1] [a2 b2] [f g] [a1' b1'] [a2' b2'].
  exact (DHom f a1' a2' * DHom g b1' b2').
Defined.

Global Instance isd01cat_prod {A B : Type} (DA : A -> Type) `{IsD01Cat A DA}
  (DB : B -> Type) `{IsD01Cat B DB}
  : IsD01Cat (pointwise_prod DA DB).
Proof.
  srapply Build_IsD01Cat.
  - intros [a b] [a' b'].
    exact (DId a', DId b').
  - intros [a1 b1] [a2 b2] [a3 b3] [f2 g2] [f1 g1] [a1' b1'] [a2' b2'] [a3' b3'].
    intros [f2' g2'] [f1' g1'].
    exact (f2' $o' f1', g2' $o' g1').
Defined.

Global Instance isd0gpd_prod {A B : Type} (DA : A -> Type) `{IsD0Gpd A DA}
  (DB : B -> Type) `{IsD0Gpd B DB}
  : IsD0Gpd (pointwise_prod DA DB).
Proof.
  intros [a1 b1] [a2 b2] [f g] [a1' b1'] [a2' b2'] [f' g'].
  exact (f'^$', g'^$').
Defined.

Global Instance isd2graph_prod {A B : Type} (DA : A -> Type) `{IsD2Graph A DA}
  (DB : B -> Type) `{IsD2Graph B DB}
  : IsD2Graph (pointwise_prod DA DB).
Proof.
  intros [a1 b1] [a2 b2] [a1' b1'] [a2' b2'].
  srapply isdgraph_prod.
Defined.

Global Instance isd1cat_prod {A B : Type} (DA : A -> Type) `{IsD1Cat A DA}
  (DB : B -> Type) `{IsD1Cat B DB}
  : IsD1Cat (pointwise_prod DA DB).
Proof.
  snrapply Build_IsD1Cat.
  - intros ab1 ab2 ab1' ab2'.
    srapply isd01cat_prod.
  - intros ab1 ab2 ab1' ab2'.
    srapply (isd0gpd_prod _ _).
  - intros ab1 ab2 ab3 fg ab1' ab2' ab3' [f' g'].
    intros hk1 hk2 pq hk1' hk2' [p' q'].
    exact (f' $@L' p', g' $@L' q').
  - intros ab1 ab2 ab3 fg ab1' ab2' ab3' [f' g'].
    intros hk1 hk2 pq hk1' hk2' [p' q'].
    exact (p' $@R' f', q' $@R' g').
  - intros ab1 ab2 ab3 ab4 fg1 fg2 fg3.
    intros ab1' ab2' ab3' ab4' [f1' g1'] [f2' g2'] [f3' g3'].
    exact (dcat_assoc f1' f2' f3', dcat_assoc g1' g2' g3').
  - intros ab1 ab2 fg ab1' ab2' [f' g'].
    exact (dcat_idl f', dcat_idl g').
  - intros ab1 ab2 fg ab1' ab2' [f' g'].
    exact (dcat_idr f', dcat_idr g').
Defined.
