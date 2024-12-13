(** * Injective Types *)

(** Formalization of the paper: Injective Types in Univalent Mathematics by Martin Escardo (with some extra results). *)

Require Import Basics Types.
Require Import Truncations.Core.
Require Import Modalities.Modality.
Require Import HFiber.
Require Import Universes.HProp.
Require Import Constant.
Require Import ExcludedMiddle.
Require Import InjectiveTypes.TypeFamKanExt.

(** ** Definitions of injectivity and first examples *)

(** Since the universe levels are important to many of the results here, we keep track of them explicitly as much as possible. Due to our inability to use the max and successor operations within proofs, we instead construct these universes and their associated posetal relations in the arguments of the functions. In universe declarations, we use [u], [v], [w], etc. as our typical universe variables. Our convention for the max of two universes [u] and [v] is [uv], and the successor of a universe [u] is [su]. Occasionally we write [T] for a top universe which is strictly larger than all other provided universes. We hope that later versions of Coq will allow us access to the max and successor operations and much of the cumbersome universe handing here can be greatly reduced. *)

Section UniverseStructure.
  Universes u v w uv uw vw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw.

  Definition IsInjectiveType@{uvw | uv <= uvw, uw <= uvw, vw <= uvw} (D : Type@{w})
    := forall (X : Type@{u}) (Y : Type@{v}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j)
      (f : X -> D), merely@{uvw} (sig@{vw uw} (fun f' => f' o j == f)).

  Class IsAlgebraicInjectiveType@{} (D : Type@{w}) := {
    lift_ai {X : Type@{u}} {Y : Type@{v}} (j : X -> Y) {isem : IsEmbedding@{u v uv} j} (f : X -> D)
      : Y -> D;
    is_ext_ai {X : Type@{u}} {Y : Type@{v}} (j : X -> Y) {isem} f
      : lift_ai j f o j == f;
  }.

  (** Contractible types are algebraically injective. *)
  Global Instance alg_inj_contr@{} (D : Type@{w}) (cD : Contr D)
    : IsAlgebraicInjectiveType@{} D.
  Proof.
    snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
    - exact (const (center D)).
    - intros x.
      exact (contr _).
  Defined.

  (** [Empty] is not algebraically injective. *)
  Definition not_alg_inj_empty@{}
    : IsAlgebraicInjectiveType@{} Empty -> Empty.
  Proof.
    intros Eai.
    refine (lift_ai (Empty_rec@{v}) idmap tt).
    apply istruncmap_mapinO_tr.
    rapply mapinO_between_inO@{uv u v uv}.
  Defined.

End UniverseStructure.

(** [Type@{uv}] is algebraically [u],[v]-injective in at least two ways. *)
Definition alg_inj_Type_sigma@{u v uv suv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv} Type@{uv}.
Proof.
  snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
  - exact (f <| j).
  - intros x.
    rapply isext_leftkanfam.
Defined.

Global Instance alg_inj_Type_forall@{u v uv suv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv} Type@{uv}.
Proof.
  snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
  - exact (f |> j).
  - intros x. 
    rapply isext_rightkanfam.
Defined.

(** ** Constructions with algebraically injective types *)

(** Retracts of algebraically injective types are algebraically injective. *)
Definition alg_inj_retract@{u v w w' uv uw vw uw' vw' | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, u <= uw', v <= vw', w' <= uw', w' <= vw'}
  {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
  (retr : r o s == idmap) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
  : IsAlgebraicInjectiveType@{u v w' uv uw' vw'} D'.
Proof.
  snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
  - exact (r o lift_ai _ (s o f)).
  - intros x. rhs_V apply (retr (f x)).
    exact (ap r (is_ext_ai _ (s o f) x)).
Defined.

Section UniverseStructure.
  Universes u v w t uv uw vw tw utw vtw.
  Constraint u <= uv, u <= uw, v <= vw, v <= uv, w <= uw, w <= vw, w <= tw, t <= tw,
    uw <= utw, vw <= vtw, tw <= utw, tw <= vtw.
  
  (** Dependent products are algebraically injective when all their factors are. *)
  Global Instance alg_inj_forall@{}
    `{Funext} {A : Type@{t}} (D : A -> Type@{w})
    (Dai : forall a, IsAlgebraicInjectiveType@{u v w uv uw vw} (D a))
    : IsAlgebraicInjectiveType@{u v tw uv utw vtw} (forall a, D a).
  Proof.
    snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
    - exact (fun y a => lift_ai _ (fun x => f x a) y).
    - intros x. funext a.
      exact (is_ext_ai _ (fun x => f x a) x).
  Defined.

  (** In particular, exponentials of algebraically injective types are algebraically injective. *)
  Definition alg_inj_arrow@{}
    `{Funext} {A : Type@{t}} {D : Type@{w}}
    (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicInjectiveType@{u v tw uv utw vtw} (A -> D)
    := _.

End UniverseStructure.

(** Algebraically injective types are retracts of any type that they embed into. *)
Definition retract_alg_inj_embedding@{v w vw | v <= vw, w <= vw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Dai : IsAlgebraicInjectiveType@{w v w vw w vw} D)
  : { r : Y -> D & r o j == idmap }
  := (lift_ai _ idmap; is_ext_ai _ idmap).

(** Any algebraically [u],[su]-injective type [X : Type@{u}], is a retract of [X -> Type@{u}]. *)
Definition retract_power_universe_alg_usuinj@{u su | u < su} `{Univalence}
  (D : Type@{u}) (Dai : IsAlgebraicInjectiveType@{u su u su u su} D)
  : { r : (D -> Type@{u}) -> D & r o (@paths D) == idmap }
  := retract_alg_inj_embedding D (@paths D) isembedding_paths Dai.

(** ** Algebraic flabbiness and resizing constructions *)
(** If [D : Type@{u}] is algebraically [u],[su]-injective, then it is algebraically [u],[u]-injective. *)
Definition alg_uuinj_alg_usu_inj@{u w su uw suw | u < su, u <= uw, w <= uw, su <= suw, w <= suw}
  (D : Type@{w}) (Dai : IsAlgebraicInjectiveType@{u su w su uw suw} D)
  : IsAlgebraicInjectiveType@{u u w u uw uw} D.
Proof.
  snrapply Build_IsAlgebraicInjectiveType.
  - exact (@lift_ai D Dai).
  - exact (@is_ext_ai D Dai).
Defined.
(** Note that this proof is easy because of cumulativity of [Type] (which is not assumed in the original paper). *)

(** Algebraic flabbiness is a variant of algebraic injectivity, but only ranging over embeddings of propositions into the unit type. *)
Class IsAlgebraicFlabbyType@{u w} (D : Type@{w}) := {
  center_af {P : HProp@{u}} (f : P -> D) : D;
  contr_af {P : HProp@{u}} (f : P -> D) (p : P) : center_af f = f p;
}.

(** Algebraic flabbiness of a type [D] is equivalent to the statement that all conditionally constant functions [X -> D] are constant. First we give the condition, and then the two implications. *)
Definition cconst_is_const_cond@{u w uw | u <= uw, w <= uw}
  (D : Type@{w})
  := forall (X : Type@{u}) (f : X -> D),
    ConditionallyConstant@{u w uw} f -> sig@{uw uw} (fun d => forall x, d = f x).

Definition alg_flab_cconst_is_const@{u w uw | u <= uw, w <= uw}
  (D : Type@{w}) (ccond : cconst_is_const_cond@{u w uw} D)
  : IsAlgebraicFlabbyType@{u w} D.
Proof.
  snrapply Build_IsAlgebraicFlabbyType; intros P f.
  - apply (ccond P f).
    apply (cconst_factors_hprop _ _ idmap f).
    reflexivity.
  - apply (ccond P f).
Defined.

Definition cconst_is_const_alg_flab@{u w uw | u <= uw, w <= uw}
  (D : Type@{w}) (Daf : IsAlgebraicFlabbyType@{u w} D)
  : cconst_is_const_cond@{u w uw} D.
Proof.
  intros X f [f' e].
  srefine (center_af f'; _).
  intros x.
  exact (contr_af f' (tr x) @ e x).
Defined.

(** Algebraic flabbiness is equivalent to algebraic injectivity, with appropriate choices of universes. *)
Section UniverseStructure.
  Universes u v w uv uw vw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw.

  (** Algebraically [u],[v]-injective types are algebraically [u]-flabby. *)
  Definition alg_flab_alg_inj@{}
    {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicFlabbyType@{u w} D.
  Proof.
    snrapply Build_IsAlgebraicFlabbyType; intros P f.
    - srapply (lift_ai _ f tt).
    - apply is_ext_ai.
  Defined.

  (** Algebraically [uv]-flabby types are algebraically [u],[v]-injective. *)
  Definition alg_inj_alg_flab@{}
    {D : Type@{w}} (Daf : IsAlgebraicFlabbyType@{uv w} D)
    : IsAlgebraicInjectiveType@{u v w uv uw vw} D.
  Proof.
    snrapply Build_IsAlgebraicInjectiveType; intros X Y j isem f.
    - intros y. exact (center_af (fun x : Build_HProp (hfiber j y) => f x.1)).
    - intros x. exact (contr_af _ (x; idpath (j x))).
  Defined.

End UniverseStructure.

(** By combining the above, we see that if [D] is algebraically [ut],[v]-injective, then it is algebraically [u],[t]-injective. *)
Definition resize_alg_inj@{u v w t ut uw vw tw uvt utw | u <= ut, u <= uw, v <= vw, v <= uvt, w <= uw, w <= vw, w <= tw, t <= ut, t <= tw,
                            ut <= uvt, ut <= utw, uw <= utw, tw <= utw}
  {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{ut v w uvt utw vw} D)
  : IsAlgebraicInjectiveType@{u t w ut uw tw} D.
Proof.
  apply alg_inj_alg_flab.
  exact (alg_flab_alg_inj Dai).
Defined.

(** We include two direct proofs of the algebraic flabbiness of [Type], instead of combining [alg_inj_alg_flab] with the previous proofs of algebraic injectivity, for better computations later. *)
Definition alg_flab_Type_sigma@{u su | u < su} `{Univalence}
  : IsAlgebraicFlabbyType@{u su} Type@{u}.
Proof.
  snrapply Build_IsAlgebraicFlabbyType; intros P A.
  - exact (sig@{u u} (fun p => A p)).
  - intros p.
    apply path_universe_uncurried.
    exact (@equiv_contr_sigma _ _ (contr_inhabited_hprop _ _)).
Defined.

Global Instance alg_flab_Type_forall@{u su | u < su} `{Univalence}
  : IsAlgebraicFlabbyType@{u su} Type@{u}.
Proof.
  snrapply Build_IsAlgebraicFlabbyType; intros P A.
  - exact (forall p : P, A p).
  - intros p.
    apply path_universe_uncurried.
    exact (@equiv_contr_forall _ _ (contr_inhabited_hprop _ _) _).
Defined.

(** ** Algebraic flabbiness with resizing axioms *)

Section AssumePropResizing.
  Context `{PropResizing}.

  (** Algebraic flabbiness is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_flab@{v u w}
    {D : Type@{w}} (Daf : IsAlgebraicFlabbyType@{v w} D)
    : IsAlgebraicFlabbyType@{u w} D.
  Proof.
    snrapply Build_IsAlgebraicFlabbyType; intros P f;
    pose (e := (equiv_smalltype@{v u} P));
    pose (PropQ := (@istrunc_equiv_istrunc _ _ e^-1 (-1) _)).
    - exact (center_af (f o e)).
    - intros p.
      lhs apply (contr_af (f o e) (e^-1 p)).
      apply ap.
      apply eisretr.
  Defined.

  (** Algebraic injectivity is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_inj@{u v w u' v' uv uw vw u'v' u'w v'w | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
                                            u' <= u'v', v' <= u'v', u' <= u'w, w <= u'w, v' <= v'w, w <= v'w}
    {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicInjectiveType@{u' v' w u'v' u'w v'w} D.
  Proof.
    apply alg_inj_alg_flab.
    apply universe_independent_alg_flab@{u u'v' w}.
    exact (alg_flab_alg_inj Dai).
  Defined.

  (** Any algebraically injective type [D : Type@{u}] is a retract of [X -> Type@{u}] with [X : Type@{u}]. This is a universe independent version of [retract_power_universe_alg_usuinj]. *)
  Definition retract_power_universe_alg_inj@{u su | u < su} `{Univalence}
    {D : Type@{u}} (Dai : IsAlgebraicInjectiveType@{u u u u u u} D)
    : exists (X : Type@{u}) (s : D -> (X -> Type@{u})) (r : (X -> Type@{u}) -> D), r o s == idmap.
  Proof.
    refine (D; _).
    refine (@paths D; _).
    apply (retract_power_universe_alg_usuinj D).
    exact (universe_independent_alg_inj@{u u u u su u u u su u su} Dai).
  Defined.

End AssumePropResizing.

(** Any retract of a type family [X -> Type@{u}] is algebraically injective. This is the opposite result as above, classifying algebraically injective types, independent of universes. It should be noted that this direction of the if and only if does not depend on propositional resizing. *)
Definition alg_inj_retract_power_universe@{u su | u < su}
  `{Univalence} (D : Type@{u}) {X : Type@{u}} {s : D -> (X -> Type@{u})}
  (r : (X -> Type@{u}) -> D) (retr : r o s == idmap)
  : IsAlgebraicInjectiveType@{u u u u u u} D.
Proof.
  apply (alg_inj_retract r retr).
  rapply alg_inj_arrow.
Defined.

(** ** Injectivity in terms of algebraic injectivity in the absence of resizing *)

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  (** Algebraically injective types are injective. *)
  Definition inj_alg_inj@{}
    (D : Type@{w}) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsInjectiveType@{u v w uv uw vw uvw} D.
  Proof.
    intros X Y j isem f.
    apply tr.
    exact (lift_ai _ _; is_ext_ai _ f).
  Defined.

  (** The propositional truncation of algebraic injectivity implies injectivity. *)
  Definition inj_merely_alg_inj@{T | uvw < T}
    `{Funext} {D : Type@{w}}
    (mDai : merely@{T} (IsAlgebraicInjectiveType@{u v w uv uw vw} D))
    : ((IsInjectiveType@{u v w uv uw vw uvw} D) : Type@{T}).
  Proof.
    revert mDai.
    nrapply Trunc_rec@{T T}. (* Manually stripping truncations so as to control universe variables. *)
    - repeat (nrapply istrunc_forall@{T T T}; intro).
      apply istrunc_truncation.
    - intro Dai.
      exact (inj_alg_inj@{} D Dai).
  Defined.

  (** A retract of an injective type is injective. *)
  Definition inj_retract@{w' uw' vw' uvw' T | u <= uw', v <= vw', w' <= uw', w' <= vw', uv <= uvw', uw' <= uvw', vw' <= uvw', uvw < T, uvw' < T}
    `{Funext} {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
    (retr : r o s == idmap) (Di : IsInjectiveType@{u v w uv uw vw uvw} D)
    : IsInjectiveType@{u v w' uv uw' vw' uvw'} D'.
  Proof.
    intros X Y j isem f.
    specialize (Di X Y j isem (s o f)).
    revert Di.
    rapply Trunc_rec@{T T}.
    intros [g e].
    apply tr.
    snrefine (r o g; _).
    intros x.
    rhs_V apply (retr (f x)).
    exact (ap r (e x)).
  Defined.

End UniverseStructure.

(** Injective types are retracts of any type that they embed into, in an unspecified way. *)
Definition merely_retract_inj_embedding@{v w vw svw | v <= vw, w <= vw, vw < svw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Di : IsInjectiveType@{w v w vw w vw vw} D)
  : merely@{svw} { r : Y -> D & r o j == idmap }
  := Di _ _ _ _ idmap.

(** The power of an injective type is injective. *)
Definition inj_arrow@{u v w t uv ut vt tw uvt utw vtw utvw | u <= uv, v <= uv, u <= ut, t <= ut, v <= vt, t <= vt, t <= tw, w <= tw,
                        uv <= uvt, ut <= uvt, vt <= uvt, ut <= utw, tw <= utw, vt <= vtw, tw <= vtw, uvt <= utvw, utw <= utvw, vtw <= utvw}
  `{Funext} {A : Type@{t}} (D : Type@{w})
  (Di : IsInjectiveType@{ut vt w uvt utw vtw utvw} D)
  : IsInjectiveType@{u v tw uv utw vtw utvw} (A -> D).
Proof.
  intros X Y j isem f.
  assert (embId : IsEmbedding (fun a : A => a)) by rapply istruncmap_mapinO_tr.
  pose proof (mD := Di (X * A) (Y * A) (functor_prod j equiv_idmap)
    (istruncmap_functor_prod@{u v t t ut vt uvt uvt uv t} _ _ _) (uncurry f)).
  revert mD.
  rapply Trunc_rec@{utvw utvw}.
  intros [g e].
  apply tr.
  refine (fun y a => g (y, a); _).
  intros x. funext a.
  exact (e (x, a)).
Defined.

(** Any [u],[su]-injective type [X : Type@{u}], is a retract of [X -> Type@{u}] in an unspecified way. *)
Definition merely_retract_power_universe_inj@{u su ssu | u < su, su < ssu}
  `{Univalence} (D : Type@{u}) (Di : IsInjectiveType@{u su u su u su su} D)
  : merely@{su} (sig@{su su} (fun r => r o (@paths D) == idmap))
  := merely_retract_inj_embedding D (@paths D) isembedding_paths Di.

(** Inverse of [inj_merely_alg_inj] modulo universes. *)
Definition merely_alg_inj_inj@{u su ssu | u < su, su < ssu} `{Univalence}
  (D : Type@{u}) (Di : IsInjectiveType@{u su u su u su su} D)
  : merely@{su} (IsAlgebraicInjectiveType@{u u u u u u} D).
Proof.
  srefine (Trunc_functor (-1) _ (merely_retract_power_universe_inj D Di)).
  intros [r retr].
  exact (alg_inj_retract_power_universe D r retr).
Defined.

(** ** The equivalence of excluded middle with the (algebraic) injectivity of pointed types *)

(** Assuming excluded middle, all pointed types are algebraically flabby (and thus algebraically injective). *)
Definition alg_flab_pointed_lem@{u w}
  `{ExcludedMiddle} {D : Type@{w}} (d : D)
  : IsAlgebraicFlabbyType@{u w} D.
Proof.
  snrapply Build_IsAlgebraicFlabbyType; intros P f.
  - destruct (LEM P _) as [p | np].
    + exact (f p).
    + exact d.
  - cbn.  intros q.
    destruct (LEM P _) as [p | np].
    + exact (ap f (path_ishprop _ _)).
    + exact (Empty_rec (np q)).
Defined.

(** If the type [P + ~P + Unit] is algebraically flabby for [P] a proposition, then [P] is decidable. *)
Definition decidable_alg_flab_hprop@{w} `{Funext} (P : HProp@{w})
  (Paf : IsAlgebraicFlabbyType@{w w} ((P + ~P) + (Unit : Type@{w})))
  : Decidable P.
Proof.
  pose (inl' := inl : P + ~P -> (P + ~P) + (Unit : Type@{w})).
  assert (l : {d : (P + ~P) + (Unit : Type@{w}) & forall z, d = inl' z}).
  { refine (center_af _; contr_af inl'). rapply ishprop_decidable_hprop@{w w}. }
  destruct l as [[s | u] l2].
  - exact s.
  - assert (np := fun p => inl_ne_inr _ _ (l2 (inl p))^).
    assert (nnp := fun np' => inl_ne_inr _ _ (l2 (inr np'))^).
    exact (Empty_rec (nnp np)).
Defined.

(** If all pointed types are algebraically flabby, then excluded middle holds. *)
Definition lem_pointed_types_alg_flab@{w} `{Funext}
  (ptaf: forall (D : Type@{w}), D -> IsAlgebraicFlabbyType@{w w} D)
  : ExcludedMiddle_type@{w}.
Proof.
  intros P PropP.
  apply (decidable_alg_flab_hprop (@Build_HProp P PropP)).
  apply ptaf.
  exact (inr tt).
Defined.
