(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Extensions Pullback.
Require Import ReflectiveSubuniverse Modality Accessible Localization.

Local Open Scope path_scope.
Local Open Scope subuniverse_scope.

(** * Descent between subuniverses *)

(** We study here a strengthening of the relation [O << O'] saying that [O]-modal type families descend along [O']-equivalences.  Pairs of reflective subuniverses with this relation share nearly all the properties of a reflective subuniverse [O] paired with its subuniverse [Sep O] of separated types (see [Separated.v]) and also many of those of a single left exact modality (see [Lex.v]).  Thus, many of the results herein generalize those of RSS for lex modalities and those of CORS for separated subuniverses.

Note that this kind of descent is not the same as the "modal descent" of Cherubini and Rijke.  When we get around to formalizing that, we may need to worry about disambiguating the names. *)

(** ** Definitions *)

(** This definition is an analogue of the statement of Lemma 2.19 of CORS, and of Theorem 3.1(xiii) of RSS.  Note that CORS Lemma 2.19 includes uniqueness of the extension, which we don't assert explicitly.  However, uniqueness follows from the [ReflectsD] parameter -- see [ooextendable_TypeO_lex_leq] below. *)
Class Descends@{i} (O' O : Subuniverse@{i}) (T : Type@{i})
      `{ReflectsD@{i} O' O T} :=
{
  OO_descend :
    forall (P : T -> Type@{i}) {P_inO : forall x, In O (P x)},
      O_reflector O' T -> Type@{i} ;
  OO_descend_inO :
    forall (P : T -> Type@{i}) {P_inO : forall x, In O (P x)} (x : O_reflector O' T),
      In O (OO_descend P x) ;
  OO_descend_beta :
    forall (P : T -> Type@{i}) {P_inO : forall x, In O (P x)} (x : T),
      OO_descend P (to O' T x) <~> P x ;
}.

Global Existing Instance OO_descend_inO.
Arguments OO_descend O' O {T _ _ _} P {P_inO} x.
Arguments OO_descend_inO O' O {T _ _ _} P {P_inO} x.
Arguments OO_descend_beta O' O {T _ _ _} P {P_inO} x.

Class O_lex_leq (O1 O2 : ReflectiveSubuniverse) `{O1 << O2} :=
  O_lex_leq_descends : forall A, Descends O2 O1 A.

Notation "O1 <<< O2" := (O_lex_leq O1 O2) (at level 70) : subuniverse_scope.
Global Existing Instance O_lex_leq_descends.

(** Unfortunately, it seems that generalizing binders don't work on notations: writing [`{O <<< O'}] doesn't automatically add the precondition [O << O'], although writing [`{O_lex_leq O O'}] does. *)

Definition O_lex_leq_eq {O1 O2 O3 : ReflectiveSubuniverse}
           `{O1 <=> O2} `{O2 << O3, O2 <<< O3}
           (Hstrong := O_strong_leq_trans_l O1 O2 O3)
  : O1 <<< O3.
Proof.
  intros A; unshelve econstructor; intros P P_inO1.
  all:pose (P_inO2 := fun x => inO_leq O1 O2 _ (P_inO1 x)).
  - apply (OO_descend O3 O2 P).
  - intros x; apply (inO_leq O2 O1), (OO_descend_inO O3 O2 P).
  - apply (OO_descend_beta O3 O2 P).
Defined.

(** ** Left exactness properties *)

(** We prove analogues of the properties in section 2.4 of CORS and Theorem 3.1 of RSS, but in a different order, with different proofs, to increase the generality.  The proofs in CORS use Proposition 2.26 for everything else, but it seems that most of the other results are true in the generality of two reflective subuniverses with [O <<< O'], so we give different proofs for some of them.  (To show that this generality is non-spurious, note that a lex modality [O] satisfies [O <<< O], but does not generally coincide with [Sep O].)

In the case of a single modality, most of these statements are equivalent to lex-ness (as stated in Theorem 3.1 of RSS).  We do not know if anything similar is true more generally. *)

Section LeftExactness.
Context (O' O : ReflectiveSubuniverse) `{O << O', O <<< O'}.

(** Proposition 2.30 of CORS and Theorem 3.1(xii) of RSS: any [O']-equivalence is [O]-connected.  The special case when [f = to O' A] requires only [O << O'], but the general case seems to require [O <<< O']. *)
Global Instance conn_map_OO_inverts
       {A B : Type} (f : A -> B) `{O_inverts O' f}
  : IsConnMap O f.
Proof.
  apply conn_map_from_extension_elim.
  intros P P_inO.
  assert (E : ExtendableAlong 1%nat f P); [ | exact (fst E) ].
  assert (Qp := OO_descend_beta O' O P).
  assert (Q_inO := OO_descend_inO O' O P).
  set (Q := OO_descend O' O P) in *.
  refine (extendable_postcompose' _ (Q o to O' B) P f Qp _).
  refine (cancelL_extendable _ Q f (to O' B) _ _).
  1:srapply (extendable_conn_map_inO O).
  refine (extendable_homotopic _ _ (O_functor O' f o to O' A) (to_O_natural O' f) _).
  srapply extendable_compose.
  1:srapply extendable_equiv.
  srapply (extendable_conn_map_inO O).
Defined.

(** A generalization of Lemma 2.27 of CORS: [functor_sigma] of a family of [O]-equivalences over an [O']-equivalence is an [O]-equivalence.  CORS Lemma 2.27 is the case when [f = to O' A] and [g] is a family of identities. *)
Definition OO_inverts_functor_sigma 
       {A B : Type} {P : A -> Type} {Q : B -> Type}
       (f : A -> B) (g : forall a, P a -> Q (f a))
       `{O_inverts O' f} `{forall a, O_inverts O (g a)}
  : O_inverts O (functor_sigma f g).
Proof.
  srapply isequiv_homotopic'.
  - refine (equiv_O_sigma_O O _ oE _ oE (equiv_O_sigma_O O _)^-1).
    refine (Build_Equiv _ _ (O_functor O (functor_sigma f (fun x => O_functor O (g x)))) _).
  - apply O_indpaths. intros [x u]; cbn.
    rewrite !to_O_natural, O_rec_beta; cbn.
    rewrite !to_O_natural, O_rec_beta.
    reflexivity.
Defined.

(** Families of [O]-modal types descend along all [O']-equivalences (not just the [O']-units, as asserted in the definition of [<<<]. *)
Definition OO_descend_O_inverts
           {A B : Type} (f : A -> B) `{O_inverts O' f}
           (P : A -> Type) {P_inO : forall x, In O (P x)}
  : B -> Type.
Proof.
  intros b.
  pose (Q := OO_descend O' O P).
  exact (Q ((O_functor O' f)^-1 (to O' B b))).
Defined.

Global Instance OO_descend_O_inverts_inO
       {A B : Type} (f : A -> B) `{O_inverts O' f}
       (P : A -> Type) {P_inO : forall x, In O (P x)} (b : B)
  : In O (OO_descend_O_inverts f P b)
  := _.

Definition OO_descend_O_inverts_beta
           {A B : Type} (f : A -> B) `{O_inverts O' f}
           (P : A -> Type) {P_inO : forall x, In O (P x)} (a : A)
  : (OO_descend_O_inverts f P (f a)) <~> P a.
Proof.
  unfold OO_descend_O_inverts.
  refine (OO_descend_beta O' O P a oE _).
  assert (p := (to_O_natural O' f a)^).
  apply moveR_equiv_V in p.
  exact (equiv_transport _ _ _ p).
Defined.

(** Morally, an equivalent way of saying [O <<< O'] is that the universe of [O]-modal types is [O']-modal.  We can't say this directly since this type lives in a higher universe, but here is a rephrasing of it. *)
Definition ooextendable_TypeO_lex_leq `{Univalence}
           {A B : Type} (f : A -> B) `{O_inverts O' f}
  : ooExtendableAlong f (fun _ => Type_ O).
Proof.
  (** It suffices to show that maps into [Type_ O] extend along [f], and that sections of families of equivalences are [ooExtendableAlong] it.  However, due to the implementation of [ooExtendableAlong], we have to prove the first one twice (there should probably be a general cofixpoint lemma for this). *)
  intros [|[|n]];
    [ exact tt
    | split; [ intros P | intros; exact tt ]
    | split; [ intros P | ] ].
  (** The first follows from what we just proved. *)
  1-2:exists (fun x => (OO_descend_O_inverts f P x ;
                        OO_descend_O_inverts_inO f P x)).
  1-2:intros x; apply path_TypeO, path_universe_uncurried; cbn. 
  1-2:exact (OO_descend_O_inverts_beta f P x).
  (** The second follows from the fact that the type of equivalences between two [O]-modal types is [O]-modal. *)
  intros P Q; rapply (ooextendable_postcompose' (fun b => P b <~> Q b)).
  - intros x; refine (equiv_path_TypeO _ _ _ oE equiv_path_universe _ _).
  - (** Typeclass inference spins on [rapply], I don't know why. *)
    apply (ooextendable_conn_map_inO O); exact _.
Defined.  

(** We can also state it in terms of belonging to a subuniverse if we lift [O'] accessibly (an analogue of Theorem 3.11(iii) of RSS). *)
Global Instance inO_TypeO_lex_leq `{Univalence} `{IsAccRSU O'}
  : In (lift_accrsu O') (Type_ O)
  := fun i => ooextendable_TypeO_lex_leq (acc_lgen O' i).

(** If [f] is an [O']-equivalence, then [ap f] is an [O]-equivalence. *)
Global Instance OO_inverts_ap
       {A B : Type} (f : A -> B) `{O_inverts O' f} (x y : A)
  : O_inverts O (@ap _ _ f x y).
Proof.
  assert (Pb := OO_descend_O_inverts_beta f (fun y:A => O (x = y))).
  assert (P_inO := OO_descend_O_inverts_inO f (fun y:A => O (x = y))).
  set (P := OO_descend_O_inverts f (fun y:A => O (x = y))) in *.
  clearbody P; cbn in *.
  srapply isequiv_adjointify.
  - intros q.
    pose (t := fun p => @transport B P (f x) (f y) p ((Pb x)^-1 (to O (x = x) 1))).
    exact (Pb y (O_rec t q)).
  - apply O_indpaths; intros p; cbn.
    rewrite O_rec_beta.
    assert (g := extension_conn_map_elim O (functor_sigma f (fun (a:A) (p:P (f a)) => p))
                                         (fun bp => O (f x = bp.1)) (fun u => O_functor O (ap f) (Pb u.1 u.2))). 
    pose (g1 b p := g.1 (b;p)). cbn in g1.
    assert (e : (fun u => g1 u.1 u.2) == g.1). 
    1:intros [a b]; reflexivity.
    assert (g2 := fun a p => e _ @ g.2 (a;p)); cbn in g2.
    refine ((g2 y _)^ @ _).
    rewrite (ap_transport p g1).
    rewrite (g2 x ((Pb x)^-1 (to O (x = x) 1))).
    rewrite eisretr, to_O_natural; cbn.
    rewrite <- (ap_transport p (fun b => to O (f x = b))).
    apply ap.
    rewrite transport_paths_r.
    apply concat_1p.
  - apply O_indpaths; intros p; cbn.
    rewrite to_O_natural, O_rec_beta.
    destruct p; cbn.
    srapply eisretr.
Defined.

Definition equiv_O_functor_ap_OO_inverts
       {A B : Type} (f : A -> B) `{O_inverts O' f} (x y : A)
  : O (x = y) <~> O (f x = f y)
  := Build_Equiv _ _ (O_functor O (ap f)) _.

(** Theorem 3.1(i) of RSS: path-spaces of [O']-connected types are [O]-connected. *)
Definition OO_isconnected_paths
           {A : Type} `{IsConnected O' A} (x y : A)
  : IsConnected O (x = y).
Proof.
  rapply (contr_equiv' _ (equiv_O_functor_ap_OO_inverts (const tt) x y)^-1).
Defined.  

(** Proposition 2.26 of CORS and Theorem 3.1(ix) of RSS; also generalizes Theorem 7.3.12 of the book.  Here we need to add the extra assumption that [O' <= Sep O], which is satisfied when [O' = Sep O] but also when [O] is lex and [O' = O].  That some such extra hypothesis is necessary can be seen from the fact that [Tr (-2) <<< O'] for any [O'], whereas this statement is certainly not true in that generality. *)
Definition path_OO `{O' <= Sep O}
           {X : Type@{i}} (x y : X)
  : O (x = y) -> (to O' X x = to O' X y).
Proof.
  nrefine (O_rec (O := O) (@ap X (O' X) (to O' X) x y)).
  - rapply (@inO_leq O' (Sep O)).
  - exact _.
Defined.

Global Instance isequiv_path_OO `{O' <= Sep O}
       {X : Type@{i}} (x y : X)
  : IsEquiv (path_OO x y).
Proof.
  nrefine (isequiv_O_rec_O_inverts O _).
  (** Typeclass search can find this, but it's quicker (and may help the reader) to give it explicitly. *)
  apply (OO_inverts_ap (to O' X)).
Defined.

Definition equiv_path_OO `{O' <= Sep O}
           {X : Type@{i}} (x y : X)
  : O (x = y) <~> (to O' X x = to O' X y)
  := Build_Equiv _ _ (path_OO x y) _.

(** [functor_hfiber] on a pair of [O']-equivalences is an [O]-equivalence. *)
Global Instance OO_inverts_functor_hfiber
       {A B C D : Type} {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
       (p : k o f == g o h) (b : B)
       `{O_inverts O' h, O_inverts O' k}
  : O_inverts O (functor_hfiber p b).
Proof.
  unfold functor_hfiber.
  simple notypeclasses refine (OO_inverts_functor_sigma _ _).
  1:exact _.
  intros a; cbn.
  refine (isequiv_homotopic (O_functor O (concat (p a)^) o O_functor O (@ap _ _ k (f a) b)) _).
  symmetry; apply O_functor_compose.
Defined.

(** Corollary 2.29 of CORS: [O'] preserves fibers up to [O]-equivalence. *)
Global Instance OO_inverts_functor_hfiber_to_O
       {Y X : Type} (f : Y -> X) (x : X)
  : O_inverts O (functor_hfiber (fun a => (to_O_natural O' f a)^) x).
Proof.
  (** Typeclass search can find this, but it's faster to give it explicitly. *)
  exact (OO_inverts_functor_hfiber _ _).
Defined.

Definition equiv_OO_functor_hfiber_to_O
           {Y X : Type@{i} } (f : Y -> X) (x : X)
  : O (hfiber f x) <~> O (hfiber (O_functor O' f) (to O' X x))
  := Build_Equiv _ _ _ (OO_inverts_functor_hfiber_to_O f x).

(** Theorem 3.1(iii) of RSS: any map between [O']-connected types is [O]-connected.  (Part (ii) is just the version for dependent projections.) *)
Definition OO_conn_map_isconnected
       {Y X : Type} `{IsConnected O' Y, IsConnected O' X} (f : Y -> X)
  : IsConnMap O f.
Proof.
  intros x; rapply (contr_equiv' _ (equiv_OO_functor_hfiber_to_O f x)^-1).
Defined.

Definition OO_isconnected_hfiber
       {Y X : Type} `{IsConnected O' Y, IsConnected O' X} (f : Y -> X) (x : X)
  : IsConnected O (hfiber f x)
  := OO_conn_map_isconnected f x.

(** Theorem 3.1(iv) of RSS: an [O]-modal map between [O']-connected types is an equivalence. *)
Global Instance OO_isequiv_mapino_isconnected
       {Y X : Type} `{IsConnected O' Y, IsConnected O' X} (f : Y -> X) `{MapIn O _ _ f}
  : IsEquiv f.
Proof.
  apply (isequiv_conn_ino_map O).
  - apply OO_conn_map_isconnected.
  - assumption.
Defined.

(** Theorem 3.1(vi) of RSS (and part (v) is just the analogue for dependent projections). *)
Definition OO_conn_map_functor_hfiber {A B C D : Type}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           `{IsConnMap O' _ _ h, IsConnMap O' _ _ k}
           (p : k o f == g o h) (b : B)
  : IsConnMap O (functor_hfiber p b).
Proof.
  intros [c q].
  nrefine (isconnected_equiv' O _ (hfiber_functor_hfiber p b c q)^-1 _).
  apply OO_isconnected_hfiber.
Defined.

(** An enhancement of Corollary 2.29 of CORS, corresponding to Theorem 3.1(viii) of RSS: when [O'] is a modality, the map between fibers is not just an O-equivalence but is O-connected. *)
Global Instance OO_conn_map_functor_hfiber_to_O `{IsModality O'}
       {Y X : Type} (f : Y -> X) (x : X)
  : IsConnMap O (functor_hfiber (fun y => (to_O_natural O' f y)^) x).
Proof.
  apply OO_conn_map_functor_hfiber.
Defined.

(** Theorem 3.1(vii) of RSS *)
Definition OO_ispullback_connmap_mapino
           {A B C D : Type} {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           `{O_inverts O' h, O_inverts O' k, MapIn O _ _ f, MapIn O _ _ g}
  : IsPullback p.
Proof.
  apply ispullback_isequiv_functor_hfiber; intros b.
  apply (isequiv_O_inverts O).
  apply OO_inverts_functor_hfiber; exact _.
Defined.

(** [functor_pullback] on a triple of [O']-equivalences is an [O]-equivalence. *)
Global Instance OO_inverts_functor_pullback
       {A1 B1 C1 A2 B2 C2 : Type}
       (f1 : B1 -> A1) (g1 : C1 -> A1)
       (f2 : B2 -> A2) (g2 : C2 -> A2)
       (h : A1 -> A2) (k : B1 -> B2) (l : C1 -> C2)
       (p : f2 o k == h o f1) (q : g2 o l == h o g1)
       `{O_inverts O' h, O_inverts O' k, O_inverts O' l}
  : O_inverts O (functor_pullback f1 g1 f2 g2 h k l p q).
Proof.
  unfold functor_pullback.
  simple notypeclasses refine (OO_inverts_functor_sigma _ _).
  1:exact _.
  intros b1; cbn.
  simple notypeclasses refine (OO_inverts_functor_sigma _ _).
  1:exact _.
  intros c1; cbn.
  pose @isequiv_compose. (* Speed up typeclass search. *)
  refine (isequiv_homotopic (O_functor O (fun r => r @ (q c1)^) o O_functor O (concat (p b1)) o O_functor O (@ap _ _ h (f1 b1) (g1 c1))) _).
  intros r; symmetry. 
  refine (_ @ _).
  2:apply O_functor_compose.
  cbn; srapply O_functor_compose.
Defined.

(** Proposition 2.28 of CORS, and Theorem 3.1(x) of RSS: the functor [O'] preserves pullbacks up to [O]-equivalence. *)
Global Instance OO_inverts_functor_pullback_to_O
       {A B C : Type} (f : B -> A) (g : C -> A)
  : O_inverts O (functor_pullback f g (O_functor O' f) (O_functor O' g)
                                  (to O' A) (to O' B) (to O' C)
                                  (to_O_natural O' f) (to_O_natural O' g)).
Proof.
  apply OO_inverts_functor_pullback; exact _.
Defined.

Definition equiv_OO_pullback {A B C : Type} (f : B -> A) (g : C -> A)
  : O (Pullback f g) <~> O (Pullback (O_functor O' f) (O_functor O' g))
  := Build_Equiv _ _ _ (OO_inverts_functor_pullback_to_O f g).

(** The "if" direction of CORS Proposition 2.31, and the nontrivial part of Theorem 3.1(xi) of RSS.  Note that we could also deduce Theorem 3.1(iii) of RSS from this. *)
Definition OO_cancelL_conn_map
           {Y X Z : Type} (f : Y -> X) (g : X -> Z)
           `{IsConnMap O' _ _ (g o f)} `{IsConnMap O' _ _ g}
  : IsConnMap O f.
Proof.
  apply conn_map_OO_inverts.
  nrapply (cancelL_isequiv (O_functor O' g)).
  1:exact _.
  rapply (isequiv_homotopic _ (O_functor_compose O' f g)).
Defined.

End LeftExactness.

(** Here's the "only if" direction of CORS Proposition 2.31.  Note that the hypotheses are different from those of the "if" direction, and the proof is shorter than the one given in CORS. *)
Definition OO_cancelR_conn_map
       (O' O : ReflectiveSubuniverse) `{O <= O', O' <= Sep O}
       {Y X Z : Type} (f : Y -> X) (g : X -> Z)
       `{IsConnMap O' _ _ (g o f)} `{IsConnMap O _ _ f}
  : IsConnMap O' g.
Proof.
  apply conn_map_from_extension_elim.
  intros P P_inO h.
  exists (conn_map_elim O' (g o f) P (h o f)).
  nrefine (conn_map_elim O f _ _); [ exact _ | .. ].
  - intros x.
    pose proof (fun z => inO_leq O' (Sep O) (P z) (P_inO z)).
    exact _.
  - intros y.
    apply (conn_map_comp O' (g o f)).
Defined.

Definition OO_isconnected_from_conn_map
       (O' O : ReflectiveSubuniverse) `{O <= O', O' <= Sep O}
       {Y X : Type} (f : Y -> X)
       `{IsConnected O' Y} `{IsConnMap O _ _ f}
  : IsConnected O' X.
Proof.
  apply isconnected_conn_map_to_unit.
  apply (OO_cancelR_conn_map O' O f (const tt)).
Defined.

(** An interesting scholium to Proposition 2.31. *)
Definition OO_inverts_conn_map_factor_conn_map
       (O' O : ReflectiveSubuniverse) `{O << O', O <<< O', O' <= Sep O}
       {Y X Z : Type} (f : Y -> X) (g : X -> Z)
       `{IsConnMap O' _ _ (g o f)} `{IsConnMap O _ _ f}
  : O_inverts O' f.
Proof.
  nrapply (cancelL_isequiv (O_functor O' g)).
  - apply O_inverts_conn_map.
    apply (OO_cancelR_conn_map O' O f g).
  - rapply (isequiv_homotopic _ (O_functor_compose O' f g)).
Defined.

Definition OO_inverts_conn_map_isconnected_domain
       (O' O : ReflectiveSubuniverse) `{O << O', O <<< O', O' <= Sep O}
       {Y X : Type} (f : Y -> X)
       `{IsConnected O' Y} `{IsConnMap O _ _ f}
  : O_inverts O' f.
Proof.
  apply (OO_inverts_conn_map_factor_conn_map O' O f (const tt)).
Defined.

(** Here is the converse of [ooextendable_TypeO_lex_leq]. *)
Definition O_lex_leq_extendable_TypeO
           (O' O : ReflectiveSubuniverse) `{O << O'}
           (e : forall (A:Type) (g:A->Type_ O), ExtensionAlong (to O' A) (fun _ => Type_ O) g)
  : O <<< O'.
Proof.
  intros A; unshelve econstructor; intros P' P_inO; pose (P := fun x => (P' x ; P_inO x) : Type_ O).
  - exact (fun x => ((e A P).1 x).1).
  - exact (fun x => ((e A P).1 x).2).
  - intros x.
    apply equiv_path.
    exact (((e A P).2 x)..1).
Defined.

(** And a version for the accessible case. *)
Definition O_lex_leq_inO_TypeO
           (O' O : ReflectiveSubuniverse) `{O << O'}
           `{IsAccRSU O'} `{In (lift_accrsu O') (Type_ O)}
  : O <<< O'.
Proof.
  apply O_lex_leq_extendable_TypeO.
  intros A g.
  assert (O_inverts (lift_accrsu O') (to O' A)).
  - rapply (O_inverts_O_leq' (lift_accrsu O') O').
  - exact (fst (ooextendable_O_inverts (lift_accrsu O') (to O' A) (Type_ O) 1%nat) g).
Defined.
