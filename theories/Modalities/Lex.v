(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Extensions Pullback NullHomotopy Factorization PathAny.
Require Import Modality Accessible Localization Descent Separated.

Local Open Scope path_scope.
Local Open Scope subuniverse_scope.

(** * Lex modalities *)

(** A lex modality is one that preserves finite limits, or equivalently pullbacks.  Many equivalent characterizations of this can be found in Theorem 3.1 of RSS.

We choose as our definition that a lex modality to be a reflective subuniverse such that [O <<< O], which is close to (but not quite the same as) RSS Theorem 3.1 (xiii).

Note that since this includes [O << O] as a precondition, such an [O] must indeed be a modality (and since modalities coerce to reflective subuniverses, in the following notation [O] could be either an element of [ReflectiveSubuniverse] or of [Modality]). *)
Notation Lex O := (O <<< O).

(** ** Properties of lex modalities *)

(** We now show that lex modalities have all the other properties from RSS Theorem 3.1 (which are equivalent to lex-ness).  All of them are simple specializations of properties from [Descent.v] to the case [O' = O] (although in the general case they are not known to be equivalent). *)
Section LexModality.
  Context (O : Modality) `{Lex O}.

  (** RSS Theorem 3.1 (i) *)
  Definition isconnected_paths
             {A : Type} `{IsConnected O A} (x y : A)
    : IsConnected O (x = y)
    := OO_isconnected_paths O O x y.

  (** RSS Theorem 3.1 (iii) *)
  Definition conn_map_lex
             {Y X : Type} `{IsConnected O Y, IsConnected O X} (f : Y -> X)
    : IsConnMap O f
    := OO_conn_map_isconnected O O f.

  (** RSS Theorem 3.1 (iv) *)
  Global Instance isequiv_mapino_isconnected
         {Y X : Type} `{IsConnected O Y, IsConnected O X}
         (f : Y -> X) `{MapIn O _ _ f}
    : IsEquiv f
    := OO_isequiv_mapino_isconnected O O f.

  (** RSS Theorem 3.1 (vi) *)
  Definition conn_map_functor_hfiber {A B C D : Type}
             {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
             `{IsConnMap O _ _ h, IsConnMap O _ _ k}
             (p : k o f == g o h) (b : B)
    : IsConnMap O (functor_hfiber p b)
    := OO_conn_map_functor_hfiber O O p b.

  (** RSS Theorem 3.1 (vii) *)
  Definition ispullback_connmap_mapino_commsq
             {A B C D : Type} {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
             (p : k o f == g o h)
             `{O_inverts O h, O_inverts O k, MapIn O _ _ f, MapIn O _ _ g}
    : IsPullback p
    := OO_ispullback_connmap_mapino O O p.

  (** RSS Theorem 3.1 (viii) *)
  Global Instance conn_map_functor_hfiber_to_O
         {Y X : Type} (f : Y -> X) (x : X)
    : IsConnMap O (functor_hfiber (fun y => (to_O_natural O f y)^) x)
    := OO_conn_map_functor_hfiber_to_O O O f x.

  Global Instance isequiv_O_functor_hfiber
         {A B} (f : A -> B) (b : B)
    : IsEquiv (O_functor_hfiber O f b).
  Proof.
    apply (isequiv_O_rec_O_inverts O).
    apply O_inverts_conn_map.
    refine (conn_map_homotopic
              O (functor_hfiber (fun x => (to_O_natural O f x)^) b)
              _ _ _).
    intros [a p].
    unfold functor_hfiber, functor_sigma. apply ap.
    apply whiskerR, inv_V.
  Defined.

  Definition equiv_O_functor_hfiber
             {A B} (f : A -> B) (b : B)
    : O (hfiber f b) <~> hfiber (O_functor O f) (to O B b)
    := Build_Equiv _ _ (O_functor_hfiber O f b) _.

  (** RSS Theorem 3.1 (ix) *)
  Global Instance isequiv_path_O
         {X : Type@{i}} (x y : X)
    : IsEquiv (path_OO O O x y)
    := isequiv_path_OO O O x y.

  Definition equiv_path_O {X : Type@{i}} (x y : X)
    : O (x = y) <~> (to O X x = to O X y)
    := equiv_path_OO O O x y.

  (** RSS Theorem 3.1 (x).  This justifies the term "left exact". *)
  Global Instance O_inverts_functor_pullback_to_O
         {A B C : Type} (f : B -> A) (g : C -> A)
    : O_inverts O (functor_pullback f g (O_functor O f) (O_functor O g)
                                    (to O A) (to O B) (to O C)
                                    (to_O_natural O f) (to_O_natural O g))
    := OO_inverts_functor_pullback_to_O O O f g.

  Definition equiv_O_pullback {A B C : Type} (f : B -> A) (g : C -> A)
    : O (Pullback f g) <~> O (Pullback (O_functor O f) (O_functor O g))
    := equiv_OO_pullback O O f g.

  Definition O_functor_pullback
             {A B C : Type} (f : B -> A) (g : C -> A)
    : IsPullback (O_functor_square O _ _ _ _ (pullback_commsq f g)).
  Proof.
    unfold IsPullback.
    nrapply (isequiv_homotopic
               (O_rec (functor_pullback _ _ _ _ _ _ _
                                        (to_O_natural O f) (to_O_natural O g)))).
    1:apply isequiv_O_rec_O_inverts; exact _.
    apply O_indpaths; intros [b [c e]].
    refine (O_rec_beta _ _ @ _).
    (** This *seems* like it ought to be the easier goal, but it turns out to involve lots of naturality wrangling.  If we ever want to make real use of this theorem, we might want to separate out this goal into an opaque lemma so we could make the main theorem transparent. *)
    unfold functor_pullback, functor_sigma, pullback_corec; simpl.
    refine (path_sigma' _ (to_O_natural O pullback_pr1 (b;(c;e)))^ _).
    rewrite transport_sigma'; simpl.
    refine (path_sigma' _ (to_O_natural O pullback_pr2 (b;(c;e)))^ _).
    rewrite transport_paths_Fl.
    rewrite transport_paths_Fr.
    Open Scope long_path_scope.
    unfold O_functor_square.
    rewrite ap_V, inv_V, O_functor_homotopy_beta, !concat_p_pp.
    unfold pullback_commsq; simpl.
    rewrite to_O_natural_compose, !concat_pp_p.
    do 3 apply whiskerL.
    rewrite ap_V, <- inv_pp.
    rewrite <- (inv_V (O_functor_compose _ _ _ _)), <- inv_pp.
    apply inverse2, to_O_natural_compose.
    Close Scope long_path_scope.
  Qed.

  (** RSS Theorem 3.1 (xi) *)
  Definition cancelL_conn_map
             {Y X Z : Type} (f : Y -> X) (g : X -> Z)
             `{IsConnMap O _ _ (g o f)} `{IsConnMap O _ _ g}
    : IsConnMap O f
    := OO_cancelL_conn_map O O f g.

  (** RSS Theorem 3.1 (xii) *)
  Global Instance conn_map_O_inverts
         {A B : Type} (f : A -> B) `{O_inverts O f}
    : IsConnMap O f
    := conn_map_OO_inverts O O f.

  (** RSS Theorem 3.1 (xiii) *)
  Definition modal_over_connected_isconst_lex
             (A : Type) `{IsConnected O A}
             (P : A -> Type) `{forall x, In O (P x)}
    : {Q : Type & In O Q * forall x, Q <~> P x}.
  Proof.
    pose proof (O_inverts_isconnected O (fun _:A => tt)).
    exists (OO_descend_O_inverts O O (fun _:A => tt) P tt); split.
    - apply OO_descend_O_inverts_inO.
    - intros; rapply OO_descend_O_inverts_beta.
  Defined.  

  (** RSS Theorem 3.11 (iii): in the accessible case, the universe is modal. *)
  Global Instance inO_typeO_lex `{Univalence} `{IsAccRSU O}
    : In (lift_accrsu O) (Type_ O)
    := _.

  (** Part of RSS Corollary 3.9: lex modalities preserve [n]-types for all [n].  This is definitely not equivalent to lex-ness, since it is true for the truncation modalities that are not lex.  But it is also not true of all modalities; e.g. the shape modality in a cohesive topos can take 0-types to [oo]-types.  With a little more work, this can probably be proven without [Funext]. *)
  Global Instance istrunc_O_lex `{Funext}
         {n : trunc_index} {A : Type} `{IsTrunc n A}
    : IsTrunc n (O A).
  Proof.
    generalize dependent A; simple_induction n n IHn; intros A ?.
    - exact _.               (** Already proven for all modalities. *)
    - refine (O_ind (fun x => forall y, IsTrunc n (x = y)) _); intros x.
      refine (O_ind (fun y => IsTrunc n (to O A x = y)) _); intros y.
      refine (trunc_equiv _ (equiv_path_O x y)).
  Defined.

End LexModality.

(** ** Equivalent characterizations of lex-ness *)

(** We will not prove that *all* of the above properties from RSS Theorem 3.1 are equivalent to lex-ness, but we will do it for some of them. *)

Section ImpliesLex.
  Context {O : Modality}.

  (** RSS 3.1 (xiii) implies lexness *)
  Definition lex_from_modal_over_connected_isconst
             (H : forall (A : Type) (A_isC : IsConnected O A)
                         (P : A -> Type) (P_inO : forall x, In O (P x)),
                 {Q : Type & In O Q * forall x, Q <~> P x})
    : Lex O.
  Proof.
    intros A; unshelve econstructor; intros P P_inO.
    all:pose (Q := fun z:O A => H (hfiber (to O A) z) _ (P o pr1) _).
    - exact (fun z => (Q z).1).
    - exact (fun z => fst (Q z).2).
    - intros x; cbn.
      exact (snd (Q (to O A x)).2 (x;1)).
  Defined.

  (** RSS 3.11 (iii), the universe is modal, implies lex-ness *)
  Definition lex_from_inO_typeO `{IsAccRSU O} `{In (lift_accrsu O) (Type_ O)}
    : Lex O.
  Proof.
    apply (O_lex_leq_inO_TypeO O O).
  Defined.

  (** RSS Theorem 3.1 (xi) implies lex-ness *)
  Definition lex_from_cancelL_conn_map
             (cancel : forall {Y X Z : Type} (f : Y -> X) (g : X -> Z),
                 (IsConnMap O (g o f)) -> (IsConnMap O g)
                 -> IsConnMap O f)
    : Lex O.
  Proof.
    apply lex_from_modal_over_connected_isconst; intros.
    exists (O {x:A & P x}); split; [ exact _ | intros x; symmetry ].
    refine (Build_Equiv _ _ (fun p => to O _ (x ; p)) _).
    nrefine (isequiv_conn_map_ino O _). 1-2:exact _.
    revert x; apply conn_map_fiber.
    nrefine (cancel _ _ _ _ (fun z:{x:A & O {x : A & P x}} => z.2) _ _).
    1: clear cancel; exact _.
    intros z.
    refine (isconnected_equiv' O A _ _).
    unfold hfiber.
    refine (equiv_adjointify (fun x => ((x ; z) ; 1))
                             (fun y => y.1.1) _ _). 
    - intros [[x y] []]; reflexivity.
    - intros x; reflexivity.
  Defined.

  (** RSS Theorem 3.1 (iii) implies lex-ness *)
  Definition lex_from_conn_map_lex
             (H : forall A B (f : A -> B),
                 (IsConnected O A) -> (IsConnected O B) ->
                 IsConnMap O f)
    : Lex O.
  Proof.
    apply lex_from_cancelL_conn_map.
    intros Y X Z f g gfc gc x.
    pose (h := @functor_hfiber Y Z X Z (g o f) g f idmap (fun a => 1%path)).
    assert (cc := H _ _ (h (g x)) (gfc (g x)) (gc (g x))).
    refine (isconnected_equiv' O _ _ (cc (x;1))).
    unfold hfiber.
    subst h; unfold functor_hfiber, functor_sigma; cbn.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    apply equiv_functor_sigma_id; intros y; cbn.
    refine (_ oE (equiv_functor_sigma_id _)).
    2:intros; symmetry; apply equiv_path_sigma.
    cbn.
    refine (_ oE equiv_sigma_symm _).
    apply equiv_sigma_contr; intros p.
    destruct p; cbn.
    refine (contr_equiv' { p : g (f y) = g (f y) & p = 1%path } _).
    apply equiv_functor_sigma_id; intros p; cbn.
    apply equiv_concat_l.
    exact (concat_1p _ @ ap_idmap _).
  Defined.

  (** RSS Theorem 3.1 (i) implies lex-ness *)
  Definition lex_from_isconnected_paths
             (H : forall (A : Type) (Ac : IsConnected O A) (x y : A),
                 IsConnected O (x = y))
    : Lex O.
  Proof.
    apply lex_from_conn_map_lex.
    intros A B f Ac Bc c.
    rapply isconnected_sigma.
  Defined.

  (** RSS Theorem 3.1 (iv) implies lex-ness *)
  Definition lex_from_isequiv_ismodal_isconnected_types
             (H : forall A B (f : A -> B),
                 (IsConnected O A) -> (IsConnected O B) -> 
                 (MapIn O f) -> IsEquiv f)
    : Lex O.
  Proof.
    apply lex_from_conn_map_lex.
    intros A B f AC BC.
    apply (conn_map_homotopic O _ _ (fact_factors (image O f))).
    apply conn_map_compose; [ exact _ | ].
    apply conn_map_isequiv.
    apply H; [ | exact _ | exact _ ].
    apply isconnected_conn_map_to_unit.
    apply (cancelR_conn_map O (factor1 (image O f)) (const tt)).
  Defined.

  (** RSS Theorem 3.1 (vii) implies lex-ness *)
  Definition lex_from_ispullback_connmap_mapino_commsq
             (H : forall {A B C D}
                         (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D),
                 (IsConnMap O f) -> (IsConnMap O g) ->
                 (MapIn O h) -> (MapIn O k) ->
                 forall (p : k o f == g o h), IsPullback p)
    : Lex O.
  Proof.
    apply lex_from_isequiv_ismodal_isconnected_types.
    intros A B f AC BC fM.
    specialize (H A Unit B Unit (const tt) (const tt) f idmap _ _ _ _
                  (fun _ => 1)).
    unfold IsPullback, pullback_corec in H.
    refine (@isequiv_compose _ _ _ H _ (fun x => x.2.1) _).
    unfold Pullback.
    refine (@isequiv_compose _ {b:Unit & B}
                             (functor_sigma idmap (fun a => pr1))
                             _ _ pr2 _).
    refine (@isequiv_compose _ _ (equiv_sigma_prod0 Unit B)
                             _ _ snd _).
    apply (equiv_isequiv (prod_unit_l B)).
  Defined.

End ImpliesLex.

(** ** Lex reflective subuniverses *)

(** A reflective subuniverse that preserves fibers is in fact a modality (and hence lex). *)
Definition ismodality_isequiv_O_functor_hfiber (O : ReflectiveSubuniverse)
           (H : forall {A B : Type} (f : A -> B) (b : B),
               IsEquiv (O_functor_hfiber O f b))
  : IsModality O.
Proof.
  intros A'; rapply reflectsD_from_inO_sigma.
  intros B B_inO.
  pose (A := O A').
  pose (g := O_rec pr1 : O {x : A & B x} -> A).
  transparent assert (p : (forall x, g (to O _ x) = x.1)).
  { intros x; subst g; apply O_rec_beta. }
  apply inO_isequiv_to_O.
  apply isequiv_contr_map; intros x.
  snrefine (contr_equiv' _ (hfiber_hfiber_compose_map _ g x)).
  apply contr_map_isequiv.
  unfold hfiber_compose_map.
  transparent assert (h : (hfiber (@pr1 A B) (g x) <~> hfiber g (g x))).
  { refine (_ oE equiv_to_O O _).
    refine (_ oE Build_Equiv _ _
              (O_functor_hfiber O (@pr1 A B) (g x)) _).
    unfold hfiber.
    apply equiv_functor_sigma_id. intros y; cbn.
    refine (_ oE (equiv_moveR_equiv_V _ _)).
    apply equiv_concat_l.
    apply moveL_equiv_V.
    unfold g, O_functor.
    revert y; apply O_indpaths; intros [a q]; cbn.
    refine (_ @ (O_rec_beta _ _)^).
    apply ap, O_rec_beta. }
  refine (isequiv_homotopic (h oE equiv_hfiber_homotopic _ _ p (g x)) _).
  intros [[a b] q]; cbn. clear h.
  unfold O_functor_hfiber.
  rewrite O_rec_beta.
  unfold functor_sigma; cbn.
  refine (path_sigma' _ 1 _).
  rewrite O_indpaths_beta; cbn.
  unfold moveL_equiv_V, moveR_equiv_V.
  Open Scope long_path_scope.
  Local Opaque eissect. (* work around bug 4533 *)
  rewrite !ap_pp, !concat_p_pp, !ap_V.
  unfold to_O_natural.
  rewrite concat_pV_p.
  subst p.
  rewrite concat_pp_V.
  rewrite concat_pp_p; apply moveR_Vp.
  rewrite <- !(ap_compose (to O A) (to O A)^-1).
  rapply @concat_A1p.
  Local Transparent eissect. (* work around bug 4533 *)
  Close Scope long_path_scope.
Qed.
