Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Limits.Pullback Factorization Truncations.Core.
Require Import Modality Accessible Modalities.Localization Descent Separated.

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
  Definition isequiv_mapino_isconnected
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
  #[export] Instance
    conn_map_functor_hfiber_to_O
         {Y X : Type} (f : Y -> X) (x : X)
    : IsConnMap O (functor_hfiber (fun y => (to_O_natural O f y)^) x)
    := OO_conn_map_functor_hfiber_to_O O O f x.

  #[export] Instance isequiv_O_functor_hfiber
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
  #[export] Instance isequiv_path_O
         {X : Type@{i}} (x y : X)
    : IsEquiv (path_OO O O x y)
    := isequiv_path_OO O O x y.

  Definition equiv_path_O {X : Type@{i}} (x y : X)
    : O (x = y) <~> (to O X x = to O X y)
    := equiv_path_OO O O x y.

  Definition equiv_path_O_to_O {X : Type} (x y : X)
    : (equiv_path_O x y) o (to O (x = y)) == @ap _ _ (to O X) x y.
  Proof.
    intros p; unfold equiv_path_O, equiv_path_OO, path_OO; cbn.
    apply O_rec_beta.
  Defined.

  (** RSS Theorem 3.1 (x).  This justifies the term "left exact". *)
  #[export] Instance O_inverts_functor_pullback_to_O
         {A B C : Type} (f : B -> A) (g : C -> A)
    : O_inverts O (functor_pullback f g (O_functor O f) (O_functor O g)
                                    (to O A) (to O B) (to O C)
                                    (to_O_natural O f) (to_O_natural O g))
    := OO_inverts_functor_pullback_to_O O O f g.

  Definition equiv_O_pullback {A B C : Type} (f : B -> A) (g : C -> A)
    : O (Pullback f g) <~> Pullback (O_functor O f) (O_functor O g)
    := equiv_O_rec_O_inverts
         O (functor_pullback f g (O_functor O f) (O_functor O g)
                             (to O A) (to O B) (to O C)
                             (to_O_natural O f) (to_O_natural O g)).

  Definition O_functor_pullback
             {A B C : Type} (f : B -> A) (g : C -> A)
    : IsPullback (O_functor_square O _ _ _ _ (pullback_commsq f g)).
  Proof.
    unfold IsPullback.
    napply (isequiv_homotopic
               (O_rec (functor_pullback _ _ _ _ _ _ _
                                        (to_O_natural O f) (to_O_natural O g)))).
    1: apply isequiv_O_rec_O_inverts; exact _.
    apply O_indpaths.
    etransitivity.
    1: intro x; apply O_rec_beta.
    symmetry.
    snapply pullback_homotopic; intros [b [c e]]; cbn.
    all: change (to (modality_subuniv O)) with (to O).
    - napply (to_O_natural O).
    - napply (to_O_natural O).
    - Open Scope long_path_scope.
      lhs napply concat_p_pp.
      lhs napply (concat_p_pp _ _ _ @@ 1).
      rewrite to_O_natural_compose.
      unfold O_functor_square.
      rewrite O_functor_homotopy_beta.
      rewrite 6 concat_pp_p.
      do 3 apply whiskerL.
      rhs_V napply concat_pp_p.
      apply moveL_pM.
      lhs_V napply inv_pp.
      rhs_V napply inv_Vp.
      apply (ap inverse).
      napply to_O_natural_compose.
      Close Scope long_path_scope.
  Defined.

  Definition diagonal_O_functor {A B : Type} (f : A -> B)
    : diagonal (O_functor O f) == equiv_O_pullback f f o O_functor O (diagonal f).
  Proof.
    apply O_indpaths; intros x.
    refine (_ @ (ap _ (to_O_natural _ _ _))^).
    cbn.
    refine (_ @ (O_rec_beta _ _)^).
    unfold diagonal, functor_pullback, functor_sigma; cbn.
    apply ap, ap.
    apply moveL_pV; exact (concat_1p_p1 _).
  Defined.

  (** RSS Theorem 3.1 (xi) *)
  Definition cancelL_conn_map
             {Y X Z : Type} (f : Y -> X) (g : X -> Z)
             `{IsConnMap O _ _ (g o f)} `{IsConnMap O _ _ g}
    : IsConnMap O f
    := OO_cancelL_conn_map O O f g.

  (** RSS Theorem 3.1 (xii) *)
  #[export] Instance conn_map_O_inverts
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
    - intros; napply OO_descend_O_inverts_beta.
  Defined.  

  (** RSS Theorem 3.11 (iii): in the accessible case, the universe is modal. *)
  #[export] Instance inO_typeO_lex `{Univalence} `{IsAccRSU O}
    : In (lift_accrsu O) (Type_ O)
    := _.

  (** Part of RSS Corollary 3.9: lex modalities preserve [n]-types for all [n].  This is definitely not equivalent to lex-ness, since it is true for the truncation modalities that are not lex.  But it is also not true of all modalities; e.g. the shape modality in a cohesive topos can take 0-types to [oo]-types.  With a little more work, this can probably be proven without [Funext]. *)
  #[export] Instance istrunc_O_lex `{Funext}
         {n : trunc_index} {A : Type} `{IsTrunc n A}
    : IsTrunc n (O A).
  Proof.
    generalize dependent A; simple_induction n n IHn; intros A ?.
    - exact _.               (** Already proven for all modalities. *)
    - apply istrunc_S.
      refine (O_ind (fun x => forall y, IsTrunc n (x = y)) _); intros x.
      refine (O_ind (fun y => IsTrunc n (to O A x = y)) _); intros y.
      exact (istrunc_equiv_istrunc _ (equiv_path_O x y)).
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
    exact (O_lex_leq_inO_TypeO O O).
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
    exact (cancelR_conn_map O (factor1 (image O f)) (const_tt _)).
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
    specialize (H A Unit B Unit (const_tt _) (const_tt _) f idmap _ _ _ _
                  (fun _ => 1)).
    unfold IsPullback, pullback_corec in H.
    refine (isequiv_compose _ (H:=H) (fun x => x.2.1)).
    unfold Pullback.
    refine (isequiv_compose (B:={b:Unit & B})
              (functor_sigma idmap (fun a => pr1))
              pr2).
    refine (isequiv_compose (equiv_sigma_prod0 Unit B) snd).
    exact (equiv_isequiv (prod_unit_l B)).
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
  (* Even though https://github.com/coq/coq/issues/4533 is closed, this is still needed. *)
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

(** ** Lexness via generators *)

(** Here the characterization of when an accessible presentation yields a lex modality from Anel-Biederman-Finster-Joyal ("Higher Sheaves and Left-Exact Localizations of ∞-Topoi", arXiv:2101.02791): it's enough for path spaces of the generators to be connected. *)
Definition lex_gen `{Univalence} (O : Modality) `{IsAccModality O}
           (lexgen : forall (i : ngen_indices (acc_ngen O)) (x y : ngen_type (acc_ngen O) i),
               IsConnected O (x = y))
  : Lex O.
Proof.
  srapply lex_from_inO_typeO; [ exact _ | intros i ].
  rapply ooextendable_TypeO_from_extension; intros P; srefine (_;_).
  1:intros; exists (forall x, P x); exact _.
  assert (wc : forall y z, P y <~> P z).
  { intros y z.
    (** Here we use the hypothesis [lexgen] (typeclass inference finds it automatically). *)
    exact (pr1 (isconnected_elim O _ (@equiv_transport _ P y z))). }
  intros x; apply path_TypeO, path_universe_uncurried.
  refine (equiv_adjointify (fun f => f x) (fun u y => wc x y ((wc x x)^-1 u)) _ _).
  - intros u; apply eisretr.
  - intros f; apply path_forall; intros y; apply moveR_equiv_M.
    destruct (isconnected_elim O _ (fun y => (wc x y)^-1 (f y))) as [z p].
    exact (p x @ (p y)^).
Defined.

(** ** n-fold separation *)

(** A type is [n]-[O]-separated, for n >= -2, if all its (n+2)-fold iterated identity types are [O]-modal.  Inductively, this means that it is (-2)-O-separated if it is O-modal, and (n+1)-O-separated if its identity types are n-O-separated. *)
Fixpoint nSep (n : trunc_index) (O : Subuniverse) : Subuniverse
  := match n with
     | -2 => O
     | n.+1 => Sep (nSep n O)
     end.

(** The reason for indexing this notion by a [trunc_index] rather than a [nat] is that when O is lex, a type is n-O-separated if and only if its O-unit is an n-truncated map. *)
Definition nsep_iff_trunc_to_O (n : trunc_index) (O : Modality) `{Lex O} (A : Type)
  : In (nSep n O) A <-> IsTruncMap n (to O A).
Proof.
  revert A; induction n as [|n IHn]; intros A; split; intros ?.
  - apply contr_map_isequiv; rapply isequiv_to_O_inO.
  - exact (inO_equiv_inO (O A) (to O A)^-1).
  - apply istruncmap_from_ap; intros x y.
    pose (i := fst (IHn (x = y)) _).
    apply istruncmap_mapinO_tr, (mapinO_homotopic _ _ (equiv_path_O_to_O O x y)).
  - intros x y.
    apply (snd (IHn (x = y))).
    pose (i := istruncmap_ap n (to O A) x y).
    apply mapinO_tr_istruncmap in i.
    apply istruncmap_mapinO_tr, (mapinO_homotopic _ ((equiv_path_O O x y)^-1 o (@ap _ _ (to O A) x y))).
    { intros p; apply moveR_equiv_V; symmetry; apply equiv_path_O_to_O. }
    pose mapinO_isequiv. (* This speeds up the next line. *)
    rapply mapinO_compose.
Defined.
