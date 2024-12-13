(** * Kan extensions of type families *)

(** This is part of the formalization of section 4 of the paper: Injective Types in Univalent Mathematics by Martin Escardo.  Many proofs are guided by Martin Escardo's original Agda formalization of this paper which can be found at: https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.Article.html. *)

Require Import Basics.
Require Import Types.Sigma Types.Unit Types.Forall Types.Empty Types.Universe Types.Equiv Types.Paths.
Require Import HFiber.
Require Import Truncations.Core.
Require Import Modalities.ReflectiveSubuniverse Modalities.Modality.

(** We are careful about universe variables for these first few definitions because they are used in the rest of the paper.  We use [u], [v], [w], etc. as our typical universe variables. Our convention for the max of two universes [u] and [v] is [uv]. *)

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition LeftKanFam@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => sig@{uv w} (fun (w : hfiber j y) => P (w.1)).

  Definition RightKanFam@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => forall (w : hfiber j y), P (w.1).

  (** Below we will introduce notations [P <| j] and [P |> j] for these Kan extensions. *)

  (** If [j] is an embedding, then [P <| j] and [P |> j] are extensions in the following sense: [(P <| j o j) x <~> P x <~> (P |> j o j) x].  So, with univalence, we get that they are extensions. *)

  Definition isext_equiv_leftkanfam@{} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (LeftKanFam@{} P j (j x)) (P x).
  Proof.
    rapply (@equiv_contr_sigma (hfiber j (j x)) _ _).
  Defined.

  Definition isext_equiv_rightkanfam@{} `{Funext} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (RightKanFam@{} P j (j x)) (P x).
  Proof.
    rapply (@equiv_contr_forall _ (hfiber j (j x)) _ _).
  Defined.

  Definition isext_leftkanfam@{suvw | uvw < suvw} `{Univalence} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : @paths@{suvw} Type@{uvw} (LeftKanFam@{} P j (j x)) (P x)
    := path_universe_uncurried (isext_equiv_leftkanfam _ _ _ _).

  Definition isext_rightkanfam@{suvw | uvw < suvw} `{Univalence} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : @paths@{suvw} Type@{uvw} (RightKanFam@{} P j (j x)) (P x)
    := path_universe_uncurried (isext_equiv_rightkanfam _ _ _ _).

End UniverseStructure.

Notation "P <| j" := (LeftKanFam P j) : function_scope.
Notation "P |> j" := (RightKanFam P j) : function_scope.

(** For [y : Y] not in the image of [j], [(P <| j) y] is empty and [(P |> j) y] is contractible. *)
Definition isempty_leftkanfam {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : (P <| j) y -> Empty
  := fun '((x; p); _) => ynin x p.

Definition contr_rightkanfam `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : Contr ((P |> j) y).
Proof.
  snrapply contr_forall.
  intros [x p].
  apply (Empty_rec (ynin x p)).
Defined.

(** The following equivalences tell us that [{ y : Y & (P <| j) y}] and [forall y : Y, (P |> j) y] can be thought of as just different notation for the sum and product of a type family. *)
Definition equiv_leftkanfam {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y)
  : {x : X & P x} <~> {y : Y & (P <| j) y}.
Proof.
  snrapply equiv_adjointify.
  - exact (fun w : {x : X & P x} => (j w.1; (w.1; idpath); w.2)).
  - exact (fun '((y; ((x; p); y')) : {y : Y & (P <| j) y}) => (x; y')).
  - by intros [y [[x []] y']].
  - reflexivity.
Defined.

Definition equiv_rightkanfam `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y)
  : (forall x, P x) <~> (forall y, (P |> j) y).
Proof.
  snrapply equiv_adjointify.
  - intros g y w. exact (g w.1).
  - exact (fun h x => h (j x) (x; idpath)).
  - intros h. by funext y [x []].
  - intros g. by apply path_forall.
Defined.

(** Here we are taking the perspective that a type family [P : X -> Type] as an oo-presheaf, considering the interpretation of [X] as an oo-groupoid and [Type] as a universe of spaces i.e. an appropriate generalization of the category of sets. It is easy to see that a type family [P] is functorial if we define its action on paths with [transport]. Functoriality then reduces to known lemmas about the [transport] function. *)

(** With this in mind, we define the type of transformations between two type families. [concat_Ap] says that these transformations are automatically natural. *)
Definition MapFam {X : Type} (P : X -> Type) (R : X -> Type)
  := forall x, P x -> R x.

Notation "P >=> R" := (MapFam P R) : function_scope.

(** Composition of transformations. *)
Definition compose_mapfam {X} {P R Q : X -> Type} (b : R >=> Q) (a : P >=> R)
  : P >=> Q
  := fun x => (b x) o (a x).

(** If [j] is an embedding then [(P <| j) =< (P |> j)]. *)
Definition transform_leftkanfam_rightkanfam {X Y : Type}
  (P : X -> Type) (j : X -> Y) (isem : IsEmbedding j)
  : (P <| j) >=> (P |> j).
Proof.
  intros y [w' z] w.
  snrapply (transport (fun a => P a.1) _ z).
  srapply path_ishprop.
Defined.

(** Under this interpretation, we can think of the maps [P <| j] and [P |> j] as left and right Kan extensions of [P : X -> Type] along [j : X -> Y]. To see this we can construct the (co)unit transformations of our extensions. *)
Definition unit_leftkanfam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : P >=> ((P <| j) o j)
  := fun x A => ((x; idpath); A).
  
Definition counit_rightkanfam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : ((P |> j) o j) >=> P
  := fun x A => A (x; idpath).

Definition counit_leftkanfam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : ((R o j) <| j) >=> R.
Proof.
  intros y [[x p] C].
  exact (transport R p C).
Defined.

Definition unit_rightkanfam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : R >=> ((R o j) |> j).
Proof.
  intros y C [x p].
  exact (transport R p^ C).
Defined.

(** Universal property of the Kan extensions. *)
Definition univ_property_leftkanfam {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : P >=> R o j)
  : { b : P <| j >=> R & compose_mapfam (b o j) (unit_leftkanfam P j) == a}.
Proof.
  snrefine (_; _).
  - intros y [[x p] A]. exact (p # a x A).
  - intros x. reflexivity.
Defined.

Definition contr_univ_property_leftkanfam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} {a : P >=> R o j}
  : Contr { b : P <| j >=> R | compose_mapfam (b o j) (unit_leftkanfam P j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_leftkanfam a)).
  intros [b F].
  symmetry. (* Do now to avoid inversion in the first subgoal. *)
  srapply path_sigma.
  - funext y. funext [[w []] c]. srefine (ap10 (F w) c).
  - simpl.
    funext x.
    lhs nrapply transport_forall_constant.
    lhs nrapply transport_paths_Fl.
    apply moveR_Vp.
    rhs nrapply concat_p1.
    unfold compose_mapfam, unit_leftkanfam.
    symmetry.
    pose (i := fun px: P x => ((x; 1); px) : (P <| j) (j x)).
    lhs nrapply (ap_compose (fun k : (P <| j) >=> R => k (j x)) (fun ka => ka o i)).
    (* [ap (fun k => k (j x))] is exactly [apD10], so it cancels the first [path_forall]. *)
    lhs nrefine (ap _ (apD10_path_forall _ _ _ _)).
    lhs rapply (ap_precompose _ i).
    unfold path_forall, ap10.
    rewrite (eisretr apD10); cbn.
    apply eissect.
Defined.

Definition univ_property_rightkanfam {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : R o j >=> P)
  : { b : R >=> P |> j & compose_mapfam (counit_rightkanfam P j) (b o j) == a}.
Proof.
  snrefine (_; _).
  - intros y A [x p]. exact (a x (p^ # A)).
  - intro x. reflexivity.
Defined.

Definition contr_univ_property_rightkanfam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : R o j >=> P)
  : Contr { b : R >=> P |> j & compose_mapfam (counit_rightkanfam P j) (b o j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_rightkanfam a)).
  intros [b F].
  symmetry. (* Do now to avoid inversion in the first subgoal. *)
  srapply path_sigma.
  - funext y. funext C. funext [x p]. destruct p. srefine (ap10 (F x) C).
  - simpl.
    funext x.
    lhs nrapply transport_forall_constant.
    lhs nrapply transport_paths_Fl.
    apply moveR_Vp.
    symmetry.
    lhs nrapply concat_p1.
    unfold compose_mapfam.
    lhs nrapply (ap_compose (fun k : R >=> (P |> j) => k (j x)) (fun ka => _ o ka)).
    (* [ap (fun k => k (j x))] is exactly [apD10], so it cancels the first [path_forall]. *)
    lhs nrefine (ap _ (apD10_path_forall _ _ _ _)).
    lhs nrapply ap_postcompose.
    unfold path_forall, ap10.
    rewrite (eisretr apD10).
    change (ap _ ?p) with (apD10 p (x; 1)).
    nrapply moveR_equiv_V.
    funext r.
    exact (apD10_path_forall _ _ _ (x; _)).
Defined.

(** The above (co)unit constructions are special cases of the following, which tells us that these extensions are adjoint to restriction by [j] *)
Definition leftadjoint_leftkanfam `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : ((P <| j) >=> R) <~> (P >=> R o j).
Proof.
  snrapply equiv_adjointify.
  - intros a x B. exact (a (j x) ((x; idpath); B)).
  - intros b y [[x p] C]. exact (p # (b x C)).
  - intros b. by funext x C.
  - intros a. by funext y [[x []] C].
Defined.

Definition rightadjoint_rightkanfam `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : (R >=> (P |> j)) <~> (R o j >=> P).
Proof.
  snrapply equiv_adjointify.
  - intros a x C. exact (a (j x) C (x; idpath)).
  - intros a y C [x p]. apply (a x). exact (p^ # C).
  - intros a. by funext x C.
  - intros b. funext y C [x p]. destruct p; cbn. reflexivity.
Defined.

(** This section is all set up for the proof that the left Kan extension of an embedding is an embedding of type families. *)
Section EmbedProofLeft.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  (** The counit transformation of a type family of the form [P <| j] has each of its components an equivalence.  In other words, the type family [P <| j] is the left Kan extension of its restriction along [j]. *)
  Definition isequiv_counit_leftkanfam_leftkanfam (P : X -> Type) {y : Y}
    : IsEquiv (counit_leftkanfam (P <| j) j y).
  Proof.
    snrapply isequiv_adjointify.
    - exact (fun '(((x; p); C) : (P <| j) y) => ((x; p); ((x; idpath); C))).
    - by intros [[x []] C].
    - intros [[x []] [[x' p'] C]]; cbn; cbn in C, p'.
      revert p'; apply (equiv_ind (ap j)).
      by intros [].
  Defined.

  (** We now use the above fact to show that type families over [X] are equivalent to type families over [Y] such that the counit map is a natural isomorphism. *)
  Definition leftkanfam_counit_equiv (P : X -> Type)
    : { R : Y -> Type & forall y, IsEquiv (counit_leftkanfam R j y) }.
  Proof.
    exists (P <| j).
    rapply isequiv_counit_leftkanfam_leftkanfam.
  Defined.

  Global Instance isequiv_leftkanfam_counit_equiv
    : IsEquiv leftkanfam_counit_equiv.
  Proof.
    snrapply isequiv_adjointify.
    - intros [R e]. exact (R o j).
    - intros [R e]. srapply path_sigma_hprop; cbn.
      funext y.
      exact (path_universe _ (feq:=e y)).
    - intros P.
      funext x.
      rapply isext_leftkanfam.
  Defined.

  (** Using these facts we can show that the map [_ <| j] is an embedding if [j] is an embedding. *)
  Definition isembed_leftkanfam_ext
    : IsEmbedding (fun P => P <| j)
    := mapinO_compose (O:=-1) leftkanfam_counit_equiv pr1.

End EmbedProofLeft.

(** Dual proof for the right Kan extension. *)
Section EmbedProofRight.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Definition isequiv_unit_rightkanfam_rightkanfam (P : X -> Type) {y : Y}
    : IsEquiv (unit_rightkanfam (P |> j) j y).
  Proof.
    snrapply isequiv_adjointify.
    - intros C [x p]. exact (C (x; p) (x; idpath)).
    - intros C. funext [x p]. destruct p. funext w.
      rapply (@transport _ (fun t => C t (t.1; idpath) = C (x; idpath) t) _ w
        (center _ (isem (j x) (x; idpath) w)) idpath).
    - intros a. funext [x p]. destruct p.
      reflexivity.
  Defined.

  Definition rightkanfam_unit_equiv (P : X -> Type)
    : {R : Y -> Type & forall y, IsEquiv (unit_rightkanfam R j y)}.
  Proof.
    exists (P |> j).
    rapply isequiv_unit_rightkanfam_rightkanfam.
  Defined.
      
  Global Instance isequiv_rightkanfam_unit_equiv
    : IsEquiv rightkanfam_unit_equiv.
  Proof.
    snrapply isequiv_adjointify.
    - intros [R e]. exact (R o j).
    - intros [R e]. srapply path_sigma_hprop; cbn.
      funext y.
      symmetry; exact (path_universe _ (feq:=e y)).
    - intros P.
      funext x.
      rapply isext_rightkanfam.
  Defined.

  (** The map [_ |> j] is an embedding if [j] is an embedding. *)
  Definition isembed_rightkanfam_ext
    : IsEmbedding (fun P => P |> j)
    := mapinO_compose (O:=-1) rightkanfam_unit_equiv pr1.

End EmbedProofRight.
