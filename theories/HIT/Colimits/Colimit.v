Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Diagram.
Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of cocone and colimits, and functoriality results on colimits. *)

(** * Cocones *)

(** A cocone over a diagram [D] to a type [X] is a family of maps from the types of [D] to [X] making the triangles formed with the arrows of [D] commuting. *)

Record cocone {G: graph} (D: diagram G) (X: Type) :=
  {q : forall i, D i -> X;
   qq : forall (i j: G) (g: G i j) (x: D i), q j (D _f g x) = q i x}.

Arguments Build_cocone {G D X} q qq.
Arguments q {G D X} C i x : rename.
Arguments qq {G D X} C i j g x : rename.

Coercion q : cocone >-> Funclass.


Section Cocone.
  Context `{Funext} {G: graph} {D: diagram G} {X:Type}.

  (** [path_cocone] says when two cocones are equals (up to funext). *)

  Definition path_cocone_naive {C1 C2: cocone D X}
             (P := fun q' => forall {i j:G} (g: G i j) (x: D i), q' j (D _f g x)
                                                         = q' i x)
             (eq0 : q C1 = q C2)
             (eq1 : transport P eq0 (qq C1) = qq C2)
    : C1 = C2 :=
    match eq1 in (_ = v1) return C1 = {|q := q C2; qq := v1 |} with
    | idpath =>
      match eq0 in (_ = v0) return C1 = {|q := v0; qq := eq0 # (qq C1) |} with
      | idpath => 1
      end
    end.

  Definition path_cocone {C1 C2: cocone D X}
             (eq1 : forall i,  C1 i == C2 i)
             (eq2 : forall i j g x, qq C1 i j g x @ eq1 i x = eq1 j (D _f g x) @ qq C2 i j g x)
    : C1 = C2.
  Proof.
    destruct C1 as [q pp_q], C2 as [r pp_r].
    refine (path_cocone_naive (path_forall _ _ (fun i => path_forall _ _ (eq1 i))) _). simpl.
    funext i j f x.
    repeat rewrite transport_forall_constant.
    rewrite transport_paths_FlFr.
    rewrite concat_pp_p. apply moveR_Vp.
    rewrite !(ap_apply_lD2
                (path_forall q r (fun i => path_forall (q i) (r i) (eq1 i)))).
    rewrite !eisretr. apply eq2.
  Defined.

  (** Given a cocone [C] to [X] and a map from [X] to [Y], one can postcompose each map of [C] to get a cocone to [Y]. *)

  Definition postcompose_cocone (C: cocone D X) {Y: Type}
    : (X -> Y) -> cocone D Y.
  Proof.
    intros f.
    simple refine (Build_cocone _ _).
    - intros i. exact (f o (C i)).
    - intros i j g x. exact (ap f (qq _ i j g x)).
  Defined.

  (** ** Universality of a cocone. *)

  (** A colimit will be the extremity of an universal cocone. *)

  (** A cocone [C] over [D] to [X] is said universal when for all [Y] the map [postcompose_cocone] is an equivalence. In particular, given another cocone [C'] over [D] to [X'] the inverse of the map allows to recover a map [h] : [X] -> [X'] such that [C'] is [C] postcomposed with [h]. The fact that [postcompose_cocone] is an equivalence is an elegant way of stating the usual "unique existence" of category theory. *)

  Definition is_universal (C: cocone D X)
    := forall (Y: Type), IsEquiv (@postcompose_cocone C Y).

End Cocone.


(** * Colimits *)

(** A colimit is the extremity of a cocone. *)

Record is_colimit `(D: diagram G) (Q: Type) :=
  {is_colimit_C :> cocone D Q;
   is_colimit_H : is_universal is_colimit_C}.

Arguments Build_is_colimit {G D Q} C H : rename.
Arguments is_colimit_C {G D Q} C : rename.
Arguments is_colimit_H {G D Q} H X : rename.

(** [postcompose_cocone_inv] is defined for convenience: it is only the inverse of [postcompose_cocone]. It allows to recover the map [h] from a cocone [C']. *)

Definition postcompose_cocone_inv `{D: diagram G} `(H: is_colimit D Q)
           `(C': cocone D X) : Q -> X
  := @equiv_inv _ _ _ (is_colimit_H H X) C'.



(** * Existence of colimits *)

(** Whatever the diagram considered, there exists a colimit of it. The existence is given by the HIT [colimit]. *)

(** ** Definition of the HIT *)

Module Export ColimitHIT.
  Private Inductive colimit {G: graph} (D: diagram G) : Type:=
  | colim : forall i, D i -> colimit D.

  Arguments colim {G D} i x.

  Axiom colimp : forall {G: graph} {D: diagram G} (i j: G) (f : G i j) (x: D i),
      colim j (D _f f x) = colim i x.

  Definition colimit_ind {G: graph} {D: diagram G} (P: colimit D -> Type)
             (q : forall i x, P (colim i x))
             (pp_q : forall (i j: G) (g: G i j) (x: D i), (@colimp G D i j g x) # (q j (D _f g x)) = q i x)
    : forall w, P w
    := fun w => match w with colim i a => fun _ => q _ a end pp_q.

  Axiom colimit_ind_beta_colimp
    : forall {G: graph} {D: diagram G} (P: colimit D -> Type)
             (q : forall i x, P (colim i x))
             (pp_q : forall (i j: G) (g: G i j) (x: D i),
                 @colimp G D i j g x # q _ (D _f g x) = q _ x)
             (i j: G) (g: G i j) (x: D i),
      apD (colimit_ind P q pp_q) (colimp i j g x) = pp_q i j g x.

  Definition colimit_rec {G: graph} {D: diagram G} (P: Type) (C: cocone D P)
    : colimit D -> P.
  Proof.
    simple refine (colimit_ind _ _ _).
    - exact C.
    - intros i j g x.
      exact ((transport_const (colimp i j g x) (q _ _ (D _f g x))) @ (qq _ i j g x)).
  Defined.

  Definition colimit_rec_beta_colimp {G: graph} {D: diagram G} (P: Type) (C: cocone D P)
             (i j: G) (g: G i j) (x: D i)
    : ap (colimit_rec P C) (colimp i j g x) = qq C i j g x.
  Proof.
    unfold colimit_rec, colimit_ind.
    eapply (cancelL (transport_const (colimp i j g x) _)).
    simple refine ((apD_const (colimit_ind (fun _ => P) C _) (colimp i j g x))^ @ _).
    simple refine (colimit_ind_beta_colimp (fun _ => P) C _ i j g x).
  Defined.
End ColimitHIT.

(** And we can now show that the HIT is actually a colimit. *)

Definition cocone_colimit {G: graph} (D: diagram G) : cocone D (colimit D)
  := Build_cocone colim colimp.

Lemma is_universal_colimit `{Funext} {G: graph} (D: diagram G)
  : is_universal (cocone_colimit D).
Proof.
  intro Y; simpl.
  simple refine (isequiv_adjointify _ (colimit_rec Y) _ _).
  - intros C. simple refine (path_cocone _ _).
    intros i x. reflexivity.
    intros i j f x. simpl. hott_simpl.
    apply colimit_rec_beta_colimp.
  - intro f. apply path_forall.
    simple refine (colimit_ind  _ _ _).
    intros i x. reflexivity.
    intros i j g x. simpl.
    rewrite transport_paths_FlFr.
    rewrite colimit_rec_beta_colimp. hott_simpl.
Defined.

Definition is_colimit_colimit `{Funext} {G: graph} (D: diagram G) : is_colimit D (colimit D)
  := Build_is_colimit _ (is_universal_colimit D).


(** * Functoriality of colimits *)

(** We now prove several functoriality results, first on cocone and then on colimits. *)

Section FunctorialityCocone.
  Context `{fs: Funext} {G: graph}.

  (** ** Postcomposition for cocones *)

  (** Identity and associativity for the postcomposition of a cocone with a map. *)

  Definition postcompose_cocone_identity {D: diagram G} `(C: cocone D X)
    : postcompose_cocone C idmap = C.
  Proof.
    simple refine (path_cocone _ _).
    intros i x; reflexivity.
    intros i j g x; simpl; hott_simpl.
  Defined.

  Definition postcompose_cocone_comp {D: diagram G}
             `(f: X -> Y) `(g: Y -> Z) (C: cocone D X)
    : postcompose_cocone C (g o f)
      = postcompose_cocone (postcompose_cocone C f) g.
  Proof.
    simple refine (path_cocone _ _).
    intros i x; reflexivity.
    intros i j h x; simpl; hott_simpl. apply ap_compose.
  Defined.

  (** ** Precomposition for cocones *)

  (** Given a cocone over [D2] and a diagram map [m] : [D1] => [D2], one can precompose each map of the cocone by the corresponding one of [m] to get a cocone over [D1]. *)

  Definition precompose_cocone {D1 D2: diagram G}
             (m: diagram_map D1 D2) {X: Type}
    : (cocone D2 X) -> (cocone D1 X).
  Proof.
    intros C. simple refine (Build_cocone _ _).
    intros i x. exact (C i (m i x)).
    intros i j g x; simpl.
    etransitivity. apply ap. symmetry. apply diagram_map_comm. apply qq.
  Defined.

  (** Identity and associativity for the precomposition of a cocone with a diagram map. *)

  Definition precompose_cocone_identity (D: diagram G) (X: Type)
    : precompose_cocone (X:=X) (diagram_idmap D) == idmap.
    intros C; simpl. simple refine (path_cocone _ _).
    intros i x. reflexivity. intros; simpl. hott_simpl.
  Defined.

  Definition precompose_cocone_comp {D1 D2 D3: diagram G}
             (m2: diagram_map D2 D3) (m1: diagram_map D1 D2) (X: Type)
    : (precompose_cocone (X:=X) m1) o (precompose_cocone m2)
      == precompose_cocone (diagram_comp m2 m1).
  Proof.
    intro C; simpl.
    simple refine (path_cocone _ _).
    intros i x. reflexivity.
    intros i j g x. simpl. hott_simpl.
    apply ap10. apply ap. unfold CommutativeSquares.comm_square_comp.
    rewrite inv_pp. rewrite ap_pp. rewrite ap_compose. by rewrite ap_V.
  Defined.

  (** Associativity of a precomposition and a postcomposition. *)

  Definition precompose_postcompose_cocone {D1 D2: diagram G}
             (m: diagram_map D1 D2) `(f: X -> Y) (C: cocone D2 X)
    : postcompose_cocone (precompose_cocone m C) f
      = precompose_cocone m (postcompose_cocone C f).
  Proof.
    simple refine (path_cocone _ _).
    - intros i x; reflexivity.
    - intros i j g x; simpl; hott_simpl.
      etransitivity. apply ap_pp. apply ap10. apply ap.
      symmetry. apply ap_compose.
  Defined.

  (** The precomposition with a diagram equivalence is an equivalence. *)

  Definition precompose_cocone_equiv {D1 D2: diagram G} (m: D1 ~d~ D2) (X: Type)
    : IsEquiv (precompose_cocone (X:=X) m).
  Proof.
    simple refine (isequiv_adjointify
                     _ (precompose_cocone (diagram_equiv_inv m)) _ _).
    - intros C. etransitivity. apply precompose_cocone_comp.
      rewrite diagram_inv_is_retraction. apply precompose_cocone_identity.
    - intros C. etransitivity. apply precompose_cocone_comp.
      rewrite diagram_inv_is_section. apply precompose_cocone_identity.
  Defined.

  (** The postcomposition with an equivalence is an equivalence. *)

  Definition postcompose_cocone_equiv {D: diagram G} `(f: X <~> Y)
    : IsEquiv (fun C: cocone D X => postcompose_cocone C f).
  Proof.
    serapply isequiv_adjointify.
    - exact (fun C => postcompose_cocone C f^-1).
    - intros C. etransitivity. symmetry. apply postcompose_cocone_comp.
      etransitivity. 2:apply postcompose_cocone_identity. apply ap.
      funext x; apply eisretr.
    - intros C. etransitivity. symmetry. apply postcompose_cocone_comp.
      etransitivity. 2:apply postcompose_cocone_identity. apply ap.
      funext x; apply eissect.
  Defined.

  (** ** Universality preservation *)

  (** Universality of a cocone is preserved by composition with a (diagram) equivalence. *)

  Definition precompose_equiv_universality {D1 D2: diagram G} (m: D1 ~d~ D2)
             `(C: cocone D2 X)
    : is_universal C -> is_universal (precompose_cocone (X:=X) m C).
  Proof.
    unfold is_universal.
    intros H Y.
    rewrite (path_forall _ _ (fun f => precompose_postcompose_cocone m f C)).
    simple refine isequiv_compose. apply precompose_cocone_equiv.
  Defined.

  Definition postcompose_equiv_universality {D: diagram G} `(f: X <~> Y)
             `(C: cocone D X)
    : is_universal C -> is_universal (postcompose_cocone C f).
  Proof.
    unfold is_universal.
    intros H Z.
    rewrite <- (path_forall _ _ (fun g => postcompose_cocone_comp f g C)).
    simple refine isequiv_compose.
  Defined.

  (** Colimits are preserved by composition with a (diagram) equivalence. *)

  Definition precompose_equiv_is_colimit {D1 D2: diagram G}
             (m: D1 ~d~ D2) {Q: Type}
    : is_colimit D2 Q -> is_colimit D1 Q.
  Proof.
    intros HQ. simple refine (Build_is_colimit (precompose_cocone m HQ) _).
    apply precompose_equiv_universality. apply HQ.
  Defined.

  Definition postcompose_equiv_is_colimit {D: diagram G} `(f: Q <~> Q')
    : is_colimit D Q -> is_colimit D Q'.
  Proof.
    intros HQ. simple refine (Build_is_colimit (postcompose_cocone HQ f) _).
    apply postcompose_equiv_universality. apply HQ.
  Defined.
End FunctorialityCocone.


(** * Functoriality of colimits *)

Section FunctorialityColimit.
  Context `{fs: Funext} {G: graph}.

  (** A diagram map [m] : [D1] => [D2] induces a map between any two colimits of [D1] and [D2]. *)

  Definition functoriality_colimit {D1 D2: diagram G}
             (m: diagram_map D1 D2)
             `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2)
    : Q1 -> Q2
    := postcompose_cocone_inv HQ1 (precompose_cocone m HQ2).

  (** And this map commutes with diagram map. *)

  Definition functoriality_colimit_commute {D1 D2: diagram G}
             (m: diagram_map D1 D2)
             `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2)
    : precompose_cocone m HQ2
      = postcompose_cocone HQ1 (functoriality_colimit m HQ1 HQ2).
  Proof.
    unfold functoriality_colimit.
    exact (eisretr (postcompose_cocone HQ1) _)^.
  Defined.

  (** ** Colimits of equivalent diagrams *)

  (** Now we have than two equivalent diagrams have equivalent colimits. *)

  Context {D1 D2: diagram G} (m: D1 ~d~ D2)
          `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2).

  Definition functoriality_colimit_eissect
    : Sect (functoriality_colimit (diagram_equiv_inv m) HQ2 HQ1)
           (functoriality_colimit m HQ1 HQ2).
  Proof.
    unfold functoriality_colimit. apply ap10.
    simple refine (equiv_inj (postcompose_cocone HQ2) _). apply HQ2.
    etransitivity. 2:symmetry; apply postcompose_cocone_identity.
    etransitivity. apply postcompose_cocone_comp.
    unfold postcompose_cocone_inv. rewrite eisretr.
    rewrite precompose_postcompose_cocone. rewrite eisretr.
    rewrite precompose_cocone_comp. rewrite diagram_inv_is_section.
    apply precompose_cocone_identity.
  Defined.

  Definition functoriality_colimit_eisretr
    : Sect (functoriality_colimit m HQ1 HQ2)
           (functoriality_colimit (diagram_equiv_inv m) HQ2 HQ1).
  Proof.
    unfold functoriality_colimit.  apply ap10.
    simple refine (equiv_inj (postcompose_cocone HQ1) _). apply HQ1.
    etransitivity. 2:symmetry; apply postcompose_cocone_identity.
    etransitivity. apply postcompose_cocone_comp.
    unfold postcompose_cocone_inv. rewrite eisretr.
    rewrite precompose_postcompose_cocone. rewrite eisretr.
    rewrite precompose_cocone_comp. rewrite diagram_inv_is_retraction.
    apply precompose_cocone_identity.
  Defined.

  Definition functoriality_colimit_isequiv
    : IsEquiv (functoriality_colimit m HQ1 HQ2)
    := isequiv_adjointify _ _ functoriality_colimit_eissect
                          functoriality_colimit_eisretr.

  Definition functoriality_colimit_equiv
    : Q1 <~> Q2
    := BuildEquiv _ _ _ functoriality_colimit_isequiv.
End FunctorialityColimit.


(** * Unicity of colimits *)

(** A particuliar case of the functoriality result is that all colimits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem colimit_unicity `{Funext} {G: graph} {D: diagram G} {Q1 Q2: Type}
        (HQ1: is_colimit D Q1) (HQ2: is_colimit D Q2)
  : Q1 <~> Q2.
Proof.
  simple refine (functoriality_colimit_equiv _ HQ1 HQ2).
  simple refine (Build_diagram_equiv (diagram_idmap D) _).
Defined.