Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Diagram.
Local Open Scope path_scope.
Generalizable All Variables.

Context `{Funext}.

Record cocone {G: graph} (D: diagram G) (X: Type) :=
  {q : forall i, D i -> X;
   qq : forall (i j: G) (g: G i j) (x: D i), q j (D _f g x) = q i x}.

Arguments Build_cocone {G D X} q qq.
Arguments q {G D X} C i x : rename.
Arguments qq {G D X} C i j g x : rename.

Coercion q : cocone >-> Funclass.


(** *** Definition of colimits *** *)

Section Cocone.
  Context {G: graph} {D: diagram G} {X:Type}.
  
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

  Definition postcompose_cocone (C: cocone D X) {Y: Type}
    : (X -> Y) -> cocone D Y.
    intros f.
    simple refine (Build_cocone _ _).
    - intros i. exact (f o (C i)).
    - intros i j g x. exact (ap f (qq _ i j g x)).
  Defined.

  (** Definition of the universality of a cocone. *)
  Definition is_universal (C: cocone D X)
    := forall (Y: Type), IsEquiv (@postcompose_cocone C Y).
  
End Cocone.


Record is_colimit `(D: diagram G) (Q: Type) :=
  {is_colimit_C :> cocone D Q;
   is_colimit_H : is_universal is_colimit_C}.

Arguments Build_is_colimit {G D Q} C H : rename.
Arguments is_colimit_C {G D Q} C : rename.
Arguments is_colimit_H {G D Q} H X : rename.
  
Definition postcompose_cocone_inv `{D: diagram G} `(H: is_colimit D Q)
           `(C: cocone D X) : Q -> X
  := @equiv_inv _ _ _ (is_colimit_H H X) C.



(** *** Existence of colimits *** *)
(** The existence is given by an HIT. *)

Module Export colimit_HIT.
  Private Inductive colimit {G: graph} (D: diagram G) : Type:=
  | colim : forall i, D i -> colimit D.

  Arguments colim {G D} i x.
  
  Axiom pp : forall {G: graph} {D: diagram G} (i j: G) (f : G i j) (x: D i),
      colim j (D _f f x) = colim i x.

  Definition colimit_ind {G: graph} {D: diagram G} (P: colimit D -> Type)
             (q : forall i x, P (colim i x))
             (pp_q : forall (i j: G) (g: G i j) (x: D i), (@pp G D i j g x) # (q j (D _f g x)) = q i x)
    : forall w, P w
    := fun w => match w with colim i a => fun _ => q _ a end pp_q.

  Axiom colimit_ind_beta_pp
    : forall {G: graph} {D: diagram G} (P: colimit D -> Type)
             (q : forall i x, P (colim i x))
             (pp_q : forall (i j: G) (g: G i j) (x: D i),
                 @pp G D i j g x # q _ (D _f g x) = q _ x)
             (i j: G) (g: G i j) (x: D i),
      apD (colimit_ind P q pp_q) (pp i j g x) = pp_q i j g x.

  Definition colimit_rec {G: graph} {D: diagram G} (P: Type) (C: cocone D P)
    : colimit D -> P.
    simple refine (colimit_ind _ _ _).
    - exact C.
    - intros i j g x.
      exact ((transport_const (pp i j g x) (q _ _ (D _f g x))) @ (qq _ i j g x)).
  Defined.
  
  Definition colimit_rec_beta_pp {G: graph} {D: diagram G} (P: Type) (C: cocone D P)
             (i j: G) (g: G i j) (x: D i)
    : ap (colimit_rec P C) (pp i j g x) = qq C i j g x.
    unfold colimit_rec, colimit_ind.
    eapply (cancelL (transport_const (pp i j g x) _)).
    simple refine ((apD_const (colimit_ind (fun _ => P) C _) (pp i j g x))^ @ _).
    simple refine (colimit_ind_beta_pp (fun _ => P) C _ i j g x).
  Defined.

  Definition cocone_colimit {G: graph} (D: diagram G) : cocone D (colimit D)
    := Build_cocone colim pp.
  
  Lemma is_universal_colimit {G: graph} (D: diagram G)
    : is_universal (cocone_colimit D).
    intro Y; simpl.
    simple refine (isequiv_adjointify _ (colimit_rec Y) _ _).
    - intros C. simple refine (path_cocone _ _).
      intros i x. reflexivity.
      intros i j f x. simpl. hott_simpl.
      apply colimit_rec_beta_pp.
    - intro f. apply path_forall.
      simple refine (colimit_ind  _ _ _).
      intros i x. reflexivity.
      intros i j g x. simpl.
      rewrite transport_paths_FlFr.
      rewrite colimit_rec_beta_pp. hott_simpl.
  Defined.

  Definition is_colimit_colimit {G: graph} (D: diagram G) : is_colimit D (colimit D)
    := Build_is_colimit _ (is_universal_colimit D).
End colimit_HIT.



(** *** Functoriality of colimits *** *)

Section FunctorialityCocone.
  Context {G: graph}.

  (* postcompose *)
  Definition postcompose_cocone_identity {D: diagram G} `(C: cocone D X)
    : postcompose_cocone C idmap = C.
    simple refine (path_cocone _ _).
    intros i x; reflexivity.
    intros i j g x; simpl; hott_simpl.
  Defined.

  Definition postcompose_cocone_comp {D: diagram G}
             `(f: X -> Y) `(g: Y -> Z) (C: cocone D X)
    : postcompose_cocone C (g o f)
      = postcompose_cocone (postcompose_cocone C f) g.
    simple refine (path_cocone _ _).
    intros i x; reflexivity.
    intros i j h x; simpl; hott_simpl. apply ap_compose.
  Defined.

  (* precompose *)
  Definition precompose_cocone {D1 D2: diagram G}
             (m: diagram_map D1 D2) {X: Type}
    : (cocone D2 X) -> (cocone D1 X).
    intros C. simple refine (Build_cocone _ _).
    intros i x. exact (C i (m i x)).
    intros i j g x; simpl.
    etransitivity. apply ap. symmetry. apply diagram_map_comm. apply qq.
  Defined.

  Definition precompose_cocone_identity (D: diagram G) (X: Type)
    : precompose_cocone (X:=X) (diagram_idmap D) == idmap.
    intros C; simpl. simple refine (path_cocone _ _).
    intros i x. reflexivity. intros; simpl. hott_simpl.
  Defined.

  Definition precompose_cocone_comp {D1 D2 D3: diagram G}
             (m2: diagram_map D2 D3) (m1: diagram_map D1 D2) (X: Type)
    : (precompose_cocone (X:=X) m1) o (precompose_cocone m2)
      == precompose_cocone (diagram_comp m2 m1).
    intro C; simpl.
    simple refine (path_cocone _ _).
    intros i x. reflexivity.
    intros i j g x. simpl. hott_simpl.
    apply ap10. apply ap. unfold CommutativeSquares.comm_square_comp.
    rewrite inv_pp. rewrite ap_pp. rewrite ap_compose. by rewrite ap_V.
  Defined.

  (* precompose and postcompose *)
  Definition precompose_postcompose_cocone {D1 D2: diagram G}
             (m: diagram_map D1 D2) `(f: X -> Y) (C: cocone D2 X)
    : postcompose_cocone (precompose_cocone m C) f
      = precompose_cocone m (postcompose_cocone C f).
    simple refine (path_cocone _ _).
    - intros i x; reflexivity.
    - intros i j g x; simpl; hott_simpl.
      etransitivity. apply ap_pp. apply ap10. apply ap.
      symmetry. apply ap_compose.
  Defined.

  (* compose with equivalences *)
  Definition precompose_cocone_equiv {D1 D2: diagram G} (m: D1 ≃ D2) (X: Type)
    : IsEquiv (precompose_cocone (X:=X) m).
    simple refine (isequiv_adjointify
                     _ (precompose_cocone (diagram_equiv_inv m)) _ _).
    - intros C. etransitivity. apply precompose_cocone_comp.
      rewrite diagram_inv_is_retraction. apply precompose_cocone_identity.
    - intros C. etransitivity. apply precompose_cocone_comp.
      rewrite diagram_inv_is_section. apply precompose_cocone_identity.
  Defined.

  Definition postcompose_cocone_equiv {D: diagram G} `(f: X <~> Y)
    : IsEquiv (fun C: cocone D X => postcompose_cocone C f).
    serapply isequiv_adjointify.
    - exact (fun C => postcompose_cocone C f^-1).
    - intros C. etransitivity. symmetry. apply postcompose_cocone_comp.
      etransitivity. 2:apply postcompose_cocone_identity. apply ap.
      funext x; apply eisretr.
    - intros C. etransitivity. symmetry. apply postcompose_cocone_comp.
      etransitivity. 2:apply postcompose_cocone_identity. apply ap.
      funext x; apply eissect.
  Defined.

  (* universality preserved by equivalences *)
  Definition precompose_equiv_universality {D1 D2: diagram G} (m: D1 ≃ D2)
             `(C: cocone D2 X)
    : is_universal C -> is_universal (precompose_cocone (X:=X) m C).
    unfold is_universal.
    intros H Y.
    rewrite (path_forall _ _ (fun f => precompose_postcompose_cocone m f C)).
    simple refine isequiv_compose. apply precompose_cocone_equiv.
  Defined.

  Definition postcompose_equiv_universality {D: diagram G} `(f: X <~> Y)
             `(C: cocone D X)
    : is_universal C -> is_universal (postcompose_cocone C f).
    unfold is_universal.
    intros H Z.
    rewrite <- (path_forall _ _ (fun g => postcompose_cocone_comp f g C)).
    simple refine isequiv_compose.
  Defined.

  Definition precompose_equiv_is_colimit {D1 D2: diagram G}
             (m: D1 ≃ D2) {Q: Type}
    : is_colimit D2 Q -> is_colimit D1 Q.
    intros HQ. simple refine (Build_is_colimit (precompose_cocone m HQ) _).
    apply precompose_equiv_universality. apply HQ.
  Defined.

  Definition postcompose_equiv_is_colimit {D: diagram G} `(f: Q <~> Q')
    : is_colimit D Q -> is_colimit D Q'.
    intros HQ. simple refine (Build_is_colimit (postcompose_cocone HQ f) _).
    apply postcompose_equiv_universality. apply HQ.
  Defined.
End FunctorialityCocone.


Section FunctorialityColimit.
  Context {G: graph}.
  
  Definition functoriality_colimit {D1 D2: diagram G}
             (m: diagram_map D1 D2)
             `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2)
    : Q1 -> Q2
    := postcompose_cocone_inv HQ1 (precompose_cocone m HQ2).

  Definition functoriality_colimit_commute {D1 D2: diagram G}
             (m: diagram_map D1 D2)
             `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2)
    : forall i, (q HQ2 i) o (m i)
           == (functoriality_colimit m HQ1 HQ2) o (q HQ1 i).
    intros i x.
    change (precompose_cocone m HQ2 i x =
            postcompose_cocone HQ1
              (postcompose_cocone_inv HQ1 (precompose_cocone m HQ2)) i x). 
    f_ap. exact (eisretr (postcompose_cocone HQ1) _)^.
  Defined.

  (** Here we prove than two equivalent diagrams have equivalent colimits. *)
  Context {D1 D2: diagram G} (m: D1 ≃ D2)
          `(HQ1: is_colimit D1 Q1) `(HQ2: is_colimit D2 Q2).
  
  Definition functoriality_colimit_eissect
    : Sect (functoriality_colimit (diagram_equiv_inv m) HQ2 HQ1)
           (functoriality_colimit m HQ1 HQ2).
    unfold functoriality_colimit.  apply ap10.
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


(** *** Unicity of colimits *** *)

Theorem colimit_unicity {G: graph} {D: diagram G} {Q1 Q2: Type}
        (HQ1: is_colimit D Q1) (HQ2: is_colimit D Q2)
  : Q1 <~> Q2.
  simple refine (functoriality_colimit_equiv _ HQ1 HQ2).
  simple refine (Build_diagram_equiv (diagram_idmap D) _).
Defined.



Definition transport_colimit `(D: Y -> diagram G)
           `(HQ: forall y, is_colimit (D y) (Q y))
           `(p: x = y :> Y) (i: G) (u: D x i)
  : transport Q p (HQ x i u) = HQ y i (transport (fun y => D y i) p u).
  destruct p; reflexivity.
Defined.
