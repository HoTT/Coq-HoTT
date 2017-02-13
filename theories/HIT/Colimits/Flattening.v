Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Diagram Colimits.Colimit Colimits.Pushout.
Local Open Scope path_scope.

Section Flattening.
  Context `{fs : Funext} {G : graph} (D : diagram G).

  (** We define here the graph ∫D, also denoted G·D *)
  Definition integral : graph.
    simple refine (Build_graph _ _).
    - exact {i : G & D i}.
    - intros i j. exact {g : G i.1 j.1 & diagram1 D g i.2 = j.2}.
  Defined.

  (** Then, a dependent diagram E over D is just a diagram over ∫D. *)
  Definition dep_diagram := diagram integral.

  Context (E : dep_diagram).

  Let E_f {i j : G} (g : G i j) (x : D i) : E (i; x) -> E (j; (D _f g) x)
      := @diagram1 _ E (i; x) (j; D _f g x) (g; 1).

  (** Given a dependent diagram, we can recover a diagram over G by considering the Σ types. *)
  Definition sigma_diagram : diagram G.
    simple refine (Build_diagram _ _ _).
    - intro i. exact {x : D i & E (i; x)}.
    - intros i j g x. simpl in *.
      exists (D _f g x.1). exact (E_f g x.1 x.2).
  Defined.

  Definition equifibered := forall i j (g : G i j) (x : D i), IsEquiv (E_f g x).

  Context (H : equifibered) `{Univalence}.
  
  Definition E' : colimit D -> Type.
    apply colimit_rec. simple refine (Build_cocone _ _).
    exact (fun i x => E (i; x)).
    intros i j g x; cbn. symmetry. eapply path_universe.
    apply H.
  Defined.

  
  Definition transport_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (colimp i j g x) (E_f g x y) = y.
  Proof.
    simple refine (transport_idmap_ap _ _ _ _ _ _ @ _).
    simple refine (transport2 idmap _ _ @ _).
    2: apply colimit_rec_beta_colimp.
    cbn. simple refine (moveR_transport_V idmap _ _ _ _).
    symmetry; apply transport_path_universe.
  Defined.

  Definition transport_E'_V {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (colimp i j g x)^ y = E_f g x y.
  Proof.
    simple refine (moveR_transport_V E' (colimp i j g x) y _ _). symmetry.
    apply transport_E'.
  Defined.

  Definition transport_E'_V_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport_E' g x y
      = ap (transport E' (colimp i j g x)) (transport_E'_V g x y)^
        @ transport_pV E' (colimp i j g x) y.
  Proof.
    unfold transport_E'_V.
    rewrite moveR_transport_V_V.
    rewrite inv_V. symmetry.
    apply ap_transport_transport_pV.
  Defined.

  
  Definition cocone_E' : cocone sigma_diagram (sig E').
  Proof.
    simple refine (Build_cocone _ _); cbn.
    + intros i w. exists (colim i w.1); cbn. exact w.2.
    + intros i j g x; cbn. simple refine (path_sigma' _ _ _).
      apply colimp. apply transport_E'.
  Defined.

  Local Opaque path_sigma ap11.

  Definition is_universal_cocone_E' : is_universal cocone_E'.
  Proof.
    intro Z. serapply isequiv_adjointify.
    - intros [q qq]. cbn in *.
      intros [x y]; revert x y.
      simple refine (colimit_ind _ _ _); cbn.
      intros i x y; exact (q i (x; y)).
      intros i j g x; cbn. funext y.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (_ @ qq i j g (x; y)). cbn. f_ap.
      refine (path_sigma' _ 1 _); cbn. apply transport_E'_V.
    - intros [q qq]. simple refine (path_cocone _ _).
      + intros i x; reflexivity.
      + intros i j g [x y].
        rewrite concat_1p, concat_p1. cbn. rewrite ap_path_sigma.
        cbn. rewrite colimit_ind_beta_colimp. rewrite ap10_path_forall.
        hott_simpl.
        refine (_ @ concat_1p _). refine (_ @@ 1).
        match goal with
        | |- ap _ ?X @ _ = _ => set X
        end.
        assert (transport_E'_V g x y = p^). {
          subst p. clear. unfold transport_E'_V.
          exact (moveL_transport_V_V E' _ _ _ _)^. }
        rewrite X. clearbody p. clear. set (E_f g x y) in *.
        clearbody d; destruct p.
        reflexivity.
    - intro f. funext [x y]. revert x y; cbn.
      simple refine (colimit_ind _ _ _); cbn.
      + reflexivity.
      + intros i j g x; cbn. funext y.
        rewrite transport_forall; cbn.
        rewrite transport_paths_FlFr.
        match goal with
        | |- (_ @ ?pp) @ _ = _ => set pp
        end. cbn in p.
        assert (p = 1). {
          subst p.
          match goal with
          | |- transportD E' ?C _ _ _ = _ => set (C2:=C)
          end.
          rewrite (transportD_is_transport _ (fun w => C2 w.1 w.2)).
          subst C2; cbn. rewrite transport_paths_FlFr.
          rewrite concat_p1. apply moveR_Vp. rewrite concat_p1.
          rewrite ap_path_sigma. cbn.
          rewrite colimit_ind_beta_colimp. rewrite ap10_path_forall. 
          hott_simpl.
          rewrite ap11_is_ap10_ap01. cbn. rewrite concat_1p.
          rewrite (ap_compose (fun y => (colim j ((D _f g) x); y)) f). cbn.
          rewrite (ap_compose (fun x0 : exists x0 : D j, E (j; x0)
                               => (colim j (pr1 x0); pr2 x0)) f).
          rewrite <- !ap_pp. apply (ap (ap f)).
          match goal with
          | |- _ = (ap ?ff ?pp1 @ ?pp2) @ ?pp3 => set (p1 := pp1)
          end.
          assert (p1 = ap (transport E' (colimp i j g x)^)
                          (transport_pV E' (colimp i j g x) y)^). {
            subst p1; clear.
            etransitivity. serapply moveL_transport_V_1.
            etransitivity. serapply inverse2. 2: serapply transport_VpV.
            symmetry; apply ap_V. }
          rewrite X. clear X p1.
          rewrite <- ap_compose. cbn.
          rewrite (ap_path_sigma (fun x => E (j; x)) (fun x y => (colim j x; y))).
          cbn. rewrite !concat_p1. rewrite concat_pp_p.
          rewrite ap_V. apply moveL_Vp.
          match goal with
          | |- ?pp1 @ _ = ?pp2 @ _ => set (p1 := pp1); set (p2 := pp2)
          end. cbn in *.
          assert (p1 = path_sigma' E' 1 (transport_Vp _ _ _)). {
            subst p1. rewrite <- ap_existT.
            rewrite (ap_compose (transport E' (colimp i j g x)^)
                                (fun v => (colim j ((D _f g) x); v))).
            f_ap. set (colimp i j g x). clear.
            symmetry. apply transport_VpV. }
          rewrite X; clear p1 X.
          assert (p2 = path_sigma' E' 1 (transport_E'_V _ _ _))
            by reflexivity.
          rewrite X; clear p2 X.
          rewrite <- !path_sigma_pp_pp'. f_ap.
          rewrite concat_p1. rewrite concat_pp_p.
          refine (1 @@ _).
          apply moveL_Mp. rewrite <- ap_V. rewrite <- ap_pp.
          simple refine (_ @ _). refine (ap (transport E' (colimp i j g x)) _).
          refine ((transport_E'_V _ _ _)^ @ _).
          refine (ap _ (transport_pV _ _ _)).
          f_ap. refine (1 @@ _).
          apply transport_VpV.
          set (transport E' (colimp i j g x) (transport E' (colimp i j g x)^ y)).
          rewrite ap_pp. rewrite <- ap_compose.
          refine (_ @ (transport_E'_V_E' _ _ _)^).
          refine (1 @@ _). subst e.
          refine (_ @ (transport_pVp _ _ _)^).
          rewrite ap_compose. f_ap. symmetry.
          apply transport_VpV. }
        rewrite X; hott_simpl.
  Defined.

  Definition flattening_lemma : colimit sigma_diagram <~> sig E'.
  Proof.
    serapply colimit_unicity.
    3: apply is_colimit_colimit.
    serapply Build_is_colimit.
    2: apply is_universal_cocone_E'.
  Defined.
End Flattening.



    
Section POCase.
  Context `{Univalence} {A B C} {f: A -> B} {g: A -> C}.
  
  Context (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Let P : PO f g -> Type.
    simple refine (PO_rec Type B0 C0 _).
    cbn; intro x. eapply path_universe_uncurried.
    etransitivity. symmetry. apply f0. apply g0.
  Defined.

  Let E : dep_diagram (span f g).
    simple refine (Build_diagram _ _ _); cbn.
      intros [[] x]; revert x. exact A0. destruct b; assumption.
      intros [[] x] [[] y] []; cbn; intros [].
      destruct b; intro p. exact (fun y => p # (f0 x y)).
      exact (fun y => p # (g0 x y)).
  Defined.

  Let HE : equifibered _ E.
    intros [] [] [] x; cbn. destruct b; cbn in *.
    apply (f0 x). apply (g0 x).
  Defined.

  Definition PO_flattening
    : PO (functor_sigma f f0) (functor_sigma g g0) <~> exists x, P x.
  Proof.
    assert (PO (functor_sigma f f0) (functor_sigma g g0)
            = colimit (sigma_diagram (span f g) E)). {
    unfold PO; apply ap.
    serapply path_diagram; cbn.
    - intros [|[]]; cbn. all: reflexivity.
    - intros [] [] [] x; destruct b; cbn in *.
      all: reflexivity. }
    rewrite X; clear X.
    transitivity (exists x, E' (span f g) E HE x).
    apply flattening_lemma.
    apply equiv_functor_sigma_id.
    intro x.
    assert (E' (span f g) E HE x = P x). {
      unfold E', P, PO_rec.
      f_ap. serapply path_cocone.
      - intros [[]|[]] y; cbn.
        apply path_universe_uncurried. apply g0.
        all: reflexivity.
      - intros [] [] []; cbn.
        destruct b, u; intro y; simpl; hott_simpl.
        unfold path_universe.
        rewrite <- path_universe_V_uncurried.
        refine (path_universe_compose (f0 y)^-1 (g0 y))^. }
    rewrite X. reflexivity.
  Defined.

End POCase.
