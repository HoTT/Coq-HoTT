Require Import HoTT.Basics HoTT.Types HoTT.HIT.Coeq.
Require Import Colimits.Diagram Colimits.Colimit.
Generalizable All Variables.

Context `{Funext}.
  
Definition coequalizer_graph : graph.
  simple refine (Build_graph _ _).
  - exact Bool.
  - intros i j; exact (if i then if j then Empty else Bool else Empty).
Defined.


Section Coequalizer.
  Context {B A : Type}.
  
  Definition coequalizer_diag (f g : B -> A) : diagram coequalizer_graph.
    simple refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact B. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact f. exact g.
  Defined.

  Definition Build_coequalizer_cocone {f g : B -> A}
             `(q: A -> Q) (Hq: q o g == q o f)
    : cocone (coequalizer_diag f g) Q.
  Proof.
    simple refine (Build_cocone _ _).
    - destruct i; cbn. exact (q o f). exact q.
    - destruct i, j, g0; cbn. reflexivity. exact Hq.
  Defined.

  Definition is_coequalizer (f g : B -> A)
    := is_colimit (coequalizer_diag f g).
  Definition Coequalizer (f g : B -> A)
    := colimit (coequalizer_diag f g).



  (* ***************** *)
  (* ***** Coeq ****** *)
  (* ***************** *)
  (* We show here that the coequalizer defined as a colimit *)
  (* is equivalent to the coequalizer defined as a primitive HIT. *)
  
  Context {f g : B -> A}.

  Definition Coeq_cocone : cocone (coequalizer_diag f g) (Coeq f g).
    simple refine (Build_cocone _ _).
    - intros i x; destruct i; simpl in *.
      exact (coeq (g x)). exact (coeq x).
    - intros i j phi x; destruct i, j, phi; simpl.
      exact (cp x). reflexivity.
  Defined.

  Lemma is_coequalizer_Coeq : is_colimit (coequalizer_diag f g) (Coeq f g).
  Proof.
    simple refine (Build_is_colimit Coeq_cocone _).
    intros X.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros C. simple refine (Coeq_rec _ _ _). exact (q C false).
      intros b. etransitivity.
      exact (qq C true false true b).
      exact (qq C true false false b)^.
    - intros C. simple refine (path_cocone _ _).
      + intros i x; destruct i; simpl.
        exact (qq C true false false x). reflexivity.
      + intros i j phi x; destruct i, j, phi; simpl.
        * hott_simpl.
          match goal with
          | [|- ap (Coeq_rec ?a ?b ?c) _ @ _ = _ ]
            => rewrite (Coeq_rec_beta_cp a b c)
          end. hott_simpl.
        * reflexivity.
    - intros F. apply path_forall.
      match goal with
        | [|- ?G == _ ] => simple refine (Coeq_ind (fun w => G w = F w) _ _)
      end.
      + simpl. reflexivity.
      + intros b. simpl.
        rewrite transport_paths_FlFr.
        rewrite Coeq_rec_beta_cp. hott_simpl.
  Defined.

  Definition equiv_Coeq_Coequalizer
    : Coeq f g <~> Coequalizer f g.
  Proof.
    serapply colimit_unicity.
    3: eapply is_coequalizer_Coeq.
    eapply is_colimit_colimit.
  Defined.

End Coequalizer.
