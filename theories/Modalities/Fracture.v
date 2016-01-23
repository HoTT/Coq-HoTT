(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations Extensions Pullback NullHomotopy.
Require Import Modality Lex Open Closed Nullification.
Require Import HoTT.Tactics.

Local Open Scope path_scope.


(** * The lex-modal fracture theorem *)

(** The fracture theorem for two modalities [O1] and [O2] and a type [A], when it holds, states that the naturality square

<<
 A   -->   O1 A
 |          |
 |          |
 V          V
O2 A --> O2 (O1 A)
>>

is a pullback.  This says in a certain precise sense that [A] can be recovered from its [O1]- and [O2]-reflections together with some information about how they fit together.  If we think of [O1] and [O2] as subuniverses or subtoposes, then the fracture theorem says that their "union", or more precisely their *gluing*, is the whole universe.

We will prove the fracture theorem holds under the assumptions that [O2] is lex, and that [O1]-connected types are [O2]-modal.  Note that like lex-ness, the latter is also a "large" hypothesis.  But also as with lex-ness, rather than hypothesize it polymorphically with a module type, we just hypothesize it in the obvious way and allow the polymophism of the resulting theorem to be computed automatically.  This actually gives more precise information: the fracture theorem for a particular type [A] only depends on this hypothesis for types [B] lying in the same universe as [A].  (In fact, as we will see, it only needs the special cases of the fibers of [to O1 A], but in examples it seems no harder to verify the general case.)

It may sometimes happen that in addition, the "intersection" of [O1] and [O2] is trivial.  This is naturally expressed in the context of the fracture theorem by saying that [O2]-modal types are [O1]-connected, i.e. the converse of the second hypothesis of our fracture theorem.  When this also holds, we can show that the universe [Type] can actually be reconstructed, up to equivalence, from the universes of [O1]- and [O2]-modal types and the [O2]-reflection from the first to the second, using the "Artin gluing construction" from topos theory.  *)

Module Fracture (Os : Modalities).

  Module Export OsL := Lex_Modalities_Theory Os.

  (** ** The fracture theorem *)

  Section FractureTheorem.
    Context (O1 O2 : Modality).

    Definition fracture_square (A : Type)
    : O_functor O2 (to O1 A) o to O2 A == to O2 (O1 A) o to O1 A
    := to_O_natural O2 (to O1 A).

    (** Here are the hypotheses of the fracture theorem *)
    Context `{Lex O2}.

    Definition Gluable : Type
      := forall (A : Type), IsConnected O1 A -> In O2 A.
    Context (ino2_isconnectedo1 : Gluable).

    (** The fracture theorem. *)
    Definition ispullback_fracture_square A
    : IsPullback (fracture_square A).
    Proof.
      refine (ispullback_connmap_mapino_commsq O2 _).
      (** And typeclass magic finds everything except the one we need our hypothesis for. *)
      intros x; refine (ino2_isconnectedo1 _ _).
    Defined.

    (** ** The fracture gluing theorem *)

    (** We now also assume the converse of the second hyopthesis *)
    Definition Disjoint : Type
      := forall (A : Type), In O2 A -> IsConnected O1 A.
    Context (isconnectedo1_ino2 : Disjoint).

    (** This implies that the universe decomposes into an [O1]-part, an [O2]-part, and a gluing map.  We define these pieces separately in order to make the maps transparent but the homotopies opaque. *)
    Definition fracture_glue_uncurried
    : { B : Type_ O1 & { C : Type_ O2 & C -> O2 B }} -> Type
      := fun BCf => Pullback BCf.2.2 (to O2 BCf.1).

    Definition fracture_glue
      (B C : Type) `{HB: In O1 B} `{HC: In O2 C} (f : C -> O2 B)
    : Type
      := fracture_glue_uncurried ((B;HB);((C;HC);f)).

    Definition fracture_unglue
    : Type -> { B : Type_ O1 & { C : Type_ O2 & C -> O2 B }}
    := fun A => ((O1 A ; O_inO A) ; ((O2 A ; O_inO A) ; O_functor O2 (to O1 A))).

    Definition fracture_unglue_isretr `{Univalence}
               (BCf : { B : Type_ O1 & { C : Type_ O2 & C -> O2 B }})
    : fracture_unglue (fracture_glue_uncurried BCf) = BCf.
    Proof.
      destruct BCf as [B [C f]]; simpl.
      (** The first two components of our path will be applications of univalence.  We begin by observing that maps we will use are equivalences. *)
      assert (IsEquiv (O_rec ((to O2 B)^*' f))).
      { apply isequiv_O_rec_O_inverts.
        apply O_inverts_conn_map, conn_map_pullback'.
        intros ob; apply isconnectedo1_ino2; exact _. }
      assert (IsEquiv (O_rec (f^* (to O2 B)))).
      { apply isequiv_O_rec_O_inverts.
        apply O_inverts_conn_map, conn_map_pullback; exact _. }
      (** Now we start building the path. *)
      simple refine (path_sigma' _ _ _).
      { apply path_TypeO; simpl.
        refine (path_universe (O_rec ((to O2 B)^*' f))). }
      refine (transport_sigma' _ _ @ _); simpl.
      simple refine (path_sigma' _ _ _).
      { apply path_TypeO; simpl.
        refine (path_universe (O_rec (f^* (to O2 B)))). }
      (** It remains to identify the induced function with the given [f].  We begin with some boilerplate. *)
      apply path_arrow; intros c.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (transport_arrow_fromconst
                (C := fun X:Type_ O1 => O2 X) _ _ _ @ _).
      refine (transport_compose O2 (TypeO_pr1 O1) _ _ @ _).
      refine (transport_compose idmap O2 _ _ @ _).
      (** Now we have to compute through the action of [ap] and [transport] on paths in sigmas and the universe.  In applying these it helps to specify a couple of intermediate steps explicitly. *)
      transitivity (transport idmap
                     (ap O2 (path_universe (O_rec ((to O2 B)^*' f))))
                     (O_functor O2 (to O1 (Pullback f (to O2 B)))
                                ((O_rec (f^* (to O2 B)))^-1 c)));
        [ apply ap11; repeat apply ap
        | transitivity (O_functor O2 (O_rec (to O2 B^*' f))
                          (O_functor O2 (to O1 (Pullback f (to O2 B)))
                                     ((O_rec (f^* (to O2 B)))^-1 c))) ].
      + refine (pr1_path_sigma_uncurried _ @ eisretr pr1 _).
      + refine (transport_compose idmap (TypeO_pr1 O2)
                  (path_TypeO O2 (O2 (Pullback f (to O2 B)); _) C _)^
                  c @ _).
        refine (ap (fun p => transport idmap p c) (ap_V _ _) @ _).
        refine (ap (fun p => transport idmap p^ c)
                   (pr1_path_sigma_uncurried _ @ eisretr pr1 _) @ _).
        refine (transport_path_universe_V _ _).
      + refine (ap (fun p => transport idmap p _)
                   (ap_O_path_universe O2 _) @ _).
        refine (transport_path_universe _ _).
      (** Now we're down to the real point. *)
      + refine ((O_functor_compose O2 _ _ _)^ @ _).
        refine (O_functor_homotopy O2 _ _ (O_rec_beta _) _ @ _).
        revert c; equiv_intro (O_rec (f^* (to O2 B))) x.
        refine (ap _ (eissect _ _) @ _).
        revert x; apply O_indpaths; intros x; simpl.
        refine (to_O_natural O2 _ x @ _); simpl.
        refine (_ @ ap f (O_rec_beta _ _)^).
        destruct x as [a [b q]]; simpl; exact (q^).
    Qed.

    Definition fracture_unglue_issect `{Univalence} (A : Type)
    : fracture_glue_uncurried (fracture_unglue A) = A.
    Proof.
      apply path_universe_uncurried, equiv_inverse.
      exact (BuildEquiv _ _ (pullback_corec (fracture_square A))
                        (ispullback_fracture_square A)).
    Qed.

    Definition isequiv_fracture_unglue `{Univalence}
    : IsEquiv fracture_unglue
      := isequiv_adjointify
           fracture_unglue
           fracture_glue_uncurried
           fracture_unglue_isretr
           fracture_unglue_issect.

    Definition equiv_fracture_unglue `{Univalence}
    : Type <~> { B : Type_ O1 & { C : Type_ O2 & C -> O2 B }}
      := BuildEquiv _ _ fracture_unglue isequiv_fracture_unglue.

  End FractureTheorem.

End Fracture.

(** ** The propositional fracture theorem *)

(** An easy example of the lex-modal fracture theorem is supplied by the open and closed modalities for an hprop [U].  In order to consider these together, we need to build their union as a family of modalities. *)

Module Open_And_Closed_Modalities
  := Modalities_FamUnion OpenModalities ClosedModalities.
Module Import OpClM := Lex_Modalities_Theory Open_And_Closed_Modalities.
Module Import Propositional_Fracture
  := Fracture Open_And_Closed_Modalities.

Definition gluable_open_closed `{Funext} (U : hProp)
: Gluable (Op U) (Cl U).
Proof.
  intros A.
  change (Contr (U -> A) -> (U -> Contr A)); intros ? u.
  exists (center (U -> A) u); intros a.
  exact (ap10 (path_contr _ (fun _ => a)) u).
Defined.

Definition disjoint_open_closed `{Funext} (U : hProp)
: Disjoint (Op U) (Cl U).
Proof.
  intros A.
  change ((U -> Contr A) -> Contr (U -> A)); intros uc.
  exists (fun u => let i := uc u in center A).
  intros f; apply path_arrow; intros u.
  pose (uc u); apply path_contr.
Defined.

(** We can also prove the same thing without funext if we use the nullification versions of these modalities. *)

Import NulM.
Module Import Propositional_Fracture'
  := Fracture Nullification_Modalities.

Definition gluable_open_closed' (U : hProp)
: Gluable (Op' U) (Cl' U).
Proof.
  intros A ? u; simpl in *.
  pose proof (contr_inhabited_hprop U u).
  assert (Contr A).
  { simple refine (contr_equiv (Op' U A) _).
    - refine (O_rec idmap).
      intros []; simpl.
      apply ooextendable_equiv.
      refine (equiv_isequiv (@equiv_contr_contr U Unit _ _)).
    - refine (isequiv_adjointify _ (to (Op' U) A) _ _).
      + intros a; apply O_rec_beta.
      + intros oa; revert oa; apply O_indpaths; intros a; simpl.
        apply ap, O_rec_beta. }
  apply ooextendable_contr; exact _.
Defined.

Definition disjoint_open_closed' (U : hProp)
: Disjoint (Op' U) (Cl' U).
Proof.
  intros A An.
  apply isconnected_from_elim; intros C Cn f.
  simple refine (@local_rec _ C Cn tt _ tt ; _); simpl.
  - intros u.
    exact (f (@local_rec _ A An u Empty_rec tt)).
  - intros a; simpl.
    refine (@local_indpaths _ C Cn tt (fun _ => f a) _ _ tt);
      intros u; simpl in *.
    refine (_ @ (@local_rec_beta _ C Cn tt _ u)^).
    apply ap.
    exact (@local_indpaths _ A An u (fun _ => a) _ (Empty_ind _) tt).
Defined.
