Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Pushout.
Require Import Colimits.SpanPushout.
Require Import Homotopy.Join.Core.
Require Import Truncations.

(** * The Generalized Blakers-Massey Theorem *)

(** ** Path algebra helper lemma *)

(** Here is a strange-looking path algebra helper lemma that is easier to prove by lifting to a general case and doing a path-induction blast.  It says something about what happens when we transport from the center of a based path-space to some other point, assuming we know a particular way to "compute" the action of the type family in question. *)

Definition transport_singleton `{Univalence}
           {A : Type} {x : A} (B : forall (y : A), (x = y) -> Type)
           {y : A} (p : x = y) (u : B x idpath)
           (f : forall (q:x=x), B x q <~> B y (q @ p))
           (ev : ap10 (apD B p) p =
   transport_arrow_toconst p (B x) p @
   path_universe_uncurried
     (@equiv_transport _ (B y) ((p @ p^) @ p) p (concat_pV_p p p)
      oE (f (p @ p^))
      oE @equiv_transport _ (B x)
           (transport (fun y => x = y) p^ p)
           (p @ p^) (transport_paths_r p^ p)))
  : transport (fun yp:{y:A & x=y} => B yp.1 yp.2)
              (path_contr (A := {y:A & x=y}) (x;idpath) (y;p)) u
    = transport (B y) (concat_1p _) (f idpath u).
Proof.
  destruct p; cbn in *.
  apply (fun e => e @ concat_1p _) in ev.
  apply moveR_equiv_V in ev.
  apply (ap equiv_fun) in ev.
  apply ap10 in ev.
  specialize (ev u).
  cbn in ev.
  exact ev.
Defined.

(** ** Setup *)

Section GBM.
    Context {X Y : Type} (Q : X -> Y -> Type).

    (** Here's the hypothesis of ABFJ generalized Blakers-Massey.  It works for any reflective subuniverse, not only modalities! *)
    Context (O : ReflectiveSubuniverse).
    Context
      (isconnected_cogap :
         forall (x1 x3 : X) (y2 y4 : Y)
                (q12 : Q x1 y2) (q32 : Q x3 y2) (q34 : Q x3 y4),
           IsConnected O (Join ((x1;q12) = (x3;q32) :> {x:X & Q x y2})
                               ((y2;q32) = (y4;q34) :> {y:Y & Q x3 y}))).

    Let P := SPushout Q.
    Local Notation left := (spushl Q).
    Local Notation right := (spushr Q).
    Local Notation glue := (spglue Q).

    (** Here's a lemma that's a sort of "singleton contractibility" equivalence, but expressed in a particularly strange way.  As we'll see, this form of the lemma comes up naturally *twice* in the proof, and proving it once here to use in both places is crucial so that the two uses can be identified later on. *)

    Local Definition frobnicate {x0 x1 : X} (r : left x0 = left x1)
          (s : x0 = x1) (y : Y) (q1 : Q x1 y)
      : {q0 : Q x0 y &
              {w : transport (fun x => Q x y) s q0 = q1 &
                   glue q0 @ (glue q1)^ = r } }
          <~> ap left s = r.
    Proof.
      refine (_ oE equiv_sigma_assoc' _ _).
      refine (_ oE equiv_functor_sigma'
                (Q := fun qt => glue qt.1 @ (glue q1)^ = r)
                (equiv_functor_sigma_id
                   (fun q0 : Q x0 y =>
                      equiv_moveL_transport_V
                        (fun x => Q x y) s q0 q1))
                (fun qt => equiv_idmap)).
      refine (_ oE equiv_contr_sigma _); cbn.
      rewrite (ap_transport s^ (fun x q => glue q) q1).
      rewrite (transport_paths_FlFr s^ (glue q1)).
      rewrite ap_V, inv_V, ap_const, concat_p1.
      exact (equiv_concat_l (concat_pp_V _ _)^ _).
      (** Although we proved this lemma with [rewrite], we make it transparent, not so that *we* can reason about it, but so that Coq can evaluate it. *)
    Defined.
    (* But except in one place, we don't want it to try (otherwise things get really slow). *)
    Opaque frobnicate.

    (** ** Codes *)

    (** *** Right-hand codes *)

    (** The right-hand codes family is easy. *)
    Definition coderight {x0 : X} {y : Y} (r : left x0 = right y) : Type
      := O (hfiber glue r).

    (** *** Left-hand codes *)

    (** We enhance the HFLL and ABFJ theorems by defining a version of code-left that doesn't depend on one map being surjective. *)

    Section CodeLeft.
      Context {x0 x1 : X} (r : left x0 = left x1).

      (** The left codes are themselves a pushout, of what is morally also a dependent span, but we formulate it as an ordinary pushout of projections between iterated Sigma-types, most of which we express as records for performance reasons.  The span is [codeleft1] <- [codeleft0] -> [codeleft2]. *)

      Definition codeleft1 : Type
        := { s : x0 = x1 &
          (* v : *) ap left s = r}.

      Record codeleft2
        := { codeleft2_y0  : Y ;
             codeleft2_q00 : Q x0 codeleft2_y0 ;
             codeleft2_q10 : Q x1 codeleft2_y0 ;
             codeleft2_u   : glue codeleft2_q00 @ (glue codeleft2_q10)^ = r }.

      Record codeleft0
        := { codeleft0_s   : x0 = x1 ;
             codeleft0_y0  : Y ;
             codeleft0_v   : ap left codeleft0_s = r ;
             codeleft0_q00 : Q x0 codeleft0_y0 ;
             codeleft0_q10 : Q x1 codeleft0_y0 ;
             codeleft0_w   : transport (fun x => Q x codeleft0_y0) codeleft0_s codeleft0_q00
                             = codeleft0_q10 ;
             codeleft0_u   : glue codeleft0_q00 @ (glue codeleft0_q10)^ = r ;
                   (** Note the first use of frobnicate here. *)
             codeleft0_d   : frobnicate r codeleft0_s codeleft0_y0 codeleft0_q10
                                        (codeleft0_q00 ; codeleft0_w ; codeleft0_u) = codeleft0_v }.

      Definition codeleft01 : codeleft0 -> codeleft1.
      Proof.
        intros [s y0 v q00 q10 w u d].
        exact (s;v).
      Defined.

      Definition codeleft02 : codeleft0 -> codeleft2.
      Proof.
        intros [s y0 v q00 q10 w u d].
        exact (Build_codeleft2 y0 q00 q10 u).
      Defined.

      Definition codeleft : Type
        := O (Pushout codeleft01 codeleft02).

      (** *** Codes for glue *)

      Section CodeGlue.
        Context {y1 : Y} (q11 : Q x1 y1).

        (** We prove that codes respect glue as a chain of equivalences between types built from pushouts and double-pushouts.  The first step is to add the data of our hypothesized-to-be-connected type inside [codeleft2]. *)

        Definition codeleft2plus :=
          {yqqu : codeleft2 &
                  Join ((x0; codeleft2_q00 yqqu) = (x1; codeleft2_q10 yqqu)
                                           :> {x:X & Q x (codeleft2_y0 yqqu)})
                       ((codeleft2_y0 yqqu; codeleft2_q10 yqqu) = (y1; q11)
                                           :> {y:Y & Q x1 y})}.

        (** Since this connected type is itself a join, hence a pushout, the second step is to distribute this and reexpress the whole thing as another pushout of iterated Sigma-types (again mostly expressed as records for performance reasons). *)

        Record Ocodeleft2b
        := { Ocodeleft2b_s   : x0 = x1 ;
             Ocodeleft2b_y0  : Y ;
             Ocodeleft2b_q00 : Q x0 Ocodeleft2b_y0 ;
             Ocodeleft2b_q10 : Q x1 Ocodeleft2b_y0 ;
             Ocodeleft2b_w   : transport (fun x => Q x Ocodeleft2b_y0) Ocodeleft2b_s Ocodeleft2b_q00
                               = Ocodeleft2b_q10 ;
             Ocodeleft2b_u   : glue Ocodeleft2b_q00 @ (glue Ocodeleft2b_q10)^ = r }.

        Definition Ocodeleft2c
          := { q01 : Q x0 y1 &
            (* u: *) glue q01 @ (glue q11)^ = r }.

        Record Ocodeleft2a
        := { Ocodeleft2a_s   : x0 = x1 ;
             Ocodeleft2a_q01 : Q x0 y1 ;
             Ocodeleft2a_w   : transport (fun x => Q x y1) Ocodeleft2a_s Ocodeleft2a_q01 = q11 ;
             Ocodeleft2a_u   : glue Ocodeleft2a_q01 @ (glue q11)^ = r }.

        Definition Ocodeleft2ab : Ocodeleft2a -> Ocodeleft2b.
        Proof.
          intros [s q01 w u].
          exact (Build_Ocodeleft2b s y1 q01 q11 w u).
        Defined.

        Definition Ocodeleft2ac : Ocodeleft2a -> Ocodeleft2c.
        Proof.
          intros [s q01 w u].
          exact (q01;u).
        Defined.

        (** This proof is basically just rearranging Sigma-types/records and paths in Sigma-types and contracting based path spaces. *)
        Definition equiv_Ocodeleft2plus
          : Pushout Ocodeleft2ab Ocodeleft2ac <~> codeleft2plus.
        Proof.
          refine ((equiv_sigma_pushout _ _ _ _ _)^-1 oE _).
          srefine (equiv_pushout _ _ _ _ _).
          - srefine (equiv_functor_sigma_id _ oE _).
            2:intro; refine (equiv_functor_prod' _ _); apply equiv_path_sigma.
            make_equiv_contr_basedpaths.
          - srefine (equiv_functor_sigma_id _ oE _).
            2:intro; apply equiv_path_sigma.
            make_equiv.
          - srefine (equiv_functor_sigma_id _ oE _).
            2:intro; apply equiv_path_sigma.
            make_equiv_contr_basedpaths.
          - intros; reflexivity.
          - intros; reflexivity.
        Defined.

        (** Now we combine this equivalence with the insertion of our connected type. *)
        Definition equiv_Ocodeleft2
          : O (Pushout Ocodeleft2ab Ocodeleft2ac) <~> O codeleft2.
        Proof.
          refine ((equiv_O_functor O (equiv_sigma_contr
                  (fun yqqu : codeleft2 =>
                     O (Join ((x0; codeleft2_q00 yqqu) = (x1; codeleft2_q10 yqqu))
                             ((codeleft2_y0 yqqu ; codeleft2_q10 yqqu) = (y1; q11)))))) oE _).
          refine ((equiv_O_sigma_O O _)^-1 oE _).
          apply equiv_O_functor.
          apply equiv_Ocodeleft2plus.
        Defined.

        (** The next step is to reassociate the resulting double-pushout and "contract" both of them, one after the other, because they are pushouts along equivalences.  In order to do this, we need first of all to know that the resulting map from [codeleft0] to the above pushout factors through [Ocodeleft2b] via an equivalence.  Here's the equivalence: *)

        Definition Ocodeleft02b : codeleft0 <~> Ocodeleft2b.
        Proof.
          make_equiv_contr_basedpaths.
        Defined.

        Definition Ocodeleft02 (c : codeleft0)
          : Pushout Ocodeleft2ab Ocodeleft2ac
          := pushl' Ocodeleft2ab Ocodeleft2ac (Ocodeleft02b c).

        Definition Ocodeleft02plus_02b (c : codeleft0)
          : (equiv_Ocodeleft2plus (Ocodeleft02 c)).1 = codeleft02 c.
        Proof.
          destruct c; reflexivity.
        Qed.

        (** And here we show that this equivalence is indeed a factor of the relevant map in the original pushout. *)

        Definition Ocodeleft02_02b (c : codeleft0)
          : equiv_Ocodeleft2 (to O _ (Ocodeleft02 c)) = to O _ (codeleft02 c).
        Proof.
          destruct c.
          unfold equiv_Ocodeleft2.
          Opaque equiv_Ocodeleft2plus.
          cbn.
          refine (ap _ (ap _ (to_O_natural _ _ _)) @ _).
          refine (ap _ (to_O_natural _ _ _) @ _).
          refine (to_O_natural _ _ _ @ _).
          apply ap.
          rapply Ocodeleft02plus_02b.
        Qed.

        (** Thus, our pushout in which one vertex is itself a pushout can be written as a "double pushout"

[codeleft1] <- [codeleft0] -> [codeleft2b] <- [codeleft2a] -> [codeleft2c].

Since the map [codeleft0] -> [codeleft2b] is an equivalence, the pushout of the left-hand span is equivalent to [codeleft1], and thus the whole thing is equivalent to a pushout

[codeleft1] <- [codeleft2a] -> [codeleft2c]

Now we claim that the left-hand map of this span is also an equivalence.  Rather than showing this directly, it seems to be much easier to first construct *an* equivalence from [codeleft2a] to [codeleft1] and then show that it is equal (as a function) to the induced one.  Here's the equivalence: *)

        Definition Ocodeleft2a1 : Ocodeleft2a <~> codeleft1.
        Proof.
          etransitivity.
          2:{ rapply equiv_functor_sigma_id; intros s.
              (** Here's frobnicate showing up again! *)
              apply frobnicate. }
          make_equiv.
        Defined.

        (** And now we check that the two are equal.  Because we used the same proof of [frobnicate] in two places, this equality becomes definitional after simply decomposing up a Sigma-type! *)
        Definition Ocodeleft2a1_through_2b0
          : Ocodeleft2a1 == codeleft01 o Ocodeleft02b^-1 o Ocodeleft2ab.
        Proof.
          intros; reflexivity.
        Defined.

        (** Now we're finally ready to prove the glue equivalence.  Since later on we'll have to compute its action on inputs from [codeleft1], we decompose it into seven steps, each of which with a corresponding computation lemma.  (These lemmas seem to be much easier to prove step-by-step than all at once if we proved the whole equivalence in a big shebang.) *)

        Definition codeglue1
          : codeleft <~> O (Pushout (O_functor O codeleft01)
                                    (O_functor O codeleft02))
        := equiv_O_pushout O _ _.

        Definition codeglue1_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue1 (to O _ (pushl (s;v))) =
            to O _ (pushl (to O _ (s; v)))
          := equiv_O_pushout_to_O_pushl _ _ _ _.

        Definition codeglue2
          : O (Pushout (O_functor O codeleft01) (O_functor O codeleft02))
        <~> O (Pushout (O_functor O codeleft01) (O_functor O Ocodeleft02)).
        Proof.
          srefine (equiv_O_functor O
                    (equiv_inverse
                    (equiv_pushout (f := O_functor O codeleft01)
                                   (g := O_functor O Ocodeleft02)
                                   1%equiv 1%equiv equiv_Ocodeleft2 _ _))).
          - intros x; reflexivity.
          - apply O_indpaths; intros x.
            abstract (rewrite !to_O_natural; apply Ocodeleft02_02b).
        Defined.

        Definition codeglue2_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue2 (to O _ (pushl (to O _ (s;v))))
            = to O _ (pushl (to O _ (s;v)))
          := to_O_equiv_natural _ _ _.

        Definition codeglue3
          : O (Pushout (O_functor O codeleft01) (O_functor O Ocodeleft02))
              <~> O (Pushout codeleft01 Ocodeleft02)
          := equiv_inverse (equiv_O_pushout O _ _).

        Definition codeglue3_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue3 (to O _ (pushl (to O _ (s;v))))
            = to O _ (pushl (s;v))
          := inverse_equiv_O_pushout_to_O_pushl _ _ _ _.

        Definition codeglue4
          : O (Pushout codeleft01 Ocodeleft02)
            <~> O (Pushout
                     (fun x : Ocodeleft2a =>
                        pushr' codeleft01 Ocodeleft02b (Ocodeleft2ab x))
                     Ocodeleft2ac)
          := equiv_O_functor O (equiv_inverse (equiv_pushout_assoc _ _ _ _)).

        Definition codeglue4_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue4 (to O _ (pushl (s;v)))
            = to O _ (pushl (pushl (s;v)))
          := to_O_equiv_natural _ _ _.

        Definition codeglue5
          : O (Pushout
                 (fun x : Ocodeleft2a =>
                    pushr' codeleft01 Ocodeleft02b (Ocodeleft2ab x))
                 Ocodeleft2ac)
        <~> O (Pushout Ocodeleft2a1 Ocodeleft2ac).
        Proof.
          srefine (equiv_O_functor O
                     (equiv_inverse
                        (equiv_pushout (f := Ocodeleft2a1) (g := Ocodeleft2ac)
                                       1%equiv _ 1%equiv _ _))).
          - exact (Build_Equiv _ _ (pushl' codeleft01 Ocodeleft02b) _).
          - intros x.
            refine (ap _ (Ocodeleft2a1_through_2b0 x) @ _).
            refine (pglue' codeleft01 Ocodeleft02b _ @ _).
            apply ap, eisretr.
          - intros x; reflexivity.
        Defined.

        Definition codeglue5_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue5 (to O _ (pushl (pushl (s;v))))
            = to O _ (pushl (s;v))
        := to_O_equiv_natural _ _ _.

        Definition codeglue6
          : O (Pushout Ocodeleft2a1 Ocodeleft2ac) <~> O Ocodeleft2c
          := equiv_O_functor
               O (equiv_inverse
                    (Build_Equiv _ _ (pushr' Ocodeleft2a1 Ocodeleft2ac) _)).

        Definition codeglue6_pushl (s : x0 = x1) (v : ap left s = r)
          : codeglue6 (to O _ (pushl (s;v)))
            = let z := (frobnicate r s y1 q11)^-1 v in
              to O Ocodeleft2c (Ocodeleft2ac (Build_Ocodeleft2a s z.1 z.2.1 z.2.2))
          := to_O_equiv_natural _ _ _.

        Definition codeglue7
          : O Ocodeleft2c <~> coderight (r @ glue q11).
        Proof.
          unfold coderight, Ocodeleft2c.
          apply equiv_O_functor.
          apply equiv_functor_sigma_id; intros q01.
          apply equiv_moveL_pM.
        Defined.

        Definition codeglue7_to_O
                   (q01 : Q x0 y1) (u : glue q01 @ (glue q11)^ = r)
          : codeglue7 (to O _ (q01;u))
            = to O (hfiber glue (r @ glue q11))
                 (q01 ; moveL_pM (glue q11) (glue q01) r u)
          := to_O_equiv_natural _ _ _.

        Definition codeglue
          : codeleft <~> coderight (r @ glue q11)
          := codeglue7 oE
             codeglue6 oE
             codeglue5 oE
             codeglue4 oE
             codeglue3 oE
             codeglue2 oE
             codeglue1.

      End CodeGlue.

    End CodeLeft.

    (** *** Completion of codes *)

    Context `{Univalence}.
    Context (x0 : X).

    (** The equivalence [codeglue] requires a bit of massaging to put it into the form needed by the actual definition of [code] from pushout-induction and univalence. *)

    Definition ap_code_glue (x1 : X) (y1 : Y) (q11 : Q x1 y1)
      : transport (fun p : SPushout Q => left x0 = p -> Type)
                  (glue q11) codeleft
        = coderight.
    Proof.
      apply path_arrow; intros z.
      refine ((transport_arrow_toconst _ _ _) @ _).
      apply path_universe_uncurried.
      refine (_ oE equiv_transport codeleft (transport_paths_r _ _)).
      refine (_ oE codeglue _ q11).
      refine (equiv_transport coderight _).
      refine (concat_pV_p z (glue q11)).
    Defined.

    (** Here's the final definition of [code]. *)

    Definition code (p : P) (r : left x0 = p) : Type
        := spushout_ind Q (fun p => left x0 = p -> Type)
                        (@codeleft x0) (@coderight x0)
                        ap_code_glue p r.

    (** When we compute with [code], we'll need to extract from it the actual behavior of the function [codeglue].  Here's the mess of path algebra that we "naturally" get out when we try to do that; later we'll see how to deal with it. *)
    Definition code_beta_glue (x1 : X) (y1 : Y) (q11 : Q x1 y1)
               (r : left x0 = right y1)
      : ap10 (apD code (glue q11)) r
        = transport_arrow_toconst (glue q11) codeleft r
        @ path_universe_uncurried
           (@equiv_transport _ coderight ((r @ (glue q11)^) @ glue q11) r
                            (concat_pV_p r (glue q11))
            oE (codeglue (r @ (glue q11)^) q11)
            oE @equiv_transport _ codeleft
                 (transport (fun y : SPushout Q => left x0 = y) (glue q11)^ r)
                 (r @ (glue q11)^) (transport_paths_r (glue q11)^ r)).
    Proof.
      refine (ap (fun h => ap10 h r)
             (spushout_ind_beta_spglue Q (fun p => left x0 = p -> Type)
                                  (@codeleft x0) (@coderight x0)
                                  ap_code_glue
                                  x1 y1 q11) @ _).
      refine (ap10_path_arrow _ _ _ _).
    Defined.

    (** ** Contractibility of codes *)

    (** To construct a center for every type of codes, we construct one in an easy case and transport it around. *)

    Definition center_code1 : code (left x0) 1.
    Proof.
      change (codeleft (idpath (left x0))).
      unfold codeleft.
      apply to, pushl.
      unfold codeleft1.
      exact (idpath; idpath).
    Defined.

    Definition center_code (p : P) (r : left x0 = p) : code p r
      := transport (fun (pr : {p : P & left x0 = p}) => code pr.1 pr.2)
                   (path_contr (A := {p : P & left x0 = p})
                               (left x0; idpath) (p;r))
                   center_code1.

    (** As in HFLL, we first construct a contraction in the "partially general" case of an arbitrary path from left to right. *)

    Definition contraction_code_right (y1 : Y) (r : left x0 = right y1)
               (c : code (right y1) r)
      : center_code (right y1) r = c.
    Proof.
      change (coderight r) in c.
      unfold coderight in c.
      revert c; refine (O_indpaths _ _ _); intros [q01 t].
      unfold center_code, center_code1.
      (** Here's how we use the apparently-unmanageable [code_beta_glue].  First we destruct the path [t] to make things simpler. *)
      destruct t.
      (** Then we notice that if we tried rewriting with [code_beta_glue] here, the unmanageable-looking result is actually fully general over the path [glue q01], so we can prove by path induction that it equals the nicer expression we'd like to see.  This is the purpose of the lemma [transport_singleton]. *)
      rewrite (transport_singleton
                 code (glue q01) _
                 (fun r => @codeglue x0 x0 r y1 q01)
                 (code_beta_glue x0 y1 q01 (glue q01))).
      unfold codeglue.
      (** Now we evaluate [codeglue] step by step using our lemmas. *)
      do 6 change_apply_equiv_compose.
      rewrite codeglue1_pushl, codeglue2_pushl, codeglue3_pushl,
      codeglue4_pushl, codeglue5_pushl, codeglue6_pushl, codeglue7_to_O.
      rewrite <- (ap_transport (concat_1p (glue q01))
                               (fun r => to O (hfiber glue r)) _).
      apply ap; unfold hfiber; rewrite transport_sigma'.
      apply ap; rewrite transport_paths_r.
      (** Finally, we have another terrible-looking thing involving [frobnicate].  However, there are enough identity paths that [frobnicate] evaluates to... something that's almost fully path-general!  So with just a little bit of further work, we can reduce it also to something we can prove with path-induction. *)
      Transparent frobnicate.
      cbn.
      Opaque frobnicate.
      rewrite (transport_compose (fun q => glue q @ (glue q01)^ = 1%path) pr1).
      unfold path_sigma'; rewrite ap_V, ap_pr1_path_sigma, transport_1.
      destruct (glue q01); reflexivity.
    Qed.

    (** It should be possible to prove an analogous [contraction_code_left] directly, but for now we follow HFLL and ABFJ by introducing a surjectivity assumption. *)

    Definition contraction_code {y0 : Y} (q00 : Q x0 y0)
               (pr : { p : P & left x0 = p }) (c : code pr.1 pr.2)
      : center_code pr.1 pr.2 = c.
    Proof.
      revert c.
      srefine (transport (fun pr' => forall c, center_code pr'.1 pr'.2 = c)
                         (path_contr (right y0 ; glue q00) pr) _).
      clear pr; cbn; intros c.
      apply contraction_code_right.
    Defined.

    Definition contr_code_inhab (inh : merely { y0 : Y & Q x0 y0 })
               (p : P) (r : left x0 = p)
      : Contr (code p r).
    Proof.
      strip_truncations.
      destruct inh as [y0 q00].
      exact (Build_Contr _ (center_code p r) (contraction_code q00 (p;r))).
    Defined.

    (** This version is sufficient for the classical Blakers-Massey theorem, as we'll see below, since its leg-wise connectivity hypothesis implies the above surjectivity assumption.  ABFJ have a different method for eliminating the surjectivity assumption using a lemma about pushouts of monos also being pullbacks, though it seems to only work for coderight. *)

End GBM.

(** ** The classical Blakers-Massey Theorem *)

Global Instance blakers_massey `{Univalence} (m n : trunc_index)
           {X Y : Type} (Q : X -> Y -> Type)
           `{forall y, IsConnected m.+1 { x : X & Q x y } }
           `{forall x, IsConnected n.+1 { y : Y & Q x y } }
           (x : X) (y : Y)
  : IsConnMap (m +2+ n) (@spglue X Y Q x y).
Proof.
  intros r.
  snrefine (contr_code_inhab Q (m +2+ n) _ x
                            (merely_isconnected n _) (spushr Q y) r).
  1: intros; apply isconnected_join.
  all: exact _.
Defined.
