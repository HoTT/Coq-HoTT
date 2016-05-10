(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext.
Require Import Modalities.Modality Modalities.Open.
Import OpM.

Local Open Scope path_scope.

(** * Coreflective subuniverses. *)

(** In this file we study "coreflective subuniverses" that are defined dually to reflective subuniverses.  However, it turns out that there are many fewer examples of these.  The "internal" nature of such definitions, which in the reflective case makes the subuniverse automatically an exponential ideal, in the coreflective case has much stronger consequences: it forces the entire coreflection to be determined by the image of [Unit], which can be an arbitrary hprop.  Thus, this file is essentially just a no-go theorem: there are no coreflective subuniverses other than a certain class of fairly simple ones (which we call "co-open" since they are dual to open modalities).

In particular, since we do not foresee many applications of this file, we don't bother introducing modules to make the definitions more universe polymorphic the way we did for reflective subuniverses. *)

Record CoreflectiveSubuniverse :=
  { inF : Type -> hProp ;
    F_coreflector : Type -> Type ;
    F_inF : forall X, inF (F_coreflector X) ;
    fromF : forall X, F_coreflector X -> X ;
    (** We also don't bother defining [ooLiftableAlong] so as to state the universal property without [Funext]. *)
    isequiv_fromF_postcompose
    : forall {Y X} {Y_inF : inF Y},
        IsEquiv (fun (g : Y -> F_coreflector X) => fromF X o g)
    (** Similarly, we don't bother asserting repleteness; we'll just use univalence. *)
  }.

Coercion F_coreflector : CoreflectiveSubuniverse >-> Funclass.

Section CoreflectiveSubuniverse.
  Context `{Univalence}.
  Context {F : CoreflectiveSubuniverse}.

  (** We begin by extracting the corecursor, its computation rule, and its eta principle. *)

  Definition F_corec {Y X} `(inF F Y) (f : Y -> X) : Y -> F X.
  Proof.
    refine ((fun (g : Y -> F X) => fromF F X o g)^-1 f).
    by apply isequiv_fromF_postcompose.
  Defined.

  Definition F_corec_beta {Y X} (YF : inF F Y) (f : Y -> X)
  : fromF F X o F_corec YF f == f.
  Proof.
    apply ap10, (eisretr (fun g => fromF F X o g)).
  Defined.

  Definition F_coindpaths {Y X} `(inF F Y) (g h : Y -> F X)
             (p : fromF F X o g == fromF F X o h)
  : g == h.
  Proof.
    apply ap10.
    refine (equiv_inj (fun k => fromF F X o k) _).
    - by apply isequiv_fromF_postcompose.
    - by apply path_arrow.
  Defined.

  (** The functorial action of the coreflector. *)
  Definition F_functor {X Y} (f : X -> Y) : F X -> F Y
    := F_corec (F_inF F X) (f o fromF F X).

  (** The coreflector preserves hprops (since it is a right adjoint and thus preserves limits). *)
  Local Instance ishprop_coreflection A `{IsHProp A} : IsHProp (F A).
  Proof.
    apply hprop_allpath; intros x y.
    exact (F_coindpaths (F_inF F A) (const x) (const y)
                        (fun _ => path_ishprop _ _) x).
  Defined.

  (** A type lies in [F] as soon as [fromF] admits a section. *)
  Definition inF_fromF_sect X (s : X -> F X) (p : fromF F X o s == idmap)
  : inF F X.
  Proof.
    refine (transport (inF F) (path_universe (fromF F X)) (F_inF F X)).
    refine (isequiv_adjointify _ s p _).
    change (s o fromF F X == idmap).
    apply F_coindpaths; try apply F_inF.
    intros x; apply p.
  Defined.

  (** So far, nothing unexpected has happened.  Now, however, we claim that [F] is completely determined by the image of [Unit], which by [ishprop_coreflection] is an hprop.  Specifically, we claim that [X] lies in [F] exactly when [X -> F Unit]. *)
  Definition inF_equiv_implies_funit X
  : inF F X <~> (X -> F Unit).
  Proof.
    apply equiv_iff_hprop.
    - intros ?. apply F_corec; try assumption.
      exact (fun _ => tt).
    - intros f.
      simple refine (inF_fromF_sect X _ _).
      + intros x.
        exact (F_functor (unit_name x) (f x)).
      + intros x; unfold F_functor.
        exact (F_corec_beta (F_inF F Unit) (const x) (f x)).
  Defined.

End CoreflectiveSubuniverse.

(** Conversely, we will now show that for any hprop [U], the types [X] such that [X -> U] are a coreflective subuniverse, which we call "co-open" since it is dual to the open modality. *)

Section CoOpen.
  Context `{Funext} (U : hProp).

  Definition coOp : CoreflectiveSubuniverse.
  Proof.
    simple refine (Build_CoreflectiveSubuniverse
              (fun X => BuildhProp (X -> U))
              (fun X => X * U)
              (fun X => @snd X U)
              (fun X => @fst X U) _); try exact _.
    intros Y X YU; simpl in *.
    refine (isequiv_adjointify _ (fun h y => (h y , YU y)) _ _).
    - intros g; apply path_arrow; intros y; reflexivity.
    - intros h; apply path_arrow; intros y.
      apply path_prod; [ reflexivity | by apply path_ishprop ].
  Defined.

  (** Thus, each coreflective subuniverses are uniquely determined by an hprop.  Moreover, the coreflective subuniverse corresponding to an hprop [U] is closely related to the open modality [Op U].  Specifically, they form an _adjoint modality pair_ in the sense that the subuniverses are canonically equivalent, and the coreflection and reflection respect this equivalence.  In categorical language, this says that the inclusion of an open subtopos is the center of a local geometric morphism in the other direction.  We express this concisely as follows. *)

  Definition coopen_isequiv_open X
  : IsEquiv (O_functor (Op U) (fromF coOp X)).
  Proof.
    refine (isequiv_adjointify _ (fun ux => fun u => (ux u , u)) _ _).
    - intros ux; simpl in *.
      apply path_arrow; intros u.
      transitivity (O_functor (Op U) fst (to (Op U) (X * U) (ux u , u)) u).
      + apply ap10, ap, path_arrow; intros u'; simpl in *.
        apply path_prod; simpl; [ apply ap | ]; apply path_ishprop.
      + exact (ap10 (to_O_natural (Op U) (@fst X U) (ux u , u)) u).
    - intros uux; simpl in *.
      apply path_arrow; intros u.
      apply path_prod; [ simpl | apply path_ishprop ].
      transitivity (O_functor (Op U) fst (to (Op U) _ (fst (uux u) , u)) u).
      + apply ap10, ap, path_arrow; intros u'.
        apply path_prod; simpl.
        * exact (ap fst (ap uux (path_ishprop u' u))).
        * apply path_ishprop.
      + exact (ap10 (to_O_natural (Op U) (@fst X U) (fst (uux u) , u)) u).
  Defined.

  Definition coopen_equiv_open X
  : Op U (coOp X) <~> Op U X
    := BuildEquiv _ _ (O_functor (Op U) (fromF coOp X))
                  (coopen_isequiv_open X).

End CoOpen.
