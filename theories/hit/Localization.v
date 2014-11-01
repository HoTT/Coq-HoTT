(* -*- mode: coq; mode: visual-line -*-  *)
(** * Localization *)

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions Factorization ReflectiveSubuniverse Modality EquivalenceVarieties.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** Suppose given a family of maps [f : forall (i:I), S i -> T i].  A type [X] is said to be [f]-local if for all [i:I], the map [(T i -> X) -> (S i -> X)] given by precomposition with [f i] is an equivalence.  Our goal is to show that the [f]-local types form a reflective subuniverse, with a reflector constructed by localization.  That is, morally we want to say

    Inductive Localize f (X : Type) : Type :=
    | loc : X -> Localize X
    | islocal_localize : forall i, IsEquiv (fun (g : T i -> X) => g o f i).

This is not a valid HIT by the usual rules, but if we expand out the definition of [IsEquiv] and apply [path_sigma] and [path_forall], then it becomes one.  We get a simpler definition (no 2-path constructors) if we do this with [BiInv] rather than [IsEquiv]:

    Inductive Localize f (X : Type) : Type :=
    | loc : X -> Localize X
    | lsect : forall i (g : S i -> X), T i -> X
    | lissect : forall i (g : S i -> X) (s : S i), lsect i g (f i s) = g s
    | lretr : forall i (g : S i -> X), T i -> X
    | lisretr : forall i (h : T i -> X) (t : T i), lretr i (h o f i) t = h t.

This definition works, and from it one can prove that the [f]-local types form a reflective subuniverse.  However, the proof inextricably involves [Funext].  We can avoid [Funext] in the same way that we did in the definition of a [ReflectiveSubuniverse], by using pointwise path-split precomposition equivalences.  Observe that the assertion [ExtendableAlong n f C] consists entirely of points, paths, and higher paths in [C].  Therefore, for any [n] we might choose, we can define [Localize f X] as a HIT to universally force [ExtendableAlong n (f i) (fun _ => Localize f X)] to hold for all [i].  For instance, when [n] is 2 (the smallest value which will ensure that [Localize f X] is actually [f]-local), we get

    Inductive Localize f (X : Type) : Type :=
    | loc : X -> Localize X
    | lrec : forall i (g : S i -> X), T i -> X
    | lrec_beta : forall i (g : S i -> X) (s : T i), lrec i g (f i s) = g s
    | lindpaths : forall i (h k : T i -> X) (p : h o f i == k o f i) (t : T i), h t = k t
    | lindpaths_beta : forall i (h k : T i -> X) (p : h o f i == k o f i) (s : S i),
                         lindpaths i h k p (f i s) = p s.

However, just as for [ReflectiveSubuniverse], in order to completely avoid [Funext] we need the [oo]-version of path-splitness.  Written out as above, this would involve infinitely many constructors (but it would not otherwise be problematic, so for instance it can be constructed semantically in model categories).  We can't actually write out infinitely many constructors in Coq, of course, but since we have a finite definition of [ooExtendableAlong], we can just assert directly that [ooExtendableAlong (f i) (fun _ => Localize f X)] holds for all [i].

Then, however, we have to express the hypotheses of the induction principle.  We know what these should be for each path-constructor and higher path-constructor, so all we need is a way to package up those infinitely many hypotheses into a single one, analogously to [ooExtendableAlong].  Thus, we begin this file by defining a "dependent" version of [ooExtendableAlong], and of course we start this with a version for finite [n].  *)

(** ** Dependent extendability *)

Fixpoint ExtendableAlong_Over
         (n : nat) {A B : Type} (f : A -> B) (C : B -> Type)
         (ext : ExtendableAlong n f C) (D : forall b, C b -> Type)
: Type
  := match n return ExtendableAlong n f C -> Type with
       | 0 => fun _ => Unit
       | S n => fun ext' =>
                (forall (g : forall a, C (f a)) (g' : forall a, D (f a) (g a)),
                  {rec : forall b, D b ((fst ext' g).1 b) &
                         forall a, (fst ext' g).2 a # rec (f a) = g' a }) *
                forall (h k : forall b, C b)
                       (h' : forall b, D b (h b)) (k' : forall b, D b (k b)),
                  ExtendableAlong_Over n f (fun b => h b = k b)
                    (snd ext' h k) (fun b c => c # h' b = k' b)
     end ext.

(** Like [ExtendableAlong], these can be postcomposed with known equivalences. *)
Definition extendable_over_postcompose' (n : nat)
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ExtendableAlong n f C)
           (D E : forall b, C b -> Type)
           (g : forall b c, D b c <~> E b c)
: ExtendableAlong_Over n f C ext D
  -> ExtendableAlong_Over n f C ext E.
Proof.
  revert C ext D E g; induction n as [|n IHn]; intros C ext D E g; simpl.
  1:apply idmap.
  intros ext'.
  split.
  - intros h k.
    exists (fun b => g b ((fst ext h).1 b)
                     ((fst ext' h (fun a => (g _ _)^-1 (k a))).1 b)).
    intros a.
    refine ((ap_transport ((fst ext h).2 a) (g (f a)) _)^ @ _).
    apply moveR_equiv_M.
    exact ((fst ext' h (fun a => (g _ _)^-1 (k a))).2 a).
  - intros p q p' q'.
    refine (IHn (fun b => p b = q b) _
                (fun b => fun c => transport (D b) c ((g b (p b))^-1 (p' b))
                                   = ((g b (q b))^-1 (q' b)))
                _ _
                (snd ext' p q (fun b => (g b (p b))^-1 (p' b))
                              (fun b => (g b (q b))^-1 (q' b)))).
    intros b c.
    refine (equiv_compose' _ (equiv_moveR_equiv_M _ _)).
    apply equiv_concat_l.
    refine (_ @ (ap_transport c (g b) _)^).
    apply ap, symmetry, eisretr.
Defined.

Definition extendable_over_postcompose (n : nat)
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ExtendableAlong n f C)
           (D E : forall b, C b -> Type)
           (g : forall b c, D b c -> E b c)
           `{forall b c, IsEquiv (g b c)}
: ExtendableAlong_Over n f C ext D
  -> ExtendableAlong_Over n f C ext E
:= extendable_over_postcompose' n C f ext D E
     (fun b c => BuildEquiv _ _ (g b c) _).

(** And if the dependency is trivial, we obtain them from an ordinary [ExtendableAlong]. *)
Definition extendable_over_const
         (n : nat) {A B : Type} (C : B -> Type) (f : A -> B)
         (ext : ExtendableAlong n f C) (D : B -> Type)
: ExtendableAlong n f D
  -> ExtendableAlong_Over n f C ext (fun b _ => D b).
Proof.
  revert C ext D.
  induction n as [|n IHn]; intros C ext D ext'.
  1:exact tt.
  split.
  - intros g g'.
    exists ((fst ext' g').1).
    exact (fun a => transport_const ((fst ext g).2 a) _
                                    @ (fst ext' g').2 a).
  - intros h k h' k'.
    refine (extendable_over_postcompose' _ _ _ _ _ _ _
              (IHn (fun b => h b = k b) (snd ext h k)
                   (fun b => h' b = k' b) (snd ext' h' k'))).
    exact (fun b c => equiv_concat_l (transport_const c (h' b)) (k' b)).
Defined.

(** This lemma will be used in stating the computation rule for localization. *)
Fixpoint apD_extendable_eq (n : nat) {A B : Type} (C : B -> Type) (f : A -> B)
         (ext : ExtendableAlong n f C) (D : forall b, C b -> Type)
         (g : forall b c, D b c)
         (ext' : ExtendableAlong_Over n f C ext D)
         {struct n}
: Type.
Proof.
  destruct n.
  - exact Unit.
  - apply prod.
    + exact (forall (h : forall a, C (f a)) (b : B),
               g b ((fst ext h).1 b) = (fst ext' h (fun a => g (f a) (h a))).1 b).
    + exact (forall h k, apD_extendable_eq
                           n A B (fun b => h b = k b) f (snd ext h k)
                           (fun b c => c # g b (h b) = g b (k b))
                           (fun b c => apD (g b) c)
                           (snd ext' h k _ _)).
Defined.

(** Here's the [oo]-version. *)
Definition ooExtendableAlong_Over
         {A B : Type} (f : A -> B) (C : B -> Type)
         (ext : ooExtendableAlong f C) (D : forall b, C b -> Type)
  := forall n, ExtendableAlong_Over n f C (ext n) D.

(** The [oo]-version for trivial dependency. *)
Definition ooextendable_over_const
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ooExtendableAlong f C) (D : B -> Type)
: ooExtendableAlong f D
  -> ooExtendableAlong_Over f C ext (fun b _ => D b)
:= fun ext' n => extendable_over_const n C f (ext n) D (ext' n).

(** A crucial fact: the [oo]-version is inherited by types of homotopies. *)
Definition ooextendable_over_homotopy
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ooExtendableAlong f C)
           (D : forall b, C b -> Type)
           (r s : forall b c, D b c)
: ooExtendableAlong_Over f C ext D
  -> ooExtendableAlong_Over f C ext (fun b c => r b c = s b c).
Proof.
  intros ext' n.
  revert C ext D r s ext'.
  induction n as [|n IHn]; intros C ext D r s ext'.
  1:exact tt.
  split.
  - intros g g'.
    refine (_;_); simpl.
    + intros b.
      refine (_ @ (fst (snd (ext' 2) _ _
                            (fun b' => r b' ((fst (ext n.+1) g).1 b'))
                            (fun b' => s b' ((fst (ext n.+1) g).1 b')))
                       (fun _ => 1) _).1 b).
      * refine (transport2 (D b) (p := 1) _ _).
        refine ((fst (snd (snd (ext 3) _ _) (fun b' => 1)
                          ((fst (snd (ext 2) _ _) (fun a : A => 1)).1)
                ) _).1 b); intros a.
        symmetry; refine ((fst (snd (ext 2) _ _) (fun a' => 1)).2 a).
      * intros a; simpl.
        refine (_ @
          ap (transport (D (f a)) ((fst (ext n.+1) g).2 a)^) (g' a)
          @ _);
        [ symmetry; by apply apD
        | by apply apD ].
    + intros a; simpl.
      set (h := (fst (ext n.+1) g).1).
      match goal with
          |- context[   (fst (snd (ext' 2) _ _ ?k1 ?k2) (fun _ => 1) ?l).1 ]
          => pose (p := (fst (snd (ext' 2) _ _  k1  k2) (fun _ => 1) l).2 a);
            simpl in p
      end.
      rewrite transport_paths_Fl in p.
      apply moveL_Mp in p.
      refine (ap (transport _ _) (1 @@ p) @ _); clear p.
      unfold transport2; rewrite concat_p_pp.
      match goal with
          |- transport ?P ?p ((ap ?f ?q @ ap ?f ?r) @ ?s) = ?t
          => refine (ap (transport P p) ((ap_pp f q r)^ @@ (idpath s)) @ _)
      end.
      pose (p := (fst (snd (snd (ext 3) h h) (fun b' : B => 1)
                           ((fst (snd (ext 2) h h) (fun a0 : A => 1)).1))
                      (fun a' : A => ((fst (snd (ext 2) h h)
                                           (fun a' : A => 1)).2 a')^)).2 a);
        simpl in p.
      refine (ap (transport _ _) (ap (ap _) (p @@ 1) @@ 1) @ _); clear p.
      rewrite concat_Vp; simpl; rewrite concat_1p.
      refine (transport_paths_FlFr_D _ _ @ _).
      Open Scope long_path_scope.
      rewrite !ap_pp, !concat_p_pp, ap_transport_pV, !concat_p_pp.
      refine ((((_  @@ 1) @ concat_1p _) @@ 1 @@ 1 @@ 1) @ _).
      * rewrite ap_V, concat_pp_p.
        do 2 apply moveR_Vp.
        rewrite concat_p1.
        symmetry; apply transport_pV_ap.
      * rewrite !concat_pp_p.
        refine ((1 @@ _) @ (concat_p1 _)).
        apply moveR_Vp; rewrite concat_p1.
        apply transport_pV_ap.
      Close Scope long_path_scope.
  - intros h k h' k'.
    refine (extendable_over_postcompose' _ _ _ _ _ _
             (fun b c => equiv_cancelL (apD (r b) c) _ _) _).
    refine (IHn _ _ _ _ _
                (fun n => snd (ext' n.+1) h k
                              (fun b => r b (h b)) (fun b => s b (k b)))).
Qed.

(** ** Local types *)

(**  Our first definition is called [IsLocal_internal] and ideally shouldn't be used much explicitly.  Once we build a reflective subuniverse [Loc f], we will define [IsLocal f] as a notation for [In (Loc f)], so that typeclass inference only has one class to worry about. *)

Section LocalTypesInternal.

  Context {I : Type@{i}} {S T : I -> Type@{i}} (f : forall i, S i -> T i).

  Definition IsLocal_internal (X : Type)
    := forall (i:I), ooExtendableAlong (f i) (fun _ => X).

  Global Instance ishprop_islocal `{Funext} X : IsHProp (IsLocal_internal X).
  Proof.
    exact _.
  Defined.

  Definition islocal_equiv_islocal X {Y} (Xloc : IsLocal_internal X)
             (g : X -> Y) `{IsEquiv _ _ g}
  : IsLocal_internal Y
  := fun i => ooextendable_postcompose _ _ (f i) (fun _ => g) (Xloc i).

End LocalTypesInternal.

(** ** Localization as a HIT *)

Module Export LocalizationHIT.

  Private Inductive Localize
          {I : Type} {S T : I -> Type} (f : forall i, S i -> T i)
          (X : Type) : Type :=
  | loc : X -> Localize f X.

  Arguments loc {I S T f X} x.

  Section Localization.

    Context {I : Type} {S T : I -> Type} (f : forall i, S i -> T i)
            (X : Type).

    (** Note that the following axiom actually contains a point-constructor.  We could separate out that point-constructor and make it an actual argument of the private inductive type, thereby getting a judgmental computation rule for it.  However, since locality is an hprop, there seems little point to this. *)
    Axiom islocal_localize : IsLocal_internal f (Localize f X).

    Section LocalizeInd.

      Context (P : Localize f X -> Type)
      (loc' : forall x, P (loc x))
      (islocal' : forall i, ooExtendableAlong_Over
                              (f i) (fun _ => Localize f X)
                              (islocal_localize i) (fun _ => P)).

      Fixpoint Localize_ind (z : Localize f X) {struct z}
      : P z
        := match z with
             | loc x => fun _ => loc' x
           end islocal'.

      (** We now state the computation rule for [islocal_localize].  Since locality is an hprop, we never actually have any use for it, but the fact that we can state it is a reassuring check that we have defined a meaningful HIT. *)
      Axiom Localize_ind_islocal_localize_beta :
        forall i n, apD_extendable_eq n (fun _ => Localize f X) (f i)
                                      (islocal_localize i n) (fun _ => P)
                                      (fun _ => Localize_ind)
                                      (islocal' i n).

    End LocalizeInd.
  End Localization.
End LocalizationHIT.

(** Now we prove that localization is a reflective subuniverse. *)
Section Localization.

  Context {I : Type} {S T : I -> Type} (f : forall i, S i -> T i).

  (** The induction principle is an equivalence. *)
  Definition ext_localize_ind (X : Type)
      (P : Localize f X -> Type)
      (Ploc : forall i, ooExtendableAlong_Over
                          (f i) (fun _ => Localize f X)
                          (islocal_localize f X i) (fun _ => P))
  : ooExtendableAlong loc P.
  Proof.
    intros n; generalize dependent P.
    induction n as [|n IHn]; intros P Ploc.
    1:exact tt.
    split.
    - intros g.
      exists (Localize_ind f X P g Ploc).
      intros x; reflexivity.
    - intros h k; apply IHn; intros i m.
      apply ooextendable_over_homotopy.
      exact (Ploc i).
  Defined. 

  Definition Loc : ReflectiveSubuniverse.
  Proof.
    refine (Build_ReflectiveSubuniverse
              (Build_UnitSubuniverse
                 (Localize f)
                 (IsLocal_internal f)
                 (islocal_localize f)
                 (@loc _ _ _ f)
                 (@islocal_equiv_islocal _ _ _ f)
                 _) _). simpl.
    intros P Q Qloc.
    apply ext_localize_ind; intros i.
    apply ooextendable_over_const.
    apply Qloc.
  Defined.

  (** It is accessible essentially by definition. *)
  Global Instance accessible_loc : Accessible Loc
    := Build_Accessible Loc I S T f (fun X => (idmap, idmap)).
    
End Localization.

(** Conversely, if a reflective subuniverse is accessible, then it can be "nudged" to an equivalent localization.  The nudged version has the advantages of being universe polymorphic and satisfying its computation rules judgmentally. *)
Definition nudge_reflective_subuniverse
           (O : ReflectiveSubuniverse) `{Accessible O}
: ReflectiveSubuniverse
:= Loc acc_generator.

(** Now we finally define the notation [IsLocal], so that it can refer directly to the reflective subuniverse.  This way there is only one typeclass hanging around, unlike (for instance) the slightly annoying case of [IsTrunc n] versus [In (Tr n)]. *)
Notation IsLocal f := (In (Loc f)).

Section LocalTypes.
  Context {I : Type} {S T : I -> Type} (f : forall i, S i -> T i).

  Definition ooextendable_islocal {X : Type} {Xloc : IsLocal f X} (i:I)
  : ooExtendableAlong (f i) (fun _ => X)
  := Xloc i.

  Global Instance islocal_loc (X : Type) : IsLocal f (Localize f X)
    := islocal_localize f X.

  Global Instance isequiv_precomp_islocal `{Funext}
         {X : Type} `{IsLocal f X} (i : I)
  : IsEquiv (fun (g : T i -> X) => g o f i)
  := isequiv_ooextendable (fun _ => X) (f i) (ooextendable_islocal i).

  (** The non-dependent eliminator *)
  Definition Localize_rec {X Z : Type} `{IsLocal f Z} (g : X -> Z)
  : Localize f X -> Z.
  Proof.
    refine (Localize_ind f X (fun _ => Z) g _); intros i.
    apply ooextendable_over_const.
    apply ooextendable_islocal.
  Defined.

  Definition local_rec {X} `{IsLocal f X} {i} (g : S i -> X)
  : T i -> X
  := (fst (ooextendable_islocal i 1%nat) g).1.

  Definition local_rec_beta {X} `{IsLocal f X} {i} (g : S i -> X) (s : S i)
  : local_rec g (f i s) = g s
    := (fst (ooextendable_islocal i 1%nat) g).2 s.

  Definition local_indpaths {X} `{IsLocal f X} {i} {h k : T i -> X}
             (p : h o f i == k o f i)
  : h == k
    := (fst (snd (ooextendable_islocal i 2) h k) p).1.

  Definition local_indpaths_beta {X} `{IsLocal f X} {i} (h k : T i -> X)
             (p : h o f i == k o f i) (s : S i)
  : local_indpaths p (f i s) = p s
    := (fst (snd (ooextendable_islocal i 2) h k) p).2 s.

End LocalTypes.

Arguments local_rec : simpl never.
Arguments local_rec_beta : simpl never.
Arguments local_indpaths : simpl never.
Arguments local_indpaths_beta : simpl never.

(** ** Nullification *)

(** Nullification is the special case of localization where each [T i] is [Unit].  In this case, we get a modality and not just a reflective subuniverse. *)

(** The hypotheses of this lemma may look slightly odd (why are we bothering to talk about type families dependent over [Unit]?), but they seem to be the most convenient to make the induction go through.  *)
Definition extendable_over_unit (n : nat)
  (A : Type) (C : Unit -> Type) (D : forall u, C u -> Type)
  (ext : ExtendableAlong n (@const A Unit tt) C)
  (ext' : forall (c : forall u, C u),
            ExtendableAlong n (@const A Unit tt) (fun u => (D u (c u))))
: ExtendableAlong_Over n (@const A Unit tt) C ext D.
Proof.
  generalize dependent C; induction n as [|n IHn];
    intros C D ext ext'; [exact tt | split].
  - intros g g'.
    exists ((fst (ext' (fst ext g).1)
                 (fun a => ((fst ext g).2 a)^ # (g' a))).1);
      intros a; simpl.
    apply moveR_transport_p.
    exact ((fst (ext' (fst ext g).1)
                (fun a => ((fst ext g).2 a)^ # (g' a))).2 a).
  - intros h k h' k'.
    apply IHn; intros g.
    exact (snd (ext' k) (fun u => g u # h' u) k').
Defined.

Definition ooextendable_over_unit
  (A : Type) (C : Unit -> Type) (D : forall u, C u -> Type)
  (ext : ooExtendableAlong (@const A Unit tt) C)
  (ext' : forall (c : forall u, C u),
            ooExtendableAlong (@const A Unit tt) (fun u => (D u (c u))))
: ooExtendableAlong_Over (@const A Unit tt) C ext D
  := fun n => extendable_over_unit n A C D (ext n) (fun c => ext' c n).

Section Nullification.

  Context {I : Type@{i}} (S : I -> Type@{i}).
  Let f := (fun (i:I) (s:S i) => tt).

  Definition Nul : Modality.
  Proof.
    refine (Build_Modality (Loc f) _ _ _).
    - intros A B ? g x.
      apply Localize_ind.
      + exact g.
      + intros i.
        apply ooextendable_over_unit; intros c.
        refine (ooextendable_postcompose (fun (_:Unit) => B (c tt)) _ _
                  (fun u => transport B (ap c (path_unit tt u))) _).
        refine (ooextendable_islocal f i).
    - reflexivity.
  Defined.

End Nullification.

(** We can also nudge accessible modalities into nullifications. *)
Definition nudge_modality (O : Modality) `{Accessible O}
: Modality
:= Nul acc_conn_types.
