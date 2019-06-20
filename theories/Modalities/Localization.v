(* -*- mode: coq; mode: visual-line -*-  *)
(** * Localization *)

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions EquivalenceVarieties.
Require Import ReflectiveSubuniverse Accessible.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** Suppose given a family of maps [f : forall (i:I), S i -> T i].  A type [X] is said to be [f]-local if for all [i:I], the map [(T i -> X) -> (S i -> X)] given by precomposition with [f i] is an equivalence.  Our goal is to show that the [f]-local types form a reflective subuniverse, with a reflector constructed by localization.  That is, morally we want to say

<<
Inductive Localize f (X : Type) : Type :=
| loc : X -> Localize X
| islocal_localize : forall i, IsEquiv (fun (g : T i -> X) => g o f i).
>>

This is not a valid HIT by the usual rules, but if we expand out the definition of [IsEquiv] and apply [path_sigma] and [path_forall], then it becomes one.  We get a simpler definition (no 2-path constructors) if we do this with [BiInv] rather than [IsEquiv]:

<<
Inductive Localize f (X : Type) : Type :=
| loc : X -> Localize X
| lsect : forall i (g : S i -> X), T i -> X
| lissect : forall i (g : S i -> X) (s : S i), lsect i g (f i s) = g s
| lretr : forall i (g : S i -> X), T i -> X
| lisretr : forall i (h : T i -> X) (t : T i), lretr i (h o f i) t = h t.
>>

This definition works, and from it one can prove that the [f]-local types form a reflective subuniverse.  However, the proof inextricably involves [Funext].  We can avoid [Funext] in the same way that we did in the definition of a [ReflectiveSubuniverse], by using pointwise path-split precomposition equivalences.  Observe that the assertion [ExtendableAlong n f C] consists entirely of points, paths, and higher paths in [C].  Therefore, for any [n] we might choose, we can define [Localize f X] as a HIT to universally force [ExtendableAlong n (f i) (fun _ => Localize f X)] to hold for all [i].  For instance, when [n] is 2 (the smallest value which will ensure that [Localize f X] is actually [f]-local), we get

<<
Inductive Localize f (X : Type) : Type :=
| loc : X -> Localize X
| lrec : forall i (g : S i -> X), T i -> X
| lrec_beta : forall i (g : S i -> X) (s : T i), lrec i g (f i s) = g s
| lindpaths : forall i (h k : T i -> X) (p : h o f i == k o f i) (t : T i), h t = k t
| lindpaths_beta : forall i (h k : T i -> X) (p : h o f i == k o f i) (s : S i),
                     lindpaths i h k p (f i s) = p s.
>>

However, just as for [ReflectiveSubuniverse], in order to completely avoid [Funext] we need the [oo]-version of path-splitness.  Written out as above, this would involve infinitely many constructors (but it would not otherwise be problematic, so for instance it can be constructed semantically in model categories).  We can't actually write out infinitely many constructors in Coq, of course, but since we have a finite definition of [ooExtendableAlong], we can just assert directly that [ooExtendableAlong (f i) (fun _ => Localize f X)] holds for all [i].

Then, however, we have to express the hypotheses of the induction principle.  We know what these should be for each path-constructor and higher path-constructor, so all we need is a way to package up those infinitely many hypotheses into a single one, analogously to [ooExtendableAlong].  Thus, we begin this file by defining a "dependent" version of [ooExtendableAlong], and of course we start this with a version for finite [n].  *)

(** ** Dependent extendability *)

Fixpoint ExtendableAlong_Over@{a b c d m}
         (n : nat) {A : Type@{a}} {B : Type@{b}} (f : A -> B)
         (C : B -> Type@{c})
         (D : forall b, C b -> Type@{d})
         (ext : ExtendableAlong@{a b c m} n f C)
: Type@{m}
  := match n return ExtendableAlong@{a b c m} n f C -> Type@{m} with
       | 0 => fun _ => Unit
       | S n => fun ext' =>
                (forall (g : forall a, C (f a)) (g' : forall a, D (f a) (g a)),
                  sig@{m m}     (** Control universe parameters *)
                  (fun (rec : forall b, D b ((fst ext' g).1 b)) =>
                         forall a, (fst ext' g).2 a # rec (f a) = g' a )) *
                forall (h k : forall b, C b)
                       (h' : forall b, D b (h b)) (k' : forall b, D b (k b)),
                  ExtendableAlong_Over n f (fun b => h b = k b)
                    (fun b c => c # h' b = k' b) (snd ext' h k)
     end ext.
Check ExtendableAlong_Over@{a b c d m}.
(** [ExtendableAlong_Over] takes 5 universe parameters:
    - size of A
    - size of B
    - size of C
    - size of D
    - size of result (>= A,B,C,D) *)

(** Like [ExtendableAlong], these can be postcomposed with known equivalences. *)
Definition extendable_over_postcompose' (n : nat)
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ExtendableAlong n f C)
           (D E : forall b, C b -> Type)
           (g : forall b c, D b c <~> E b c)
: ExtendableAlong_Over n f C D ext
  -> ExtendableAlong_Over n f C E ext.
Proof.
  revert C ext D E g; simple_induction n n IHn; intros C ext D E g; simpl.
  1:by apply idmap.
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
    refine (_ oE equiv_moveR_equiv_M _ _).
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
: ExtendableAlong_Over n f C D ext
  -> ExtendableAlong_Over n f C E ext
:= extendable_over_postcompose' n C f ext D E
     (fun b c => BuildEquiv _ _ (g b c) _).

(** And if the dependency is trivial, we obtain them from an ordinary [ExtendableAlong]. *)
Definition extendable_over_const
           (n : nat) {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ExtendableAlong n f C) (D : B -> Type)
: ExtendableAlong n f D
  -> ExtendableAlong_Over n f C (fun b _ => D b) ext.
Proof.
  revert C ext D.
  simple_induction n n IHn; intros C ext D ext'.
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
         (ext' : ExtendableAlong_Over n f C D ext)
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
         (D : forall b, C b -> Type) (ext : ooExtendableAlong f C)
  := forall n, ExtendableAlong_Over n f C D (ext n).
(** Universe parameters are the same as for [ExtendableAlong_Over]. *)
Check ooExtendableAlong_Over@{a b c d r}.

(** The [oo]-version for trivial dependency. *)
Definition ooextendable_over_const
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ooExtendableAlong f C) (D : B -> Type)
: ooExtendableAlong f D
  -> ooExtendableAlong_Over f C (fun b _ => D b) ext
:= fun ext' n => extendable_over_const n C f (ext n) D (ext' n).

(** A crucial fact: the [oo]-version is inherited by types of homotopies. *)
Definition ooextendable_over_homotopy
           {A B : Type} (C : B -> Type) (f : A -> B)
           (ext : ooExtendableAlong f C)
           (D : forall b, C b -> Type)
           (r s : forall b c, D b c)
: ooExtendableAlong_Over f C D ext
  -> ooExtendableAlong_Over f C (fun b c => r b c = s b c) ext.
Proof.
  intros ext' n.
  revert C ext D r s ext'.
  simple_induction n n IHn; intros C ext D r s ext'.
  1:exact tt.
  split.
  - intros g g'.
    simple refine (_;_); simpl.
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
      Local Opaque transport_pV. (* work around bug 4533 *)
      rewrite !ap_pp, !concat_p_pp, ap_transport_pV, !concat_p_pp.
      Local Transparent transport_pV. (* work around bug 4533 *)
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

Import IsLocal_Internal.

Definition islocal_equiv_islocal (f : LocalGenerators@{a})
           (X : Type@{i}) {Y : Type@{j}}
           (Xloc : IsLocal@{i i' a} f X)
           (g : X -> Y) `{IsEquiv@{i j} _ _ g}
: IsLocal@{j j' a} f Y.
Proof.
  intros i.
  (** We have to fiddle with the max universes to get this to work, since [ooextendable_postcompose] requires the max universe in both cases to be the same, whereas we don't want to assume that the hypothesis and conclusion are related in any way. *)
  apply lift_ooextendablealong@{a a j k j'}.
  refine (ooextendable_postcompose@{a a i j k k k k k k}
            _ _ (f i) (fun _ => g) _).
  apply lift_ooextendablealong@{a a i i' k}.
  apply Xloc.
Defined.

(** ** Localization as a HIT *)

Module Export LocalizationHIT.

  Private Inductive Localize (f : LocalGenerators@{a}) (X : Type@{i})
  : Type@{max(a,i)} :=
  | loc : X -> Localize f X.

  Arguments loc {f X} x.

  (** Note that the following axiom actually contains a point-constructor.  We could separate out that point-constructor and make it an actual argument of the private inductive type, thereby getting a judgmental computation rule for it.  However, since locality is an hprop, there seems little point to this. *)
  Axiom islocal_localize
  : forall (f : LocalGenerators@{a}) (X : Type@{i}),
      IsLocal@{i k a} f (Localize f X).

  Fixpoint Localize_ind
           (f : LocalGenerators@{a}) (X : Type@{i})
           (P : Localize f X -> Type@{j})
           (loc' : forall x, P (loc x))
           (islocal' : forall i, ooExtendableAlong_Over@{a a i j k}
                                   (f i) (fun _ => Localize@{a i} f X)
                                   (fun _ => P)
                                   (islocal_localize@{a i k} f X i))
           (z : Localize f X) {struct z}
  : P z
    := match z with
         | loc x => fun _ => loc' x
       end islocal'.

  (** We now state the computation rule for [islocal_localize].  Since locality is an hprop, we never actually have any use for it, but the fact that we can state it is a reassuring check that we have defined a meaningful HIT. *)
  Axiom Localize_ind_islocal_localize_beta :
    forall (f : LocalGenerators) (X : Type)
           (P : Localize f X -> Type)
           (loc' : forall x, P (loc x))
           (islocal' : forall i, ooExtendableAlong_Over
                                   (f i) (fun _ => Localize f X)
                                   (fun _ => P)
                                   (islocal_localize f X i))
           i n,
      apD_extendable_eq n (fun _ => Localize f X) (f i)
                        (islocal_localize f X i n) (fun _ => P)
                        (fun _ => Localize_ind f X P loc' islocal')
                        (islocal' i n).

End LocalizationHIT.

(** Now we prove that localization is a reflective subuniverse. *)

Section Localization.

  Context (f : LocalGenerators).

  (** The induction principle is an equivalence. *)
  Definition ext_localize_ind (X : Type)
      (P : Localize f X -> Type)
      (Ploc : forall i, ooExtendableAlong_Over
                          (f i) (fun _ => Localize f X)
                          (fun _ => P) (islocal_localize f X i))
  : ooExtendableAlong loc P.
  Proof.
    intros n; generalize dependent P.
    simple_induction n n IHn; intros P Ploc.
    1:exact tt.
    split.
    - intros g.
      exists (Localize_ind f X P g Ploc).
      intros x; reflexivity.
    - intros h k; apply IHn; intros i m.
      apply ooextendable_over_homotopy.
      exact (Ploc i).
  Defined.

End Localization.

(** We define a wrapper around [LocalGenerators].  See the comments in HIT/Truncations for an explanation.  Unlike there, here we make the wrapper a [Record] rather than a [Definition], so that a projection has to be inserted to convert one to the other.  This forces us to write [Loc f] as a parameter to all reflective-subuniverse functions, which is really entirely reasonable; we only allowed ourselves to write [n] rather than [Tr n] in the case of truncations because things like connectedness are traditionally defined only for the truncation modality, so users may prefer not to have to think about the fact that there is a modality present. *)
Record Localization_ReflectiveSubuniverse := Loc { unLoc : LocalGenerators }.

Module Localization_ReflectiveSubuniverses <: ReflectiveSubuniverses.

  (** Here we have to use the extra universe parameter that we built into the definition of [ReflectiveSubuniverse]: a set of localization generators is parametrized by the universe that it lives in, but also by the universe that the *generators* live in, which must be smaller. *)
  Definition ReflectiveSubuniverse : Type@{u} := Localization_ReflectiveSubuniverse@{a}.
  Check ReflectiveSubuniverse@{u a}.

  Definition O_reflector : ReflectiveSubuniverse@{u a} -> Type@{i} -> Type@{i}
    := fun O => Localize@{a i} (unLoc O).

  Definition In : ReflectiveSubuniverse@{u a} -> Type@{i} -> Type@{i}
    := fun O X => IsLocal@{i i a} (unLoc O) X.

  Definition O_inO :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
      In O (O_reflector O T)
    := fun O => islocal_localize@{a i i} (unLoc O).

  Definition to :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}), T -> O_reflector O T
    := fun O => @loc@{a i} (unLoc O).

  Definition inO_equiv_inO :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j}),
      In@{u a i} O T -> forall f : T -> U, IsEquiv f ->
      In@{u a j} O U
    := fun O => islocal_equiv_islocal@{a i j i j k} (unLoc O).

  Definition hprop_inO@{u a i} `{Funext}
             (O : ReflectiveSubuniverse@{u a}) (T : Type@{i})
  : IsHProp (In@{u a i} O T).
  Proof.
    apply (@trunc_forall@{a i i} _); intros i.
    apply ishprop_ooextendable@{a a i i i  i i i i i  i i i}.
  Defined.

  Definition extendable_to_O
             (O : ReflectiveSubuniverse@{u a}) {P : Type@{i}}
             {Q : Type@{j}} {Q_inO : In@{u a j} O Q}
  : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
  Proof.
    apply ext_localize_ind@{a i j i k}; intros ?.
    apply ooextendable_over_const.
    apply Q_inO.
  Defined.

End Localization_ReflectiveSubuniverses.


(** If you import the following module [LocM], then you can call all the reflective subuniverse functions with a [LocalGenerators] as the parameter. *)
Module Import LocM := ReflectiveSubuniverses_Theory Localization_ReflectiveSubuniverses.
(** If you don't import it, then you'll need to write [LocM.function_name]. *)
Export LocM.Coercions.

Coercion Localization_ReflectiveSubuniverse_to_ReflectiveSubuniverse := idmap
  : Localization_ReflectiveSubuniverse -> ReflectiveSubuniverse.

(** Here is the "real" definition of the notation [IsLocal].  Defining it this way allows it to inherit typeclass inference from [In], unlike (for instance) the slightly annoying case of [IsTrunc n] versus [In (Tr n)]. *)
Notation IsLocal f := (In (Loc f)).

Section LocalTypes.
  Context (f : LocalGenerators).

  (** A remark on universes: recall that [ooExtendableAlong] takes four universe parameters, three for the sizes of the types involved and one for the max of all of them.  In the definition of [IsLocal f X] we set that max universe to be the same as the size of [X], so that [In (Loc f) X] would lie in the same universes as [X], which is necessary for our definition of a reflective subuniverse.  However, in practice we may need this extendability property with the max universe being larger, to avoid coalescing universes undesiredly.  Thus, in making it available by the following name, we also insert a [lift] to generalize the max universe. *)
  Definition ooextendable_islocal {X : Type@{i}} {Xloc : IsLocal f X} i
  : ooExtendableAlong@{a a i k} (f i) (fun _ => X)
    := (lift_ooextendablealong _ _ (Xloc i)).

  Global Instance islocal_loc (X : Type) : IsLocal f (Localize f X)
    := islocal_localize f X.

  Global Instance isequiv_precomp_islocal `{Funext}
         {X : Type} `{IsLocal f X} i
  : IsEquiv (fun g => g o f i)
  := isequiv_ooextendable (fun _ => X) (f i) (ooextendable_islocal i).

  (** The non-dependent eliminator *)
  Definition Localize_rec {X Z : Type} `{IsLocal f Z} (g : X -> Z)
  : Localize f X -> Z.
  Proof.
    refine (Localize_ind f X (fun _ => Z) g _); intros i.
    apply ooextendable_over_const.
    apply ooextendable_islocal.
  Defined.

  Definition local_rec {X} `{IsLocal f X} {i} (g : lgen_domain f i -> X)
  : lgen_codomain f i -> X
  := (fst (ooextendable_islocal i 1%nat) g).1.

  Definition local_rec_beta {X} `{IsLocal f X} {i} (g : lgen_domain f i -> X) s
  : local_rec g (f i s) = g s
    := (fst (ooextendable_islocal i 1%nat) g).2 s.

  Definition local_indpaths {X} `{IsLocal f X} {i} {h k : lgen_codomain f i -> X}
             (p : h o f i == k o f i)
  : h == k
    := (fst (snd (ooextendable_islocal i 2) h k) p).1.

  Definition local_indpaths_beta {X} `{IsLocal f X} {i} (h k : lgen_codomain f i -> X)
             (p : h o f i == k o f i) s
  : local_indpaths p (f i s) = p s
    := (fst (snd (ooextendable_islocal i 2) h k) p).2 s.

End LocalTypes.

Arguments local_rec : simpl never.
Arguments local_rec_beta : simpl never.
Arguments local_indpaths : simpl never.
Arguments local_indpaths_beta : simpl never.

(** ** Localization and accessibility *)

(** Localization subuniverses are accessible, essentially by definition. *)
Module Accessible_Localization
  <: Accessible_ReflectiveSubuniverses Localization_ReflectiveSubuniverses.

  Import Localization_ReflectiveSubuniverses.

  Definition acc_gen : ReflectiveSubuniverse -> LocalGenerators
    := unLoc.

  Definition inO_iff_islocal
             (O : ReflectiveSubuniverse@{u a}) (X : Type@{i})
  : iff@{i i i} (In O X) (IsLocal (acc_gen O) X)
    := (idmap , idmap).

End Accessible_Localization.

(** Conversely, if a reflective subuniverse is accessible, then it can be "nudged" to an equivalent localization.  The nudged version has the advantages of satisfying its computation rules judgmentally. *)

Module Nudge_ReflectiveSubuniverses
       (Os : ReflectiveSubuniverses)
       (Acc : Accessible_ReflectiveSubuniverses Os).

  (** Once again, we are annoyed that "application of modules is restricted to paths". *)
  Module Data <: ReflectiveSubuniverses_Restriction_Data
                   Localization_ReflectiveSubuniverses.
    Definition New_ReflectiveSubuniverse := Os.ReflectiveSubuniverse.
    Definition ReflectiveSubuniverses_restriction
    : New_ReflectiveSubuniverse -> Localization_ReflectiveSubuniverses.ReflectiveSubuniverse
      := fun O => Loc (Acc.acc_gen O).
  End Data.

  Module Nudged <: ReflectiveSubuniverses
    := ReflectiveSubuniverses_Restriction Localization_ReflectiveSubuniverses Data.

End Nudge_ReflectiveSubuniverses.
