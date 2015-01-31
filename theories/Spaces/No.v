(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext TruncType HSet.
Require Import hit.Truncations.
Import TrM.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * The surreal numbers *)

(** Based on section 11.6 of the HoTT Book. *)

Delimit Scope surreal_scope with No.
Local Open Scope surreal_scope.

(** The surreal numbers use a lot of universes.  We include some universe annotations here and there to reduce the number of overall universe parameters from an unmanageable 100K to a slightly less unmanageable 50-60K.  This improves performance significantly. *)

(** ** Definition *)

Module Export Surreals.

  (** *** Games first *)

  (** Since Coq doesn't support inductive-inductive types natively, we have to hack a bit.  Inspired by Conway, we define [Game]s to be constructed by the point-constructor of [No] but without the hypothesis on inequality of options.  Then we define the inequalities as a mutual inductive family over [Game], and put an inductive predicate on [Game] characterizing those that are Numbers.  We then proceed to add axioms for the path-constructors of [No].

  It should be emphasized that this is *not* currently a correct higher inductive-inductive definition of games; these "games" are only being used inside this module as a trick to produce [No] in a way that computes on the point-constructor.  It should be possible to make a higher inductive-inductive definition of games, but this is not it. *)

  Private Inductive Game : Type :=
  | opt : forall (L R : Type@{i}) (xL : L -> Game) (xR : R -> Game), Game.

  Arguments opt {L R} xL xR.

  Private Inductive game_le : Game@{i} -> Game@{i} -> Type :=
  | game_le_lr
    : forall (L R : Type@{i}) (xL : L -> Game@{i}) (xR : R -> Game@{i})
             (L' R' : Type@{i}) (yL : L' -> Game@{i}) (yR : R' -> Game@{i}),
        (forall (l:L), game_lt (xL l) (opt yL yR)) ->
        (forall (r:R'), game_lt (opt xL xR) (yR r)) ->
        game_le (opt xL xR) (opt yL yR)

  with game_lt : Game@{i} -> Game@{i} -> Type :=
  | game_lt_l
    : forall (L R : Type@{i}) (xL : L -> Game@{i}) (xR : R -> Game@{i})
             (L' R' : Type@{i}) (yL : L' -> Game@{i}) (yR : R' -> Game@{i})
             (l : L'),
        (game_le (opt xL xR) (yL l)) ->
        game_lt (opt xL xR) (opt yL yR)
  | game_lt_r
    : forall (L R : Type@{i}) (xL : L -> Game@{i}) (xR : R -> Game@{i})
             (L' R' : Type@{i}) (yL : L' -> Game@{i}) (yR : R' -> Game@{i})
             (r : R),
        (game_le (xR r) (opt yL yR)) ->
        game_lt (opt xL xR) (opt yL yR).

  Arguments game_le_lr {L R} xL xR {L' R'} yL yR _ _.
  Arguments game_lt_l {L R} xL xR {L' R'} yL yR l _.
  Arguments game_lt_r {L R} xL xR {L' R'} yL yR r _.
  
  (** *** Now the surreals *)

  Private Inductive is_surreal : Game@{i} -> Type :=
  | isno : forall (L R : Type@{i}) (xL : L -> Game@{i}) (xR : R -> Game@{i}),
             (forall l, is_surreal (xL l))
             -> (forall r, is_surreal (xR r))
             -> (forall (l:L) (r:R), game_lt (xL l) (xR r))
             -> is_surreal (opt xL xR).

  Unset Nonrecursive Elimination Schemes.
  Record No : Type :=
    { game_of : Game
    ; isno_game_of : is_surreal (game_of) }.

  Definition lt (x y : No) := game_lt (game_of x) (game_of y).

  Definition le (x y : No) := game_le (game_of x) (game_of y).

  Infix "<" := lt : surreal_scope.
  Infix "<=" := le : surreal_scope.

  Definition No_cut {L R : Type@{i}} (xL : L -> No@{i}) (xR : R -> No@{i})
             (xcut : forall (l:L) (r:R), (xL l) < (xR r))
  : No
    := Build_No (opt (game_of o xL) (game_of o xR))
                (isno _ _ _ _ (isno_game_of o xL)
                      (isno_game_of o xR) xcut).

  Notation "{{ xL | xR // xcut }}" := (No_cut xL xR xcut).

  Axiom path_No : forall (x y : No), (x <= y) -> (y <= x) -> (x = y).
  Arguments path_No {x y} _ _.

  Definition le_lr
             {L R : Type@{i} } (xL : L -> No) (xR : R -> No)
             (xcut : forall (l:L) (r:R), (xL l) < (xR r))
             {L' R' : Type@{i} } (yL : L' -> No) (yR : R' -> No)
             (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
  : (forall (l:L), xL l < {{ yL | yR // ycut }}) ->
    (forall (r:R'), {{ xL | xR // xcut }} < yR r) ->
    {{ xL | xR // xcut }} <= {{ yL | yR // ycut }}
    := game_le_lr (game_of o xL) (game_of o xR)
                  (game_of o yL) (game_of o yR).

  Definition lt_l
             {L R : Type@{i} } (xL : L -> No) (xR : R -> No)
             (xcut : forall (l:L) (r:R), (xL l) < (xR r))
             {L' R' : Type@{i} } (yL : L' -> No) (yR : R' -> No)
             (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
             (l : L')
  : ({{ xL | xR // xcut }} <= yL l) ->
    {{ xL | xR // xcut }} < {{ yL | yR // ycut }}
    := game_lt_l (game_of o xL) (game_of o xR)
                 (game_of o yL) (game_of o yR) l.

  Definition lt_r
             {L R : Type@{i} } (xL : L -> No) (xR : R -> No)
             (xcut : forall (l:L) (r:R), (xL l) < (xR r))
             {L' R' : Type@{i} } (yL : L' -> No) (yR : R' -> No)
             (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
             (r : R)
  : (xR r <= {{ yL | yR // ycut }}) ->
    {{ xL | xR // xcut }} < {{ yL | yR // ycut }}
    := game_lt_r (game_of o xL) (game_of o xR)
                 (game_of o yL) (game_of o yR) r.

  Global Instance ishprop_No_le {x y : No}
  : IsHProp (x <= y).
  Admitted.

  Global Instance ishprop_No_lt {x y : No}
  : IsHProp (x < y).
  Admitted.

  (** *** Now the induction principle. *)

  Section NoInd.

    Context
      (A : No@{i} -> Type)
      (dle : forall (x y:No@{i}), (x <= y) -> A x -> A y -> Type)
      (dlt : forall (x y:No@{i}), (x < y) -> A x -> A y -> Type)
      {ishprop_le : forall x y a b p, IsHProp (dle x y p a b)}
      {ishprop_lt : forall x y a b p, IsHProp (dlt x y p a b)}
      (dcut : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                     (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                     (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                     (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r)),
                A {{ xL | xR // xcut }})
      (dpath : forall (x y:No) (a:A x) (b:A y) (p : x <= y) (q : y <= x)
                      (dp : dle x y p a b) (dq : dle y x q b a),
                 path_No p q # a = b)
      (dle_lr : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                       (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                       (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                       (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                       (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                       (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                       (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                       (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                       (p : forall (l:L), xL l < {{ yL | yR // ycut }})
                       (dp : forall (l:L),
                               dlt _ _ (p l)
                                   (fxL l)
                                   (dcut _ _ yL yR ycut fyL fyR fycut))
                       (q : forall (r:R'), {{ xL | xR // xcut }} < yR r)
                       (dq : forall (r:R'),
                               dlt _ _ (q r)
                                   (dcut _ _ xL xR xcut fxL fxR fxcut)
                                   (fyR r)),
                  dle {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                      (le_lr xL xR xcut yL yR ycut p q)
                      (dcut _ _ xL xR xcut fxL fxR fxcut)
                      (dcut _ _ yL yR ycut fyL fyR fycut))
      (dlt_l : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                      (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                      (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                      (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                      (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                      (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                      (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                      (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                      (l : L')
                      (p : {{ xL | xR // xcut }} <= yL l)
                      (dp : dle _ _ p
                                (dcut _ _ xL xR xcut fxL fxR fxcut)
                                (fyL l)),
                 dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                     (lt_l xL xR xcut yL yR ycut l p)
                     (dcut _ _ xL xR xcut fxL fxR fxcut)
                     (dcut _ _ yL yR ycut fyL fyR fycut))
      (dlt_r : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                      (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                      (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                      (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                      (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                      (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                      (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                      (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                      (r : R)
                      (p : (xR r) <= {{ yL | yR // ycut }})
                      (dp : dle _ _ p
                                (fxR r)
                                (dcut _ _ yL yR ycut fyL fyR fycut)),
                 dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                     (lt_r xL xR xcut yL yR ycut r p)
                     (dcut _ _ xL xR xcut fxL fxR fxcut)
                     (dcut _ _ yL yR ycut fyL fyR fycut)).

    (** Technically, we induct over the inductive predicate witnessing Numberhood of games. *)
    Local Fixpoint No_ind_internal (x : Game) (xno : is_surreal x)
          {struct xno}
    : A (Build_No x xno).
    Proof.
      revert ishprop_le ishprop_lt dpath dle_lr dlt_l dlt_r.
      destruct xno as [L R xL xR Lno Rno xcut].
      intros ishprop_le ishprop_lt dpath dle_lr dlt_l dlt_r.
      refine (dcut L R (fun l => Build_No (xL l) (Lno l))
                   (fun r => Build_No (xR r) (Rno r)) xcut _ _ _).
      - intros l; exact (No_ind_internal (xL l) (Lno l)).
      - intros r; exact (No_ind_internal (xR r) (Rno r)).
      (** I'm not entirely sure about the status of this last goal, but fortunately we don't really need to specify it, since generally when computing the value of [No_ind] we only care about the options of its output, not the proofs that they satisfy the inequality condition. *)
      - admit.
    Defined.

    Definition No_ind (x : No) : A x.
    Proof.
      destruct x as [x xno].
      exact (No_ind_internal x xno).
    Defined.

    Axiom No_ind_le : forall (x y : No) (p : x <= y),
                        dle x y p (No_ind x) (No_ind y).

    Axiom No_ind_lt : forall (x y : No) (p : x < y),
                        dlt x y p (No_ind x) (No_ind y).

    (** Sometimes it's convenient to have all three parts of [No_ind] in one package, so that we only have to verify the hypotheses once. *)
    Definition No_ind_package
    : { f : forall x, A x &
      (forall (x y : No) (p : x <= y), dle x y p (f x) (f y)) *
      (forall (x y : No) (p : x < y), dlt x y p (f x) (f y)) }
      := ( No_ind ; (No_ind_le , No_ind_lt) ).

    (** It's also sometimes convenient to have just the inequality parts together. *)
    Definition No_ind_le_lt (x y : No)
    : (forall (p : x <= y), dle x y p (No_ind x) (No_ind y)) *
      (forall (p : x < y), dlt x y p (No_ind x) (No_ind y))
      := (No_ind_le x y , No_ind_lt x y).

  End NoInd.

End Surreals.

(** ** A few surreal numbers *)

Definition zero : No
  := {{ Empty_rec | Empty_rec //
        Empty_ind (fun x => forall y, Empty_rec x < Empty_rec y ) }}.

Definition one : No
  := {{ (fun _:Unit => zero) | Empty_rec // fun x => Empty_ind _ }}.

Definition minusone : No
  := {{ Empty_rec | (fun _:Unit => zero) // Empty_ind _ }}.

(** ** More induction principles *)

(** *** The simplified induction principle for hprops *)

Definition No_ind_hprop (P : No -> Type) `{forall x, IsHProp (P x)}
           (dcut : forall (L R : Type) (xL : L -> No) (xR : R -> No)
                          (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                          (IHL : forall l, P (xL l))
                          (IHR : forall r, P (xR r)),
                     P {{ xL | xR // xcut }})
           (x : No)
: P x.
Proof.
  revert x;
  refine (No_ind P (fun _ _ _ _ _ => Unit) (fun _ _ _ _ _ => Unit)
                 _ _ _ _ _);
  intros; try apply path_ishprop; try exact tt.
  apply dcut; assumption.
Defined.

(** *** The non-dependent recursion principle *)

Section NoRec.

  Context  (A : Type)
           (dle : A -> A -> Type) `{is_mere_relation A dle}
           (dlt : A -> A -> Type) `{is_mere_relation A dlt}
           (dcut : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                          (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                          (fxL : L -> A) (fxR : R -> A)
                          (fxcut : forall l r, dlt (fxL l) (fxR r)),
                     A)
           (dpath : forall a b, dle a b -> dle b a -> a = b)
           (dle_lr : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                            (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                            (fxL : L -> A) (fxR : R -> A)
                            (fxcut : forall l r, dlt (fxL l) (fxR r))
                            (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                            (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                            (fyL : L' -> A) (fyR : R' -> A)
                            (fycut : forall l r, dlt (fyL l) (fyR r))
                            (p : forall (l:L), xL l < {{ yL | yR // ycut }})
                            (dp : forall (l:L),
                                    dlt (fxL l) (dcut _ _ yL yR ycut fyL fyR fycut))
                            (q : forall (r:R'), {{ xL | xR // xcut }} < yR r)
                            (dq : forall (r:R'),
                                    dlt (dcut _ _ xL xR xcut fxL fxR fxcut) (fyR r)),
                       dle (dcut _ _ xL xR xcut fxL fxR fxcut)
                           (dcut _ _ yL yR ycut fyL fyR fycut))
           (dlt_l : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                           (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                           (fxL : L -> A) (fxR : R -> A)
                           (fxcut : forall l r, dlt (fxL l) (fxR r))
                           (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                           (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                           (fyL : L' -> A) (fyR : R' -> A)
                           (fycut : forall l r, dlt (fyL l) (fyR r))
                           (l : L') (p : {{ xL | xR // xcut }} <= yL l)
                           (dp : dle (dcut _ _ xL xR xcut fxL fxR fxcut) (fyL l)),
                      dlt (dcut _ _ xL xR xcut fxL fxR fxcut)
                          (dcut _ _ yL yR ycut fyL fyR fycut))
           (dlt_r : forall (L R : Type@{i}) (xL : L -> No) (xR : R -> No)
                           (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                           (fxL : L -> A) (fxR : R -> A)
                           (fxcut : forall l r, dlt (fxL l) (fxR r))
                           (L' R' : Type@{i}) (yL : L' -> No) (yR : R' -> No)
                           (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                           (fyL : L' -> A) (fyR : R' -> A)
                           (fycut : forall l r, dlt (fyL l) (fyR r))
                           (r : R) (p : (xR r) <= {{ yL | yR // ycut }})
                           (dp : dle (fxR r) (dcut _ _ yL yR ycut fyL fyR fycut)),
                      dlt (dcut _ _ xL xR xcut fxL fxR fxcut)
                          (dcut _ _ yL yR ycut fyL fyR fycut)).

  Definition No_rec (x : No) : A.
  Proof.
    revert x;
    refine (No_ind (fun _ => A) (fun _ _ _ a b => dle a b)
                   (fun _ _ _ a b => dlt a b)
                   _ _ _ _ _);
    intros.
    - exact (dcut L R xL xR xcut fxL fxR fxcut).
    - refine (transport_const _ _ @ _).
      apply dpath; assumption.
    - cbn. apply dle_lr; assumption.
    - cbn. apply dlt_l with l; assumption.
    - cbn. apply dlt_r with r; assumption.
  Defined.

  Definition No_rec_le (x y : No) (p : x <= y)
  : dle (No_rec x) (No_rec y)
    := No_ind_le (fun _ => A) (fun _ _ _ a b => dle a b)
                 (fun _ _ _ a b => dlt a b) _ _ _ _ _ x y p.

  Definition No_rec_lt (x y : No) (p : x < y)
  : dlt (No_rec x) (No_rec y)
    := No_ind_lt (fun _ => A) (fun _ _ _ a b => dle a b)
                 (fun _ _ _ a b => dlt a b) _ _ _ _ _ x y p.

  Definition No_rec_package
  : { f : No -> A &
      (forall (x y : No) (p : x <= y), dle (f x) (f y)) *
      (forall (x y : No) (p : x < y), dlt (f x) (f y)) }
    := ( No_rec ; (No_rec_le , No_rec_lt) ).

End NoRec.

(** ** Conway's Theorem 0 *)

Lemma Conway_theorem0_lemma1 `{Funext} (x : No@{i}) (xle : x <= x)
      (L' R' : Type@{i}) (yL : L' -> No@{i}) (yR : R' -> No@{i})
      (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
      (l : L') (p : x = yL l)
: x < {{ yL | yR // ycut }}.
Proof.
  generalize dependent x; refine (No_ind_hprop _ _); intros.
  apply lt_l with l.
  exact (transport (fun z => {{ xL | xR // xcut}} <= z) p xle).
Defined.

Lemma Conway_theorem0_lemma2 `{Funext} (x : No@{i}) (xle : x <= x)
      (L' R' : Type@{i}) (yL : L' -> No@{i}) (yR : R' -> No@{i})
      (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
      (r : R') (p : x = yR r)
: {{ yL | yR // ycut }} < x.
Proof.
  generalize dependent x; refine (No_ind_hprop _ _); intros.
  apply lt_r with r.
  exact (transport (fun z => z <= {{ xL | xR // xcut}}) p xle).
Defined.

Theorem Conway_theorem0_i `{Funext} (x : No)
: x <= x.
Proof.
  revert x; refine (No_ind_hprop _ _); intros.
  apply le_lr.
  - intros l. refine (Conway_theorem0_lemma1 (xL l) (IHL l) _ _ _ _ _ _ 1).
  - intros r. refine (Conway_theorem0_lemma2 (xR r) (IHR r) _ _ _ _ _ _ 1).
Defined.

Instance reflexive_le `{Funext} : Reflexive le
  := Conway_theorem0_i.

Theorem Conway_theorem0_ii_l `{Funext}
        (L R : Type@{i}) (xL : L -> No@{i}) (xR : R -> No@{i})
        (xcut : forall (l:L) (r:R), (xL l) < (xR r))
        (l : L)
: xL l < {{ xL | xR // xcut }}.
Proof.
  refine (Conway_theorem0_lemma1 (xL l) _ _ _ _ _ _ _ 1).
  apply Conway_theorem0_i.
Defined.

Theorem Conway_theorem0_ii_r `{Funext}
        (L R : Type@{i}) (xL : L -> No@{i}) (xR : R -> No@{i})
        (xcut : forall (l:L) (r:R), (xL l) < (xR r))
        (r : R)
: {{ xL | xR // xcut }} < xR r.
Proof.
  refine (Conway_theorem0_lemma2 (xR r) _ _ _ _ _ _ _ 1).
  apply Conway_theorem0_i.
Defined.

Global Instance isset_No `{Funext} : IsHSet No.
Proof.
  refine (@isset_hrel_subpaths No (fun (x y:No) => (x <= y) * (y <= x)) _ _ _).
  - intros x; split; apply Conway_theorem0_i.
  - intros x y [xley ylex]; apply path_No; assumption.
Defined.

(** ** Negation *)

Definition negate : No -> No.
Proof.
  refine (No_rec No (fun x y => y <= x) (fun x y => y < x)
                 _ _ _ _ _); intros.
  - exact {{ fxR | fxL // fun r l => fxcut l r }}.
  - apply path_No; assumption.
  - cbn in *. apply le_lr; intros; [ apply dq | apply dp ].
  - cbn in *. apply lt_r with l; intros; assumption.
  - cbn in *. apply lt_l with r; intros; assumption.
Defined.

(** The following proof verifies that [No_rec] reduces definitionally when applied to a cut (although it does produce quite a large term). *)
Goal negate one = minusone.
Proof.
  apply path_No; apply le_lr; intros.
  (** Since [le_lr] only proves inequality of cuts, this would not work if [negate] didn't compute to a cut when applied to a cut. *)
  - elim l.
  - apply lt_r with r.
    apply le_lr; apply Empty_ind.
  - elim l.
  - apply lt_r with r.
    apply le_lr; apply Empty_ind.
Qed.

(** ** Encode-decode to characterize [<] and [<=] recursively (Theorem 11.6.7). *)

Section NoCodes.
  Context `{Univalence}.

  Let A := {le'_x : No -> hProp &
           {lt'_x : No -> hProp &
           (forall y : No, lt'_x y -> le'_x y) *
           (forall y z : No, le'_x y -> y <= z -> le'_x z) *
           (forall y z : No, le'_x y -> y < z -> lt'_x z) *
           (forall y z : No, lt'_x y -> y <= z -> lt'_x z)} }.

  Section Inner.

    Context {L R : Type@{i} } (xL : L -> No@{i}) (xR : R -> No@{i})
            (xcut : forall (l : L) (r : R), xL l < xR r)
            (xL_let : L -> A) (xR_let : R -> A)
            (x_lt_le : forall (l : L) (r : R) (y : No),
                         (xR_let r).1 y -> ((xL_let l).2).1 y).

    Let A' (y : No) : Type
    := { lelt'_x_y : hProp * hProp &
         (snd lelt'_x_y -> fst lelt'_x_y) *
         (forall l : L, fst lelt'_x_y -> ((xL_let l).2).1 y) *
         (forall r : R, (xR_let r).1 y -> snd lelt'_x_y) }.

    Let A'le (y z : No) (p : y <= z) (tr : A' y) (sq : A' z) : Type
      := (fst tr.1 -> fst sq.1) * (snd tr.1 -> snd sq.1).

    Let A'lt (y z : No) (p : y < z) (tr : A' y) (sq : A' z) : Type
      := (fst tr.1 -> snd sq.1).

    Local Definition inner_package
    : { inner : forall (y : No), A' y &
       (forall y z p, A'le y z p (inner y) (inner z)) *
       (forall y z p, A'lt y z p (inner y) (inner z)) }.
    Proof.
      refine (No_ind_package A' A'le A'lt _ _ _ _ _ );
      unfold A', A'le, A'lt; try exact _.
      - intros L' R' yL yR ycut x_let_yL x_let_yR y_lt_le.
        set (y := {{ yL | yR // ycut }}).
        exists (BuildhProp
                  ((forall l, (xL_let l).2.1 y) *
                   (forall r', snd (x_let_yR r').1)) ,
                (hor {l':L' & fst (x_let_yL l').1}
                    {r:R   & (xR_let r).1 y})).
        abstract (
            refine ((_,_),_);
            [ intros h; strip_truncations;
              destruct h as [[l' h]|[r h]]; split; intros;
              [ refine (snd (fst (xL_let l).2.2) (yL l') y _ _);
                [ refine (fst (fst (fst (xL_let l).2.2)) (yL l') _);
                  exact (snd (fst (x_let_yL l').2) l h)
                | by apply Conway_theorem0_ii_l ]
              | exact (y_lt_le l' r' h)
              | exact (x_lt_le l r y h)
              | refine (snd (x_let_yR r').2 r _);
                refine (fst (fst (fst (xR_let r).2.2)) _ _);
                refine (snd (fst (xR_let r).2.2) y (yR r') h _);
                apply Conway_theorem0_ii_r ]
            | intros l [h k]; apply h
            | intros r h; apply tr, inr; exact (r;h) ] ).
      - abstract (
            intros y z
                   [[x_le_y x_lt_y] ?]
                   [[x_le_z x_lt_z] ?]
                   p q;
            cbn; intros [p1 p2] [q1 q2];
            rewrite transport_sigma'; cbn;
            refine (path_sigma' _
                      (path_prod' (path_hprop (equiv_iff_hprop p1 q1))
                                  (path_hprop (equiv_iff_hprop p2 q2)))
                      _);
            apply path_ishprop ).
      - abstract (
            cbn;
            intros L' R' yL yR ycut x_let_yL x_let_yR y_lt_le;
            set (y := {{ yL | yR // ycut }});
            intros L'' R'' zL zR zcut x_let_zL x_let_zR z_lt_le;
            set (z := {{ zL | zR // zcut }});
            intros yL_lt_z h1 y_lt_zR h2;
            assert (y_le_z := le_lr yL yR ycut zL zR zcut yL_lt_z y_lt_zR);
            split; [ intros [h3 h4]; split
                   | intros h3; strip_truncations;
                     destruct h3 as [[l' h3]|[r h3]] ] ;
            [ intros l; refine (snd (xL_let l).2.2 y z (h3 l) y_le_z)
            | intros r''; refine (h2 r'' (h3 , h4))
            | refine (h1 l' h3)
            | apply tr, inr; exists r;
              refine (snd (fst (fst (xR_let r).2.2)) y z h3 y_le_z) ] ).
      - abstract (
            cbn;
            intros L' R' yL yR ycut x_let_yL x_let_yR y_lt_le;
            set (y := {{ yL | yR // ycut }});
            intros L'' R'' zL zR zcut x_let_zL x_let_zR z_lt_le;
            set (z := {{ zL | zR // zcut }});
            intros l'' y_le_zL [h1 h2] x_le_y;
            apply tr, inl; exact (l''; h1 x_le_y) ).
      - abstract (
            cbn;
            intros L' R' yL yR ycut x_let_yL x_let_yR y_lt_le;
            set (y := {{ yL | yR // ycut }});
            intros L'' R'' zL zR zcut x_let_zL x_let_zR z_lt_le;
            set (z := {{ zL | zR // zcut }});
            intros r' yR_le_z [h1 h2] x_le_y;
            apply h2; exact (snd x_le_y r') ).
    Defined.
  
    Local Definition inner (y : No) : A' y
      := inner_package.1 y.

    (** These computation laws hold definitionally, but it helps Coq out if we prove them explicitly and then rewrite along them later. *)
    Definition inner_cut_le
               (L' R' : Type@{i}) (yL : L' -> No@{i}) (yR : R' -> No@{i})
               (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
    : fst (inner {{ yL | yR // ycut }}).1 =
      (BuildhProp ((forall l, (xL_let l).2.1 {{ yL | yR // ycut }}) *
                   (forall r', snd (inner (yR r')).1)))
      := 1.

    Definition inner_cut_lt
               (L' R' : Type@{i}) (yL : L' -> No@{i}) (yR : R' -> No@{i})
               (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
    : snd (inner {{ yL | yR // ycut }}).1 =
      (hor {l':L' & fst (inner (yL l')).1}
           {r:R & (xR_let r).1 {{ yL | yR // ycut }} })
      := 1.
        
    Local Definition inner_le y z p : A'le y z p (inner y) (inner z)
      := fst (inner_package.2) y z p.

    Local Definition inner_lt y z p : A'lt y z p (inner y) (inner z)
      := snd (inner_package.2) y z p.

  End Inner.

  Arguments inner : simpl never.

  Definition No_codes_package
  : { lelt : No -> A &
         (forall (x y : No), (x <= y) ->
            forall z, ((lelt y).1 z -> (lelt x).1 z) *
                      ((lelt y).2.1 z -> (lelt x).2.1 z)) *
         (forall (x y : No), (x < y) ->
            forall z, ((lelt y).1 z -> (lelt x).2.1 z)) }.
  Proof.
    refine (No_rec_package A
              (fun dm ht => forall y, (ht.1 y -> dm.1 y)
                                      * (ht.2.1 y -> dm.2.1 y))
              (fun dm ht => forall y, (ht.1 y -> dm.2.1 y))
              _ _ _ _ _).
    - intros L R xL xR xcut xL_let xR_let x_lt_le.
      pose (x := {{ xL | xR // xcut }}).
      exists (fun y => fst (inner xL_let xR_let x_lt_le y).1).
      exists (fun y => snd (inner xL_let xR_let x_lt_le y).1).
      abstract (
          repeat split;
          [ intros y; exact (fst (fst (inner xL_let xR_let x_lt_le y).2))
          | intros y z x_le_y y_le_z;
            exact (fst (inner_le xL_let xR_let x_lt_le y z y_le_z) x_le_y)
          | intros y z x_le_y y_lt_z;
            exact (inner_lt xL_let xR_let x_lt_le y z y_lt_z x_le_y)
          | intros y z x_lt_y y_le_z;
            exact (snd (inner_le xL_let xR_let x_lt_le y z y_le_z) x_lt_y) ]).
    - abstract (
          intros [x_le [x_lt ?]] [x_le' [x_lt' ?]] p q; cbn in p, q;
          refine (path_sigma' _ _ _);
          [ apply path_arrow; intros y; apply path_hprop, equiv_iff_hprop;
            [ exact (fst (q y)) | exact (fst (p y)) ]
          | rewrite transport_sigma'; cbn;
            refine (path_sigma' _ _ _);
            [ apply path_arrow; intros y; apply path_hprop, equiv_iff_hprop;
              [ exact (snd (q y)) | exact (snd (p y)) ]
            | apply path_ishprop ] ] ).
    - abstract (
          intros L R xL xR xcut xL_let xR_let x_le_lt
                 L' R' yL yR ycut yL_let yR_let y_le_lt;
          set (x := {{ xL | xR // xcut }});
          set (y := {{ yL | yR // ycut }});
          cbn;
          intros xL_lt_y xL_lt_z x_lt_yR le_lt_y;
          refine (No_ind_hprop _ _);
          intros L'' R'' zL zR zcut zLH zRH; split;
          [ rewrite !inner_cut_le;
            intros y_le_z; split;
            [ intros l; refine (xL_lt_z l {{ zL | zR // zcut }} y_le_z)
            | intros r; refine (snd (zRH r) (snd y_le_z r)) ]
          | rewrite !inner_cut_lt;
            intros y_lt_z; strip_truncations;
            destruct y_lt_z as [[l y_le_zL]|[r yR_le_z]];
            [ apply tr; left; exact (l; fst (zLH l) y_le_zL)
            | refine (le_lt_y r {{ zL | zR // zcut }} yR_le_z) ]] ).
    - abstract (
          intros L R xL xR xcut xL_let xR_let x_le_lt
                 L' R' yL yR ycut yL_let yR_let y_le_lt;
          set (x := {{ xL | xR // xcut }});
          set (y := {{ yL | yR // ycut }});
          cbn; intros l x_le_yL zH;
          refine (No_ind_hprop _ _);
          intros L'' R'' zL zR zcut zLH zRH y_le_z;
          refine (snd (zH {{ zL | zR // zcut }}) _);
          rewrite inner_cut_le in y_le_z;
          exact (fst y_le_z l) ).
    - abstract (
          intros L R xL xR xcut xL_let xR_let x_le_lt
                 L' R' yL yR ycut yL_let yR_let y_le_lt;
          set (x := {{ xL | xR // xcut }});
          set (y := {{ yL | yR // ycut }});
          cbn; intros r xR_le_y zH;
          refine (No_ind_hprop _ _);
          intros L'' R'' zL zR zcut zLH zRH y_le_z;
          rewrite inner_cut_lt;
          apply tr; right; exists r;
          refine (fst (zH {{ zL | zR // zcut }}) y_le_z) ).
  Defined.

  Definition le' (x y : No) : hProp
    := (No_codes_package.1 x).1 y.

  Definition lt' (x y : No) : hProp
    := (No_codes_package.1 x).2.1 y.

  Definition lt'_le' x y
  : lt' x y -> le' x y
    := (fst (fst (fst (No_codes_package.1 x).2.2)) y).

  Definition le_le'_trans x y z
  : x <= y -> le' y z -> le' x z
    := fun p q => (fst (fst (No_codes_package.2) x y p z) q).

  Definition le_lt'_trans x y z
  : x <= y -> lt' y z -> lt' x z
    := fun p q => (snd (fst (No_codes_package.2) x y p z) q).

  Definition lt_le'_trans x y z
  : x < y -> le' y z -> lt' x z
    := fun p q => (snd (No_codes_package.2) x y p z q).

  Definition le'_le_trans x y z
  :  le' x y -> y <= z -> le' x z
    := fun p q => (snd (fst (fst (No_codes_package.1 x).2.2)) y z p q).

  Definition le'_lt_trans x y z
  : le' x y -> y < z -> lt' x z
    := fun p q => (snd (fst (No_codes_package.1 x).2.2) y z p q).

  Definition lt'_le_trans x y z
  : lt' x y -> y <= z -> lt' x z
    := fun p q => (snd (No_codes_package.1 x).2.2 y z p q).

  (** These computation laws hold definitionally, but it takes Coq a little while to verify that.  Thus, we prove them once and then [rewrite] along them later, so we don't have to do the verification every time. *)
  Definition le'_cut
             (L R : Type) (xL : L -> No) (xR : R -> No)
             (xcut : forall (l : L) (r : R), xL l < xR r)
             (L' R' : Type) (yL : L' -> No) (yR : R' -> No)
             (ycut : forall (l : L') (r : R'), yL l < yR r)
  : le' {{xL | xR // xcut}} {{yL | yR // ycut}}
    = ((forall l, lt' (xL l) {{ yL | yR // ycut }}) *
       (forall r', lt' {{ xL | xR // xcut }} (yR r')))
        (** For some reason, Coq has a really hard time checking the version of this that asserts an equality in [hProp].  But fortunately, we only ever really need the equality of types. *)
        :> Type
    := 1.

  Definition lt'_cut
             (L R : Type) (xL : L -> No) (xR : R -> No)
             (xcut : forall (l : L) (r : R), xL l < xR r)
             (L' R' : Type) (yL : L' -> No) (yR : R' -> No)
             (ycut : forall (l : L') (r : R'), yL l < yR r)
  : lt' {{xL | xR // xcut}} {{yL | yR // ycut}}
    = (hor {l':L' & le' {{ xL | xR // xcut }} (yL l')}
                  {r:R   & le' (xR r) {{ yL | yR // ycut }} })
    := 1.

  Definition No_encode_le_lt (x y : No)
  : ((x <= y) -> (le' x y)) * ((x < y) -> (lt' x y)).
  Proof.
    refine (No_ind_le_lt (fun _ => Unit)
                         (fun x y _ _ _ => le' x y)
                         (fun x y _ _ _ => lt' x y)
                         _ _ _ _ _ x y).
    + intros; exact tt.
    + intros; apply path_contr.
    + intros L R xL xR xcut _ _ xcut'
             L' R' yL yR ycut _ _ ycut'
             xL_lt_y xL_lt_y' x_lt_yR x_lt_yR'.
      rewrite le'_cut.
      exact (xL_lt_y' , x_lt_yR').
    + intros L R xL xR xcut _ _ xcut'
             L' R' yL yR ycut _ _ ycut'
             l x_le_yL x_le_yL'.
      rewrite lt'_cut.
      apply tr; left. exists l. exact x_le_yL'.
    + intros L R xL xR xcut _ _ xcut'
             L' R' yL yR ycut _ _ ycut'
             r xR_le_y xR_le_y'.
      rewrite lt'_cut.
      apply tr; right. exists r. exact xR_le_y'.
  Qed.

  Definition No_decode_le_lt (x y : No)
  : ((le' x y) -> (x <= y)) * ((lt' x y) -> (x < y)).
  Proof.
    revert x y.
    refine (No_ind_hprop _ _); intros L R xL xR xcut xHL xHR.
    (** TODO: Why can't Coq find [trunc_arrow] here? *)
    refine (@No_ind_hprop _
              (fun y => @trunc_prod _ _ trunc_arrow _ trunc_arrow) _).
    intros L' R' yL yR ycut yHL yHR. split.
    - intros x_le_y.
      rewrite le'_cut in x_le_y.
      exact (le_lr xL xR xcut yL yR ycut
                   (fun l => snd (xHL l _) (fst x_le_y l))
                   (fun r => snd (yHR r) (snd x_le_y r))).
    - intros x_lt_y.
      rewrite lt'_cut in x_lt_y.
      strip_truncations; destruct x_lt_y as [[l x_le_yL]|[r xR_le_y]].
      + apply lt_l with l.
        exact (fst (yHL l) x_le_yL).
      + apply lt_r with r.
        exact (fst (xHR r _) xR_le_y).
  Qed.

  Definition No_encode_le x y := fst (No_encode_le_lt x y).
  Definition No_encode_lt x y := snd (No_encode_le_lt x y).
  Definition No_decode_le x y := fst (No_decode_le_lt x y).
  Definition No_decode_lt x y := snd (No_decode_le_lt x y).

  Corollary lt_le (x y : No) (p : x < y) : x <= y.
  Proof.
    apply No_decode_le.
    apply lt'_le'.
    apply No_encode_lt.
    assumption.
  Qed.

  (** Conway's theorem 1 *)
  Corollary le_le_trans (x y z : No)
  : (x <= y) -> (y <= z) -> (x <= z).
  Proof.
    intros p q.
    apply No_decode_le.
    refine (le_le'_trans x y z p _).
    apply No_encode_le.
    assumption.
  Qed.

  Corollary le_lt_trans (x y z : No)
  : (x <= y) -> (y < z) -> (x < z).
  Proof.
    intros p q.
    apply No_decode_lt.
    refine (le_lt'_trans x y z p _).
    apply No_encode_lt.
    assumption.
  Qed.

  Corollary lt_le_trans (x y z : No)
  : (x < y) -> (y <= z) -> (x < z).
  Proof.
    intros p q.
    apply No_decode_lt.
    refine (lt_le'_trans x y z p _).
    apply No_encode_le.
    assumption.
  Qed.

End NoCodes.
