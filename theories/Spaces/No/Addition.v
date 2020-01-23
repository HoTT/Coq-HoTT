(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext.
Require Import HoTT.Spaces.No.Core HoTT.Spaces.No.Negation.

Local Open Scope path_scope.
Local Open Scope surreal_scope.

(** * Addition of surreal numbers *)

(** Addition requires the option sorts to be closed under finite sums. *)
Class HasAddition (S : OptionSort) :=
  { empty_options : InSort S Empty Empty
    ; sum_options : forall L R L' R',
        InSort S L R -> InSort S L' R' -> InSort S (L + L') (R + R')
  }.
Existing Instance empty_options.
Existing Instance sum_options.

Global Instance hasaddition_maxsort : HasAddition MaxSort
  := { empty_options := tt ;
       sum_options := fun _ _ _ _ _ _ => tt }.

Global Instance hasaddition_ordsort : HasAddition OrdSort
  := { empty_options := idmap ;
       sum_options := fun _ _ _ _ f g => sum_ind _ f g }.

Global Instance hasaddition_decsort : HasAddition DecSort.
Proof.
  constructor.
  - apply insort_decsort.
  - intros L R L' R' [? ?] [? ?]; split; exact _.
Qed.

Section Addition.
  Context `{Univalence}.
  Context {S : OptionSort@{i}} `{HasAddition S}.
  Let No := GenNo S.

  Section Inner.

    Context {L R : Type@{i} } {Sx : InSort@{i} S L R}
            (xL : L -> No@{i}) (xR : R -> No@{i})
            (xcut : forall (l : L) (r : R), xL l < xR r).

    Let A := {g : No@{i} -> No@{i} &
              (forall x y : No@{i}, x <= y -> g x <= g y) *
              (forall x y : No@{i}, x < y -> g x < g y)}.

    Context (xL_plus : L -> A) (xR_plus : R -> A)
            (xL_lt_xR_plus : forall (l : L) (r : R) (x : No),
                               (xL_plus l).1 x < (xR_plus r).1 x).

    Definition plus_inner
    : { g : forall (y : No@{i}),
              { x_plus_y : No@{i} &
                (forall l, (xL_plus l).1 y < x_plus_y) *
                (forall r, x_plus_y < (xR_plus r).1 y) } &
        (forall y z : No, y <= z -> (g y).1 <= (g z).1) *
        (forall y z : No, y <  z -> (g y).1 <  (g z).1) }.
    Proof.
      simple refine (No_ind_package
                (fun y => { x_plus_y : No &
                            (forall l, (xL_plus l).1 y < x_plus_y) *
                            (forall r, x_plus_y < (xR_plus r).1 y) })
                (fun _ _ _ z w => z.1 <= w.1)
                (fun _ _ _ z w => z.1 < w.1)
                _ _ _ _ _).
      - intros L' R' ? yL yR ycut x_plus_yL x_plus_yR x_plus_yL_lt_yR.
        pose (L'' := L + L').  pose (R'' := R + R').
        pose (zL := sum_ind (fun _ => No)
                            (fun l => (xL_plus l).1 {{ yL | yR // ycut }})
                            (fun l => (x_plus_yL l).1)
                    : L'' -> No).
        pose (zR := sum_ind (fun _ => No)
                            (fun r => (xR_plus r).1 {{ yL | yR // ycut }})
                            (fun r => (x_plus_yR r).1)
                    : R'' -> No).
        assert (zcut : forall (l:L'') (r:R''), zL l < zR r).
        { abstract (
          intros [l|l] [r|r]; cbn;
          [ apply xL_lt_xR_plus
          | transitivity ((xL_plus l).1 (yR r));
            [ apply (snd (xL_plus l).2), lt_ropt; exact _
            | exact (fst (x_plus_yR r).2 l) ]
          | transitivity ((xR_plus r).1 (yL l));
            [ exact (snd (x_plus_yL l).2 r)
            | apply (snd (xR_plus r).2), lt_lopt; exact _ ]
          | apply x_plus_yL_lt_yR ]). }
        assert (InSort S L'' R'') by (apply sum_options; exact _).
        exists ({{ zL | zR // zcut }}); split.
        + intros l.
          refine (lt_lopt zL zR zcut (inl l)).
        + intros r.
          refine (lt_ropt zL zR zcut (inl r)).
      - abstract (
        intros x y [a ?] [b ?] p q r s;
        rewrite transport_sigma; cbn in *;
        apply path_sigma_hprop, path_No; cbn;
        rewrite transport_const; assumption).
      - abstract (
        intros L' R' ? yL yR ycut x_plus_yL x_plus_yR x_plus_yL_lt_yR
               L'' R'' ? zL zR zcut x_plus_zL x_plus_zR x_plus_zL_lt_zR
               yL_lt_z x_plus_yL_lt_z y_lt_zR x_plus_y_lt_zR;
        cbn in *;
        apply le_lr; [ intros [l|l] | intros [r|r] ]; cbn;
        [ refine (le_lt_trans (fst (xL_plus l).2 _ {{ zL | zR // zcut}} _) _);
          [ by (apply le_lr; assumption)
          | refine (lt_lopt _ _ _ (inl l)) ]
        | exact (x_plus_yL_lt_z l)
        | refine (lt_le_trans _
                    (fst (xR_plus r).2 {{ yL | yR // ycut}} _ _));
          [ refine (lt_ropt _ _ _ (inl r))
          | by (apply le_lr; assumption) ]
        | exact (x_plus_y_lt_zR r) ] ).
      - abstract (
        intros L' R' ? yL yR ycut x_plus_yL x_plus_yR x_plus_yL_lt_yR
               L'' R'' ? zL zR zcut x_plus_zL x_plus_zR x_plus_zL_lt_zR
               l y_le_zL x_plus_y_le_zL; cbn;
        apply lt_l with (inr l);
        apply x_plus_y_le_zL ).
      - abstract (
        intros L' R' ? yL yR ycut x_plus_yL x_plus_yR x_plus_yL_lt_yR
               L'' R'' ? zL zR zcut x_plus_zL x_plus_zR x_plus_zL_lt_zR
               r yR_le_z x_plus_yR_le_z; cbn;
        apply lt_r with (inr r);
        apply x_plus_yR_le_z).
    Defined.

    (** We now prove a computation law for [plus_inner].  It holds definitionally, so we would like to prove it with just [:= 1] and then rewrite along it later, as we did above.  However, there is a subtlety in that the output should be a surreal defined by a cut, which in particular includes a proof of cut-ness, and that proof is rather long, so we would not like to see it in the type of this lemma.  Thus, instead we assert only that there *exists* some proof of cut-ness and an equality. *)
    Definition plus_inner_cut
               {L' R' : Type@{i} } {Sy : InSort@{i} S L' R'}
               (yL : L' -> No@{i}) (yR : R' -> No@{i})
               (ycut : forall (l : L') (r : R'), yL l < yR r)
    : let L'' := L + L' in
      let R'' := R + R' in
      let zL := sum_ind (fun _ => No)
                        (fun l => (xL_plus l).1 {{ yL | yR // ycut }})
                        (fun l => (plus_inner.1 (yL l)).1)
                : L'' -> No in
      let zR := sum_ind (fun _ => No)
                        (fun r => (xR_plus r).1 {{ yL | yR // ycut }})
                        (fun r => (plus_inner.1 (yR r)).1)
                : R'' -> No in
      let Sz := sum_options L R L' R' _ _ in
      { zcut : forall (l:L'') (r:R''), zL l < zR r &
        (plus_inner.1 {{ yL | yR // ycut }}).1 = (@No_cut _ _ _ Sz zL zR zcut) }.
    Proof.
      (** Now we tell Coq that we want the equality to be definitional, and let it figure out what the proof of cut-ness has to be. *)
      eexists.
      (** Adding [rel_hnf] here speeds things up considerably, possibly because it puts the terms in a form where the evar can be instantiated without unfolding or reduction, preventing backtracking across the evar instantiation. *)
      rel_hnf. reflexivity.
    Qed.

  End Inner.

  Definition plus_outer
  : { f : No@{i} -> { g : No@{i} -> No@{i} &
                  (forall x y, x <= y -> g x <= g y) *
                  (forall x y, x <  y -> g x <  g y) } &
      (forall x y, x <= y -> forall z, (f x).1 z <= (f y).1 z) *
      (forall x y, x <  y -> forall z, (f x).1 z <  (f y).1 z) }.
  Proof.
    refine (No_rec_package
              {g : No -> No &
                (forall x y, x <= y -> g x <= g y) *
                (forall x y, x <  y -> g x <  g y) }
              (fun g h => forall x, g.1 x <= h.1 x)
              (fun g h => forall x, g.1 x <  h.1 x)
              (fun L R Sx xL xR xcut xL_plus xR_plus xL_lt_xR_plus =>
                 let g := plus_inner xL_plus xR_plus xL_lt_xR_plus in
                 ((fun y => (g.1 y).1) ; (g.2)))
               _ _ _ _).
    - abstract (
      intros [g ?] [h ?] p q;
      apply path_sigma_hprop; cbn in *;
      apply path_arrow; intros x;
      apply path_No; [ apply p | apply q ] ).
    - abstract (
      intros L R ? xL xR xcut xL_plus xR_plus xL_lt_xR_plus
           L' R' ? yL yR ycut yL_plus yR_plus yL_lt_yR_plus;
      intros xL_lt_y xL_lt_y_plus x_lt_yR x_lt_yR_plus z;
      lazy beta zeta in *; cbn [pr1] in *;
      pattern z; refine (No_ind_hprop _ _ z);
      intros L'' R'' ? zL zR zcut x_le_y_plus_zL x_le_y_plus_zR;
      destruct (plus_inner_cut xL_plus xR_plus xL_lt_xR_plus
                               zL zR zcut) as [xzcut p]; rewrite p;
      destruct (plus_inner_cut yL_plus yR_plus yL_lt_yR_plus
                               zL zR zcut) as [yzcut q];rewrite q;
      apply le_lr; [ intros [l|l] | intros [r|r] ];
      [ (** x^L + z < y + z *)
        specialize (xL_lt_y_plus l {{ zL | zR // zcut }});
        rewrite q in xL_lt_y_plus;
        exact xL_lt_y_plus
      | (** x + z^L < y + z *)
        refine (le_lt_trans (x_le_y_plus_zL l) _);
        refine (lt_lopt _ _ _ (inr l))
      | (** x + z < y^R + z *)
        specialize (x_lt_yR_plus r {{ zL | zR // zcut }});
        rewrite p in x_lt_yR_plus;
        exact x_lt_yR_plus
      | (** x + z < y + z^R *)
        refine (lt_le_trans _ (x_le_y_plus_zR r));
        refine (lt_ropt _ _ _ (inr r)) ]).
    - abstract (
      intros L R ? xL xR xcut xL_plus xR_plus xL_lt_xR_plus
             L' R' ? yL yR ycut yL_plus yR_plus yL_lt_yR_plus;
      intros l x_le_yL x_le_yL_plus z;
      lazy beta zeta in *; cbn [pr1] in *;
      pattern z; refine (No_ind_hprop _ _ z);
      intros L'' R'' ? zL zR zcut x_le_y_plus_zL x_le_y_plus_zR;
      destruct (plus_inner_cut xL_plus xR_plus xL_lt_xR_plus
                               zL zR zcut) as [xzcut p]; rewrite p;
      destruct (plus_inner_cut yL_plus yR_plus yL_lt_yR_plus
                               zL zR zcut) as [yzcut q];rewrite q;
      refine (le_lt_trans (x_le_yL_plus {{ zL | zR // zcut }}) _);
      refine (lt_lopt _ _ _ (inl l)) ).
    - abstract (
      intros L R ? xL xR xcut xL_plus xR_plus xL_lt_xR_plus
             L' R' ? yL yR ycut yL_plus yR_plus yL_lt_yR_plus;
      intros r xR_le_y xR_le_y_plus z;
      lazy beta zeta in *; cbn [pr1] in *;
      pattern z; refine (No_ind_hprop _ _ z);
      intros L'' R'' ? zL zR zcut x_le_y_plus_zL x_le_y_plus_zR;
      destruct (plus_inner_cut xL_plus xR_plus xL_lt_xR_plus
                               zL zR zcut) as [xzcut p]; rewrite p;
      destruct (plus_inner_cut yL_plus yR_plus yL_lt_yR_plus
                               zL zR zcut) as [yzcut q];rewrite q;
      refine (lt_le_trans _ (xR_le_y_plus {{ zL | zR // zcut }}));
      refine (lt_ropt _ _ _ (inl r)) ).
  Defined.

  Definition plus (x y : No) : No
    := (plus_outer.1 x).1 y.

  Infix "+" := plus : surreal_scope.

  Definition plus_le_l (x x' y : No@{i}) (p : x <= x')
  : (x + y) <= (x' + y)
    := fst (plus_outer.2) x x' p y.

  Definition plus_lt_l (x x' y : No@{i}) (p : x < x')
  : (x + y) < (x' + y)
    := snd (plus_outer.2) x x' p y.

  Definition plus_le_r (x y y' : No@{i}) (p : y <= y')
  : (x + y) <= (x + y')
    := fst (plus_outer.1 x).2 y y' p.

  Definition plus_lt_r (x y y' : No@{i}) (p : y < y')
  : (x + y) < (x + y')
    := snd (plus_outer.1 x).2 y y' p.

  (** See the remarks above [plus_inner_cut] to explain the type of this lemma. *)
  Definition plus_cut
             {L R : Type@{i} } {Sx : InSort@{i} S L R}
             (xL : L -> No@{i}) (xR : R -> No@{i})
             (xcut : forall (l : L) (r : R), xL l < xR r)
             {L' R' : Type@{i} } {Sy : InSort@{i} S L' R'}
             (yL : L' -> No@{i}) (yR : R' -> No@{i})
             (ycut : forall (l : L') (r : R'), yL l < yR r)
  : let L'' := (L + L')%type in
    let R'' := (R + R')%type in
    let x := {{ xL | xR // xcut }} in
    let y := {{ yL | yR // ycut }} in
    let zL := sum_ind (fun _ => No)
                      (fun l => (xL l) + y) (fun l => x + (yL l))
              : L'' -> No in
    let zR := sum_ind (fun _ => No)
                      (fun r => (xR r) + y) (fun r => x + (yR r))
              : R'' -> No in
    let Sz := sum_options L R L' R' _ _ in
    { zcut : forall (l:L'') (r:R''), zL l < zR r &
      x + y = @No_cut _ _ _ Sz zL zR zcut }
    := plus_inner_cut (Sx := Sx)
         (fun l => plus_outer.1 (xL l))
         (fun r => plus_outer.1 (xR r))
         (fun l r => snd plus_outer.2 (xL l) (xR r) (xcut l r))
         yL yR ycut.

  (** Because the conclusion of [plus_cut] is a sigma-type whose second component is the real equality we want to rewrite along, in order to rewrite along it we have to first destruct it.  This tactic takes care of that for us. *)
  Ltac do_plus_cut :=
    repeat match goal with
    | [ |- context ctx [ {{ ?xL | ?xR // ?xcut }} + {{ ?yL | ?yR // ?ycut }} ] ] =>
      let xycut := fresh "cut" in
      let p := fresh "p" in
      destruct (plus_cut xL xR xcut yL yR ycut) as [xycut p];
        rewrite p; clear p
    end.

  (** Conway proves the basic properties of arithmetic using "one-line proofs".  We can't quite do them in one line of Ltac, but the following tactic does help a lot.  Note that it is specific to addition.  It requires the caller to specify the equivalences along which to identify the indexing types for the options, as well as a rewriting tactic for evaluating those equivalences on constructors.  Unfortunately, it doesn't usually manage to finish the whole proof, since in general it can't guess how to use the inductive hypotheses.  It's usually fairly easy to finish all the cases it leaves over, but we do generally have to refer by name to the inductive hypotheses that were automatically named by [intros] here.  I haven't thought of a good solution to that. *)
  Local Opaque No_cut plus. (* required to make [rewrite] fail quickly *)
  Local Unset Keyed Unification. (* shaves another second or two off of [rewrite] *)
  Tactic Notation "one_line_proof" uconstr(eL) uconstr(eR) :=
    unfold No in *;
    repeat_No_ind_hprop;
    do_plus_cut;
    refine (path_No_easy _ _ _ _ eL eR _ _ _ _);
    intros;
    repeat match goal with
           | [ H : (?A + ?B)%type |- _ ] => destruct H
           end;
    repeat match goal with
           | [ |- context[@equiv_fun ?A ?B ?e ?v] ]
             => (* first check that we picked up either [eL] or [eR]; we can't use [unify] because it doesn't infer holes, and we can't Ltac-match on [eL] / [eR] because apparently matching on uconstr doesn't work when there are holes in the uconstr *)
             first [ let unif := constr:(idpath : e = eL) in idtac
                   | let unif := constr:(idpath : e = eR) in idtac ];
             (* assume that the term reduces to a constructor; use [hnf] to get that constructor *)
             let ef := constr:(@equiv_fun A B e v) in
             let ef' := (eval hnf in ef) in
             progress change ef with ef'
           end;
    repeat cbn [sum_ind];
    (* rewrite with induction hypotheses from [repeat_No_ind_hprop] and [do_plus_cut] *)
    repeat match goal with
           | [ |- ?x = ?x ] => reflexivity
           | [ |- ?a + _ = ?a + _ ] => apply ap
           | [ |- _ + ?a = _ + ?a ] => apply (ap (fun x => x + a))
           | [ e : Empty |- _ ] => elim e
           | [ IH : (forall lr, _ + _ = _) |- _ ]
             => rewrite IH; clear IH
           | [ IH : (forall lr, _ + _ = _ + _) |- _ ]
             => first [ rewrite IH | rewrite <- IH ]; clear IH
           | [ IH : (forall lr (y : GenNo _), _ + _ = _ + _) |- _ ]
             => first [ rewrite IH | rewrite <- IH ]; clear IH
           | [ IH : (forall lr (y z : GenNo _), _ + _ = _ + _) |- _ ]
             => first [ rewrite IH | rewrite <- IH ]; clear IH
           end.

  (** At last we are ready to prove that the surreal numbers are a commutative monoid under addition. *)

  Theorem plus_comm (x y : No) : x + y = y + x.
  Proof.
    one_line_proof (equiv_sum_symm _ _) (equiv_sum_symm _ _).
  Defined.

  Theorem plus_assoc (x y z : No) : (x + y) + z = x + (y + z).
  Proof.
    one_line_proof (equiv_sum_assoc _ _ _) (equiv_sum_assoc _ _ _);
      one_line_proof 1%equiv 1%equiv.
  Defined.

  Theorem plus_zero (x : No) : x + zero = x.
  Proof.
    unfold zero.
    one_line_proof (sum_empty_r _) (sum_empty_r _).
  Defined.

  Theorem zero_plus (x : No) : zero + x = x.
  Proof.
    unfold zero.
    one_line_proof (sum_empty_l _) (sum_empty_l _).
  Defined.

  (** If we also have negation, we can prove that it gives additive inverses, so that we have an abelian group. *)
  Context `{HasNegation S}.

  Definition plus_negate (x : No) : x + negate x = zero.
  Proof.
    unfold No in *;
    repeat_No_ind_hprop;
    destruct (negate_cut xL xR xcut) as [nxcut p];
    rewrite p; clear p;
    do_plus_cut.
    apply path_No.
    - apply le_lr; [ intros [l|r]; cbn [sum_ind] | intros [] ].
      + unfold zero in IHL; rewrite <- (IHL l); clear IHL.
        apply plus_lt_r.
        refine (lt_ropt _ _ _ l).
      + unfold zero in IHR; rewrite <- (IHR r); clear IHR.
        apply plus_lt_l.
        refine (lt_ropt _ _ _ r).
    - apply le_lr; [ intros [] | intros [r|l] ]; cbn [sum_ind].
      + unfold zero in IHR; rewrite <- (IHR r); clear IHR.
        apply plus_lt_r.
        refine (lt_lopt _ _ _ r).
      + unfold zero in IHL; rewrite <- (IHL l); clear IHL.
        apply plus_lt_l.
        refine (lt_lopt _ _ _ l).
  Defined.

  Definition sub (x y : No) : No := x + (negate y).

  Infix "-" := sub : surreal_scope.

End Addition.
