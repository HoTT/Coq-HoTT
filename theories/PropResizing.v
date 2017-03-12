(* -*- mode: coq; mode: visual-line -*-  *)
(** * Propositional resizing *)

Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext HProp.
Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Class PropResizing.
Axiom resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A}, Type@{j}.
Axiom equiv_resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A},
    A <~> resize_hprop A.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := trunc_equiv A (equiv_resize_hprop A).

(** ** Impredicative propositional truncation. *)

(** We put it in a module so that it doesn't conflict with the HIT one
if that is also assumed. *)
Module Impredicative_Merely.
Section AssumePropResizing.
  Context `{PropResizing}.

  Definition merely (A : Type@{i}) : Type@{i}
    := forall P:Type@{j}, IsHProp P -> (A -> P) -> P.

  Definition trm {A} : A -> merely A
    := fun a P HP f => f a.

  Global Instance ishprop_merely `{Funext} (A : Type) : IsHProp (merely A).
  Proof.
    exact _.
  Defined.

  Definition merely_rec {A : Type@{i}} {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : merely A -> P
    := fun ma => (equiv_resize_hprop P)^-1
                 (ma (resize_hprop P) _ (equiv_resize_hprop P o f)).

  Definition functor_merely `{Funext} {A B : Type} (f : A -> B)
    : merely A -> merely B.
  Proof.
    srefine (merely_rec (trm o f)).
  Defined.

End AssumePropResizing.
End Impredicative_Merely.

(** ** The natural numbers *)

(** Using propositional resizing and univalence, we can construct the
natural numbers rather than defining them as an inductive type.  In
concrete practice there is no reason we would want to do this, but
semantically it means that an elementary (oo,1)-topos (unlike an
elementary 1-topos) automatically has a natural numbers object. *)

Module UAPRNat.
Section AssumeStuff.
  Context {UA:Univalence} {PR:PropResizing}.
  Import Impredicative_Merely.

  Definition Graph := { V : Type & { E : V -> V -> Type & forall x y, IsHProp (E x y) } }.
  Definition vert : Graph -> Type := pr1.
  Definition edge (A : Graph) : vert A -> vert A -> Type := pr1 (pr2 A).
  Instance ishprop_edge (A : Graph) (x y : vert A) : IsHProp (edge A x y)
    := pr2 (pr2 A) x y.

  Definition equiv_path_graph (A B : Graph)
    : { f : vert A <~> vert B &
            forall x y, edge A x y <-> edge B (f x) (f y) }
        <~> (A = B).
  Proof.
    srefine (equiv_path_sigma _ A B oE _).
    srefine (equiv_functor_sigma' (equiv_path_universe (vert A) (vert B)) _).
    intros f; cbn.
    rewrite transport_sigma.
    srefine (equiv_path_sigma_hprop _ _ oE _). cbn.
    srefine (equiv_path_forall _ _ oE _).
    srefine (equiv_functor_forall' (f^-1) _).
    intros x.
    srefine (equiv_path_forall _ _ oE _).
    srefine (equiv_functor_forall' (f^-1) _).
    intros y. cbn.
    rewrite transport_arrow.
    rewrite transport_arrow_toconst.
    rewrite !transport_path_universe_V.
    rewrite !eisretr.
    srefine (equiv_path_universe _ _ oE _).
    srefine (equiv_equiv_iff_hprop _ _).
  Defined.

  Definition graph_zero : Graph
    := ( Empty ; ( fun x y => Empty_rec x ; fun x y => Empty_rec x)).

  Definition graph_succ (A : Graph) : Graph.
  Proof.
    exists (vert A + Unit); srefine (_;_).
    - intros [x|x] [y|y].
      + exact (edge A x y).
      + exact Unit.
      + exact Empty.
      + exact Unit.
    - cbn; intros [x|x] [y|y]; exact _.
  Defined.

  Definition graph_succ_top {A : Graph} (x : vert (graph_succ A))
    : edge (graph_succ A) x (inr tt).
  Proof.
    destruct x as [x|x]; exact tt.
  Defined.

  Definition graph_succ_top_unique
             {A : Graph} (y : vert (graph_succ A))
             (yt : forall x, edge (graph_succ A) x y)
    : y = inr tt.
  Proof.
    destruct y as [y|[]].
    - destruct (yt (inr tt)).
    - reflexivity.
  Defined.

  Definition graph_succ_not_top {A : Graph} (x : vert A)
    : ~(edge (graph_succ A) (inr tt) (inl x))
    := idmap.

  Definition graph_succ_not_top_unique {A : Graph} (x : vert (graph_succ A))
             (xt : ~(edge (graph_succ A) (inr tt) x))
    : is_inl x.
  Proof.
    destruct x as [x|x].
    - exact tt.
    - destruct (xt tt).
  Defined.

  Section Graph_Succ_Equiv.
    Context {A B : Graph} (f : vert (graph_succ A) <~> vert (graph_succ B))
            (e : forall x y, edge (graph_succ A) x y <-> edge (graph_succ B) (f x) (f y)).

    Definition graph_succ_equiv_inr : f (inr tt) = inr tt.
    Proof.
      apply (graph_succ_top_unique (f (inr tt))).
      intros x.
      rewrite <- (eisretr f x).
      apply (fst (e (f^-1 x) (inr tt))).
      apply graph_succ_top.
    Defined.

    Local Definition Ha : forall x, is_inl (f (inl x)).
    Proof.
      intros x.
      apply graph_succ_not_top_unique.
      rewrite <- (eisretr f (inr tt)).
      intros ed.
      apply (snd (e (f^-1 (inr tt)) (inl x))) in ed.
      pose (finr := graph_succ_equiv_inr).
      apply moveL_equiv_V in finr.
      rewrite <- finr in ed.
      exact (graph_succ_not_top x ed).
    Defined.

    Local Definition Hb : forall x, is_inr (f (inr x)).
    Proof.
      destruct x.
      srefine (transport is_inr graph_succ_equiv_inr^ tt).
    Defined.

    Definition graph_unsucc_equiv_vert : vert A <~> vert B
      := equiv_unfunctor_sum_l f Ha Hb.

    Definition graph_unsucc_equiv_edge (x y : vert A)
      : edge A x y <-> edge B (graph_unsucc_equiv_vert x) (graph_unsucc_equiv_vert y).
    Proof.
      pose (h := e (inl x) (inl y)).
      rewrite <- (unfunctor_sum_l_beta f Ha x) in h.
      rewrite <- (unfunctor_sum_l_beta f Ha y) in h.
      exact h.
    Defined.

  End Graph_Succ_Equiv.

  Definition graph_succ_path_equiv (A B : Graph)
    : (A = B) <~> (graph_succ A = graph_succ B).
  Proof.
    refine ((equiv_path_graph _ _) oE _).
    refine (_ oE (equiv_path_graph _ _)^-1).
    srefine (equiv_adjointify _ _ _ _).
    - intros [f e].
      exists (f +E 1).
      intros x y.
      destruct x as [x|x]; destruct y as [y|y]; cbn.
      + apply e.
      + split; apply idmap.
      + split; apply idmap.
      + split; apply idmap.
    - intros [f e].
      exists (graph_unsucc_equiv_vert f e).
      exact (graph_unsucc_equiv_edge f e).
    - intros [f e].
      apply path_sigma_hprop; cbn.
      apply path_equiv, path_arrow; intros [x|[]]; cbn.
      + apply unfunctor_sum_l_beta.
      + symmetry; apply graph_succ_equiv_inr, e.
    - intros [f e].
      apply path_sigma_hprop; cbn.
      apply path_equiv, path_arrow; intros x; reflexivity.
  Defined.

  Definition graph_unsucc_path (A B : Graph)
    : (graph_succ A = graph_succ B) -> A = B
    := (graph_succ_path_equiv A B)^-1.

  Definition in_N (n : Graph) : Type
    := forall (P : Graph -> Type),
           (forall A, IsHProp (P A))
           -> P graph_zero
           -> (forall A, P A -> P (graph_succ A))
           -> P n.

  Instance ishprop_in_N (n : Graph) : IsHProp (in_N n).
  Proof.
    apply trunc_forall.
  Defined.

  Definition N : Type
    := { n : Graph & in_N n }.

  Definition path_N (n m : N) : n.1 = m.1 -> n = m
    := path_sigma_hprop n m.

  Definition zero : N.
  Proof.
    exists graph_zero.
    intros P PH P0 Ps; exact P0.
  Defined.

  Definition succ : N -> N.
  Proof.
    intros [n nrec].
    exists (graph_succ n).
    intros P PH P0 Ps. apply Ps.
    exact (nrec P PH P0 Ps).
  Defined.

  (* First Peano axiom: successor is injective *)
  Definition succ_inj (n m : N) (p : succ n = succ m) : n = m.
  Proof.
    apply path_N.
    apply ((graph_succ_path_equiv n.1 m.1)^-1).
    exact (p..1).
  Defined.

  Instance ishprop_path_N (n : N) (A : Graph) : IsHProp (n.1 = A).
  Proof.
    destruct n as [n nrec]; cbn.
    apply hprop_inhabited_contr; intros [].
    apply nrec; try exact _.
    - apply contr_inhabited_hprop; try exact 1.
      apply hprop_allpath.
      equiv_intro (equiv_path_graph graph_zero graph_zero) fe.
      destruct fe as [f e].
      equiv_intro (equiv_path_graph graph_zero graph_zero) fe'.
      destruct fe' as [f' e'].
      apply equiv_ap; try exact _.
      apply path_sigma_hprop, path_equiv, path_arrow.
      intros [].
    - intros B BC.
      refine (contr_equiv (B = B) (graph_succ_path_equiv B B)).
  Defined.

  Instance ishset_N : IsHSet N.
  Proof.
    intros n m.
    change (IsHProp (n = m)).
    refine (trunc_equiv (n.1 = m.1) (equiv_path_sigma_hprop n m)).
  Defined.

  Definition graph_zero_neq_succ {A : Graph}
    : graph_zero <> graph_succ A.
  Proof.
    intros p.
    destruct ((equiv_path_graph graph_zero (graph_succ A))^-1 p) as [f e].
    exact (f^-1 (inr tt)).
  Defined.

  (* Second Peano axiom: zero is not a successor *)
  Definition zero_neq_succ (n : N) : zero <> succ n.
  Proof.
    intros p; apply pr1_path in p; refine (graph_zero_neq_succ p).
  Defined.

  (* This is sometimes necessary to avoid universe inconsistency; it's
  how the impredicativity of propositional resizing enters. *)
  Definition resize_nrec (n : Graph) (nrec : in_N n)
    : in_N n.
  Proof.
    intros P' PH' P0' Ps'.
    srefine ((equiv_resize_hprop (P' n))^-1
             (nrec (fun A => resize_hprop (P' A)) _ _ _));
      try exact _; cbn.
    - exact (equiv_resize_hprop (P' graph_zero) P0').
    - intros A P'A.
      exact (equiv_resize_hprop (P' (graph_succ A))
                                (Ps' A ((equiv_resize_hprop (P' A))^-1 P'A))).
  Defined.

  Definition N_zero_or_succ (n : N)
    : merely ((n = zero) + { m : N & n = succ m }).
  Proof.
    apply (functor_merely
           (functor_sum (path_N _ _)
                       (functor_sigma (Q := fun m:N => n = succ m) idmap (fun m => path_N _ (succ m))))).
    destruct n as [n nrec]; cbn.
    srefine (resize_nrec n nrec
             (fun n => merely ((n = graph_zero) +
                       {m : N & n = graph_succ m.1})) _ _ _); cbn.
    - apply trm, inl; reflexivity.
    - intros A; apply functor_merely; intros [A0|[m As]]; apply inr.
      + exists zero.
        rewrite A0.
        reflexivity.
      + exists (succ m).
        rewrite As.
        reflexivity.
  Defined.

  Definition pred_in_N (n : Graph) (snrec : in_N (graph_succ n))
    : in_N n.
  Proof.
    refine (merely_rec _ (N_zero_or_succ (graph_succ n ; snrec))).
    intros [H0|[m Hs]].
    - apply pr1_path in H0; cbn in H0.
      destruct (graph_zero_neq_succ H0^).
    - apply pr1_path in Hs.
      apply graph_unsucc_path in Hs.
      apply (transport in_N Hs^).
      exact m.2.
  Defined.

  (* Final Peano axiom: induction *)
  Definition N_propind (P : N -> Type) `{forall n, IsHProp (P n)}
             (P0 : P zero) (Ps : forall n, P n -> P (succ n))
    : forall n, P n.
  Proof.
    intros [n nrec].
    pose (Q := fun m:Graph => forall (mrec : in_N m), P (m;mrec)).
    refine (resize_nrec n nrec Q _ _ _ nrec).
    - intros A; apply trunc_forall.
    - intros zrec.
      refine (transport P _ P0).
      apply ap.
      apply path_ishprop.
    - intros A QA Asrec.
      pose (m := (A ; pred_in_N A Asrec) : N).
      refine (transport P _ (Ps m (QA (pred_in_N A Asrec)))).
      apply path_N; reflexivity.
  Defined.

End AssumeStuff.
End UAPRNat.
