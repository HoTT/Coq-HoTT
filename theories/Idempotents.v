Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Constant.
Require Import Truncations.Core Modalities.Modality.
Require Import Homotopy.IdentitySystems.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Local Set Universe Minimization ToSet.

(** * Idempotents and their splittings *)

(** ** Basic definitions *)

(** *** Retracts *)

(** A *retract* of a type [X] is a type [A] equipped with a pair of morphisms [r : X -> A] and [s : A -> X] such that the composite [r o s] is the identity of [A]. *)

Record RetractOf {X : Type} :=
  { retract_type : Type ;
    retract_retr : X -> retract_type ;
    retract_sect : retract_type -> X ;
    retract_issect : retract_retr o retract_sect == idmap }.

Arguments RetractOf X : clear implicits.

Arguments retract_type / .
Arguments retract_retr / .
Arguments retract_sect / .
Arguments retract_issect / .

(** For example, here is the identity retraction. *)
Definition idmap_retractof (X : Type) : RetractOf X
  := Build_RetractOf X X idmap idmap (fun _ => 1).

(** Retractions can be composed with equivalences on either side. *)
Definition retractof_equiv {X Y : Type} (f : X -> Y) `{feq : IsEquiv _ _ f}
: RetractOf X -> RetractOf Y.
Proof.
  intros [A r s H]; refine (Build_RetractOf Y A (r o f^-1) (f o s) _); intros x.
  exact (ap r (eissect f (s x)) @ H x).
Defined.

Definition retractof_equiv' {X Y : Type} (f : X <~> Y)
: RetractOf X -> RetractOf Y
  := retractof_equiv f.

Definition equiv_retractof {X : Type} (R : RetractOf X)
           {B : Type} (f : retract_type R -> B) `{feq : IsEquiv _ _ f}
: RetractOf X.
Proof.
  destruct R as [A r s H]; refine (Build_RetractOf X B (f o r) (s o f^-1) _); intros x.
  exact (ap f (H (f^-1 x)) @ eisretr f x).
Defined.

Definition equiv_retractof' {X : Type} (R : RetractOf X)
           {B : Type} (f : retract_type R <~> B)
: RetractOf X
  := equiv_retractof R f.

(** A commuting retract of the domain of map induces a retract of its fibers. *)
Definition retractof_hfiber {X Y : Type} (R : RetractOf X) (f : X -> Y)
           (g : retract_type R -> Y) (p : g o retract_retr R == f)
           (y : Y)
: RetractOf (hfiber f y).
Proof.
  destruct R as [A r s H]; simpl in *.
  simple refine (Build_RetractOf (hfiber f y) (hfiber g y) _ _ _).
  - intros [x q].
    exists (r x).
    exact (p x @ q).
  - intros [a q].
    exists (s a).
    exact ((p (s a))^ @ ap g (H a) @ q).
  - intros [a q].
    simple refine (path_sigma' _ _ _).
    + exact (H a).
    + abstract (
        rewrite transport_paths_Fl, !concat_p_pp, concat_pp_V, concat_Vp, concat_1p;
        reflexivity).
Defined.

(** Retraction preserves contractibility **)
Definition contr_retracttype {X : Type} (R : RetractOf X ) (contra : Contr X) : Contr (retract_type R )
  := contr_retract (retract_retr R) (retract_sect R) (retract_issect R).

(** Like any record type, [RetractOf X] is equivalent to a nested sigma-type.  We use a product at one place in the middle, rather than a sigma, to simplify the next proof. *)
Definition issig_retractof (X : Type)
: { A : Type & {r : X -> A & {s : A -> X & r o s == idmap }}}
  <~> RetractOf X.
Proof.
  issig.
Defined.

(* Path spaces of types of retractions *)
Definition PathRetractOf (X : Type) (R' R : RetractOf X)
  := { Ap : retract_type R' <~> retract_type R &
     { rp : Ap o retract_retr R' == retract_retr R &
     { sp : retract_sect R' o Ap^-1 == retract_sect R &
            forall a, ap Ap (retract_issect R' (Ap^-1 a))
                         @ eisretr Ap a
                      = rp (retract_sect R' (Ap^-1 a))
                           @ ap (retract_retr R) (sp a)
                           @ retract_issect R a } } }.

Definition equiv_path_retractof `{ua : Univalence} {X : Type}
           (R' R : RetractOf X)
  : PathRetractOf X R' R <~> R' = R.
Proof.
  revert R' R; apply (equiv_path_issig_contr (issig_retractof X)).
  { intros [A [r [s H]]]; cbn.
    exists equiv_idmap.
    exists (fun x => 1%path).
    exists (fun x => 1%path).
    cbn. exact (fun a => equiv_p1_1q (ap_idmap (H a))). }
  intros [A [r [s H]]]; cbn.
  unfold PathRetractOf.
  contr_sigsig A (equiv_idmap A); cbn.
  contr_sigsig r (fun x:X => idpath (r x)); cbn.
  contr_sigsig s (fun x:A => idpath (s x)); cbn.
  refine (contr_equiv' {K : r o s == idmap & H == K} _).
  apply equiv_functor_sigma_id; intros K.
  apply equiv_functor_forall_id; intros a; cbn.
  apply equiv_concat_lr.
  - refine (concat_p1 _ @ ap_idmap (H a)).
  - symmetry; apply concat_1p.
Defined.

Definition path_retractof `{ua : Univalence} {X : Type} {R' R : RetractOf X}
           Ap rp sp Hp
  : R' = R
  := equiv_path_retractof R' R (Ap;rp;sp;Hp).

(** *** Splittings *)

(** If an endomap [f : X -> X] arises from a retract as [s o r], we say that that retract is a *splitting* of [f]. *)

Definition retract_idem {X : Type} (R : RetractOf X)
: (X -> X)
  := retract_sect R o retract_retr R.

Arguments retract_idem {_} _ / x .

Definition Splitting {X : Type} (f : X -> X)
  := { R : RetractOf X & retract_idem R == f}.

(** For example, here is the canonical splitting of the identity. *)
Definition splitting_idmap (X : Type) : @Splitting X idmap
  := (idmap_retractof X ; fun _ => 1).

(** *** Pre-idempotents *)

(** An "idempotent" is a map that at least "ought" to be splittable.  The naive definition of idempotent, which is correct in set-level mathematics, is a morphism [f : X -> X] such that [forall x, f (f x) = f x].  We will call this a "pre-idempotent". *)

Class IsPreIdempotent {X : Type} (f : X -> X)
  := isidem : forall x, f (f x) = f x.

Arguments isidem {X} f {_} x.

Definition ispreidem_homotopic {X : Type}
           (f : X -> X) `{IsPreIdempotent _ f} {g : X -> X} (p : f == g)
: IsPreIdempotent g.
Proof.
  intros x; refine (_ @ isidem f x @ p x).
  refine (_ @ (p (f x))^).
  apply ap; symmetry; apply p.
Defined.

Arguments ispreidem_homotopic / .

Definition PreIdempotent (X : Type) := { f : X -> X & IsPreIdempotent f }.
Definition preidempotent_pr1 {X : Type} : PreIdempotent X -> X -> X := pr1.
Coercion preidempotent_pr1 : PreIdempotent >-> Funclass.

Global Instance ispreidem_preidem {X : Type} (f : PreIdempotent X)
: IsPreIdempotent f
  := f.2.

(** The identity function has a canonical structure of a pre-idempotent. *)
Global Instance ispreidem_idmap (X : Type) : @IsPreIdempotent X idmap
  := fun _ => 1.

Definition preidem_idmap (X : Type) : PreIdempotent X.
Proof.
  exists idmap; exact _.
Defined.

(** Any pre-idempotent on a set splits. *)
Definition split_preidem_set (X : Type) `{IsHSet X} (f : PreIdempotent X)
: Splitting f.
Proof.
  simple refine (Build_RetractOf X { x : X & f x = x }
                                 (fun x => (f x ; isidem f x)) pr1 _ ; _).
  - intros [x p]; simpl.
    apply path_sigma with p; simpl.
    apply path_ishprop.
  - simpl. intros x; reflexivity.
Defined.

(** Any weakly constant pre-idempotent splits (Escardo) *)
Definition split_preidem_wconst (X : Type) (f : PreIdempotent X)
           `{WeaklyConstant _ _ f}
: Splitting f.
Proof.
  simple refine (Build_RetractOf X (FixedBy f)
                                 (fun x => (f x ; isidem f x)) pr1 _ ; _).
  - intros x; apply path_ishprop.
  - simpl. intros x; reflexivity.
Defined.

(** If [f] is pre-idempotent and [f x = x] is collapsible for all [x], then [f] splits (Escardo). *)
Definition split_preidem_splitsupp (X : Type) (f : PreIdempotent X)
           (ss : forall x, Collapsible (f x = x))
: Splitting f.
Proof.
  simple refine (Build_RetractOf X { x : X & FixedBy (@collapse (f x = x) _) }
                                 _ pr1 _ ; _).
  - intros x; exists (f x); unfold FixedBy.
    exists (collapse (isidem f x)).
    apply wconst.
  - intros [x [p q]]; simpl.
    apply path_sigma with p.
    apply path_ishprop.
  - simpl. intros x; reflexivity.
Defined.

(** Moreover, in this case the section is an embedding. *)
Definition isemb_split_preidem_splitsupp (X : Type) (f : PreIdempotent X)
           (ss : forall x, Collapsible (f x = x))
: IsEmbedding (retract_sect (split_preidem_splitsupp X f ss).1).
Proof.
  apply istruncmap_mapinO_tr; exact _.
Defined.

(** Conversely, if [f] splits with a section that is an embedding, then (it is pre-idempotent and) [f x = x] is collapsible for all [x] (Escardo). *)
Definition splitsupp_split_isemb (X : Type) (f : X -> X) (S : Splitting f)
           `{IsEmbedding (retract_sect S.1)}
: forall x, Collapsible (f x = x).
Proof.
  intros x. destruct S as [[A r s H] K]; simpl in *.
  assert (c1 : f x = x -> { a : A & s a = x }).
  { intros p; exists (r x).
    exact (K x @ p). }
  assert (c2 : { a : A & s a = x } -> f x = x).
  { intros [a q].
    exact ((K x)^ @ ap (s o r) q^ @ ap s (H a) @ q). }
  exists (c2 o c1).
  apply wconst_through_hprop.
Defined.

(** *** Quasi-idempotents *)

(** However, homotopically we may naturally expect to need some coherence on the witness [isidem] of idempotency.  And indeed, in homotopy theory there are pre-idempotents which do not split; we will see an example later on.  We expect a "coherent idempotent" to involve infinitely many data.  However, Lemma 7.3.5.14 of *Higher Algebra* suggests that for an idempotent to admit *some* coherentification, hence also a splitting, it suffices to have *one* additional datum.  By modifying the construction given there, we can show similarly in type theory that any idempotent satisfying an additional coherence datum splits.  We will call a pre-idempotent with this one additional datum a "quasi-idempotent", since it is related to a fully coherent idempotent similarly to the way having a "quasi-inverse" is related to being a coherent equivalence. *)

Class IsQuasiIdempotent {X : Type} (f : X -> X) `{IsPreIdempotent _ f}
  := isidem2 : forall x, ap f (isidem f x) = isidem f (f x).

Arguments isidem2 {X} f {_ _} x.

Definition isqidem_homotopic {X : Type}
           (f : X -> X) `{IsQuasiIdempotent _ f} {g : X -> X} (p : f == g)
: @IsQuasiIdempotent X g (ispreidem_homotopic f p).
Proof.
  intros x; unfold isidem; simpl.
  Open Scope long_path_scope.
  rewrite (concat_Ap (fun x => (p x)^) (p x)^).
  rewrite !ap_pp, !concat_pp_p; apply whiskerL.
  rewrite !concat_p_pp; apply moveL_pM.
  rewrite (concat_pA_p (fun x => (p x)^) (p x)).
  rewrite (concat_pA_p (fun x => (p x)^) (isidem _ x)).
  rewrite (concat_Ap (fun x => (p x)^) (ap f (p x)^)).
  rewrite !concat_pp_p; apply whiskerL.
  rewrite !ap_V; apply moveR_Vp.
  rewrite <- ap_compose.
  rewrite isidem2; try exact _.
  symmetry; refine (concat_Ap (isidem f) (p x)).
  Close Scope long_path_scope.
Qed.

Definition QuasiIdempotent (X : Type) := { f : PreIdempotent X & IsQuasiIdempotent f }.
Definition quasiidempotent_pr1 {X : Type} : QuasiIdempotent X -> X -> X := pr1.
Coercion quasiidempotent_pr1 : QuasiIdempotent >-> Funclass.

Global Instance isqidem_qidem {X : Type} (f : QuasiIdempotent X)
: IsQuasiIdempotent f
  := f.2.

(** The identity function has a canonical structure of a quasi-idempotent. *)
Global Instance isqidem_idmap (X : Type) : @IsQuasiIdempotent X idmap _
  := fun _ => 1.

Definition qidem_idmap (X : Type) : QuasiIdempotent X.
Proof.
  exists (preidem_idmap X); exact _.
Defined.

(** We have made [IsPreIdempotent] and [IsQuasiIdempotent] typeclasses as an experiment.  It could be that they should revert back to [Definitions]. *)

(** ** Split morphisms are quasi-idempotent *)

(** First we show that given a retract, the composite [s o r] is quasi-idempotent. *)

Global Instance ispreidem_retract {X : Type} (R : RetractOf X)
: IsPreIdempotent (retract_idem R).
Proof.
  exact (fun x => ap (retract_sect R) (retract_issect R (retract_retr R x))).
Defined.

Definition preidem_retract {X : Type} (R : RetractOf X)
: PreIdempotent X
:= (retract_idem R ; ispreidem_retract R).

Arguments ispreidem_retract / .
Arguments preidem_retract / .

Global Instance isqidem_retract {X : Type} (R : RetractOf X)
: IsQuasiIdempotent (retract_idem R).
Proof.
  destruct R as [A r s H]; intros x; unfold isidem; simpl.
  refine ((ap_compose _ _ _) @ _).
  apply ap.
  refine ((ap_compose _ _ _)^ @ _).
  refine (cancelR _ _ (H (r x)) _).
  refine (concat_A1p H (H (r x))).
Defined.

Definition qidem_retract {X : Type} (R : RetractOf X)
: QuasiIdempotent X
:= (preidem_retract R ; isqidem_retract R).

(** In particular, it follows that any split function is quasi-idempotent. *)

Global Instance ispreidem_split {X : Type} (f : X -> X) (S : Splitting f)
: IsPreIdempotent f.
Proof.
  destruct S as [R p].
  refine (ispreidem_homotopic _ p); exact _.
Defined.

Arguments ispreidem_split / .

Global Instance isqidem_split {X : Type} (f : X -> X) (S : Splitting f)
: @IsQuasiIdempotent X f (ispreidem_split f S).
Proof.
  destruct S as [R p].
  refine (isqidem_homotopic _ p); exact _.
Defined.

Arguments isqidem_split / .

(** ** Quasi-idempotents split *)

(** We now show the converse, that every quasi-idempotent splits. *)

Section Splitting.
  (** We need funext because our construction will involve a sequential limit.  We could probably also use a HIT sequential colimit, which is more like what Lurie does.  (Note that, like an interval type, HIT sequential colimits probably imply funext, so our construction uses strictly weaker hypotheses.) *)
  Context `{Funext}.
  Context {X : Type} (f : X -> X).
  Context `{IsQuasiIdempotent _ f}.

  Let I := isidem f.
  Let J : forall x, ap f (I x) = I (f x)
    := isidem2 f.

  (** The splitting will be the sequential limit of the sequence [... -> X -> X -> X]. *)
  Definition split_idem : Type
    := { a : nat -> X & forall n, f (a n.+1) = a n }.

  Definition split_idem_pr1 : split_idem -> (nat -> X)
    := pr1.
  Coercion split_idem_pr1 : split_idem >-> Funclass.
  Arguments split_idem_pr1 / .

  (** The section, retraction, and the fact that the composite in one direction is [f] are easy. *)

  Definition split_idem_sect : split_idem -> X
    := fun a => a 0.
  Arguments split_idem_sect / .

  Definition split_idem_retr : X -> split_idem.
  Proof.
    intros x.
    exists (fun n => f x).
    exact (fun n => I x).
  Defined.
  Arguments split_idem_retr / .

  Definition split_idem_splits (x : X)
  : split_idem_sect (split_idem_retr x) = f x
    := 1.

  (** What remains is to show that the composite in the other direction is the identity.  We begin by showing how to construct paths in [split_idem]. *)

  Definition path_split_idem {a a' : split_idem}
    (p : a.1 == a'.1)
    (q : forall n, a.2 n @ p n = ap f (p n.+1) @ a'.2 n)
  : a = a'.
  Proof.
    simple refine (path_sigma' _ _ _).
    - apply path_arrow; intros n.
      exact (p n).
    - apply path_forall; intros n.
      abstract (
          rewrite transport_forall_constant;
          rewrite transport_paths_FlFr;
          rewrite ap_apply_l, ap10_path_arrow;
          rewrite (ap_compose (fun b => b n.+1) (fun x => f x) _);
          rewrite ap_apply_l, ap10_path_arrow;
          rewrite concat_pp_p;
          apply moveR_Vp; by symmetry ).
  Defined.

  (** And we verify how those paths compute under [split_idem_sect]. *)
  Definition sect_path_split_idem {a a' : split_idem}
    (p : a.1 == a'.1)
    (q : forall n, a.2 n @ p n = ap f (p n.+1) @ a'.2 n)
  : ap split_idem_sect (path_split_idem p q) = p 0.
  Proof.
    change (ap ((fun b => b 0) o pr1) (path_split_idem p q) = p 0).
    refine (ap_compose pr1 (fun b => b 0) _ @ _).
    refine (ap (ap (fun b => b 0)) (pr1_path_sigma _ _) @ _).
    refine (ap_apply_l _ 0 @ _).
    apply ap10_path_arrow.
  Defined.

  (** Next we show that every element of [split_idem] can be nudged to an equivalent one in which all the elements of [X] occurring are double applications of [f]. *)

  Local Definition nudge (a : split_idem) : split_idem.
  Proof.
    exists (fun n => f (f (a (n.+1)))).
    exact (fun n => ap f (ap f (a.2 n.+1))).
  Defined.

  Local Definition nudge_eq a : nudge a = a.
  Proof.
    transparent assert (a' : split_idem).
    { exists (fun n => f (a (n.+1))).
      exact (fun n => ap f (a.2 n.+1)). }
    transitivity a'; simple refine (path_split_idem _ _); intros n; simpl.
    - exact (I (a n.+1)).
    - exact ((ap_compose f f _ @@ 1)^
               @ concat_Ap I (a.2 n.+1)
               @ (J _ @@ 1)^).
    - exact (a.2 n).
    - reflexivity.
  Defined.

  (** Now we're ready to prove the final condition.  We prove the two arguments of [path_split_idem] separately, in order to make the first one transparent and the second opaque. *)

  Local Definition split_idem_issect_part1 (a : split_idem) (n : nat)
  : f (f (a n.+1)) = f (a 0).
  Proof.
    induction n as [|n IH].
    - exact (ap f (a.2 0)).
    - exact (ap f (a.2 n.+1) @ (I (a n.+1))^ @ IH).
  Defined.

  Local Definition split_idem_issect_part2 (a : split_idem) (n : nat)
  : ap f (ap f (a.2 n.+1)) @ split_idem_issect_part1 a n =
    ap f ((ap f (a.2 n.+1) @ (I (a.1 n.+1))^) @ split_idem_issect_part1 a n) @ I (a.1 0).
  Proof.
    induction n as [|n IH]; simpl.
    Open Scope long_path_scope.
    - rewrite !ap_pp, ap_V, !concat_pp_p.
      apply whiskerL, moveL_Vp.
      rewrite J.
      rewrite <- ap_compose; symmetry; apply (concat_Ap I).
    - rewrite ap_pp.
      refine (_ @ (1 @@ IH) @ concat_p_pp _ _ _).
      rewrite !ap_pp, !concat_p_pp, ap_V.
      rewrite J.
      rewrite <- !ap_compose.
      refine ((concat_pA_p (fun x => (I x)^) _ _) @@ 1).
    Close Scope long_path_scope.
  Qed.

  Definition split_idem_issect (a : split_idem)
  : split_idem_retr (split_idem_sect a) = a.
  Proof.
    refine (_ @ nudge_eq a); symmetry.
    simple refine (path_split_idem _ _).
    - exact (split_idem_issect_part1 a).
    - exact (split_idem_issect_part2 a).
  Defined.

  Definition split_idem_retract : RetractOf X
    := Build_RetractOf
         X split_idem split_idem_retr split_idem_sect split_idem_issect.

  Definition split_idem_split : Splitting f
    := (split_idem_retract ; split_idem_splits).

  (** We end this section by showing that we can recover the witness [I] of pre-idempotence from the splitting. *)
  Definition split_idem_preidem (x : X)
  : ap split_idem_sect (split_idem_issect (split_idem_retr x))
    = I x.
  Proof.
    unfold split_idem_issect, nudge_eq.
    repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idem; simpl).
    apply moveR_Vp, whiskerR; symmetry; apply J.
  Qed.

  (** However, the particular witness [J] of quasi-idempotence can *not* in general be recovered from the splitting; we will mention a counterexample below.  This is analogous to how [eissect] and [eisretr] cannot both be recovered after [isequiv_adjointify]; one of them has to be modified. *)

End Splitting.

Definition split_idem_retract' `{fs : Funext} {X : Type}
: QuasiIdempotent X -> RetractOf X
:= fun f => split_idem_retract f.

Definition split_idem_split' `{fs : Funext} {X : Type}
           (f : QuasiIdempotent X)
: Splitting f
:= split_idem_split f.

(** ** Splitting already-split idempotents *)

(** In the other direction, suppose we are given a retract, we deduce from this a quasi-idempotent, and then split it by the above construction.  We will show that the resulting retract is equivalent to the original one, so that [RetractOf X] is itelf a retract of [QuasiIdempotent X]. *)

Section AlreadySplit.
  Context `{fs : Funext}.

  Context {X : Type} (R : RetractOf X).
  Let A := retract_type R.
  Let r := retract_retr R.
  Let s := retract_sect R.
  Let H := retract_issect R.

  (** We begin by constructing an equivalence between [split_idem (s o r)] and [A].  We want to make this equivalence transparent so that we can reason about it later.  In fact, we want to reason not only about the equivalence function and its inverse, but the section and retraction homotopies!  Therefore, instead of using [equiv_adjointify] we will give the coherence proof explicitly, so that we can control these homotopies.  However, we can (and should) make the coherence proof itself opaque.  Thus, we prove it first, and end it with [Qed].  *)
  Lemma equiv_split_idem_retract_isadj (a : split_idem (s o r))
  : H (r (s (r (split_idem_sect (s o r) a)))) @
      H (r (split_idem_sect (s o r) a)) =
    ap (r o split_idem_sect (s o r))
       (ap (split_idem_retr (s o r))
           (1 @
              ap (split_idem_sect (s o r))
              (split_idem_issect (s o r) a)) @
           split_idem_issect (s o r) a).
  Proof.
    rewrite ap_pp.
    rewrite <- ap_compose; simpl.
    rewrite concat_1p.
    rewrite <- (ap_compose (split_idem_sect (s o r)) (r o s o r)
                           (split_idem_issect (s o r) a)).
    rewrite (ap_compose _ (r o s o r) (split_idem_issect (s o r) a)).
    rewrite (ap_compose _ r (split_idem_issect (s o r) a)).
    unfold split_idem_issect, nudge_eq;
      repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idem; simpl).
    unfold isidem; fold r s H.
    rewrite !concat_pp_p.
    rewrite <- !ap_compose.
    rewrite <- (ap_compose (s o r) r).
    rewrite <- (ap_compose (s o r) (r o s o r)).
    rewrite (concat_p_Vp (ap (r o s o r) (a.2 0))).
    rewrite_moveL_Vp_p.
    rewrite (ap_compose (r o s o r) (r o s) (a.2 0)).
    rewrite (concat_A1p H (ap (r o s o r) (a.2 0))).
    rewrite (ap_compose r (r o s) (a.2 0)).
    rewrite (concat_pA1_p H (ap r (a.2 0))).
    apply whiskerR.
    refine (cancelR _ _ (H (r (a.1 1%nat))) _).
    rewrite (concat_pA1_p H (H (r (a 1%nat)))).
    rewrite !concat_pp_p; symmetry; refine (_ @ concat_pp_p _ _ _).
    exact (concat_A1p (fun x => H (r (s x)) @ H x) (H (r (a 1%nat)))).
  Qed.

  (** Now we can construct the desired equivalence. *)
  Definition equiv_split_idem_retract
  : split_idem (s o r) <~> A.
  Proof.
    simple refine (Build_Equiv _ _ (r o split_idem_sect (s o r))
              (Build_IsEquiv _ _ _ (split_idem_retr (s o r) o s) _ _ _)).
    - intros a; simpl.
      refine (H _ @ H _).
    - intros a; simpl.
      refine (_ @ split_idem_issect (s o r) a).
      apply ap.
      refine ((split_idem_splits (s o r) _)^ @ _).
      apply ap, split_idem_issect; exact _.
    - intros a; simpl; apply equiv_split_idem_retract_isadj.
  Defined.

  (** It is easy to show that this equivalence respects the section and the retraction. *)

  Definition equiv_split_idem_retract_retr (x : X)
  : equiv_split_idem_retract (split_idem_retr (s o r) x) = r x
    := H (r x).

  Definition equiv_split_idem_retract_sect (a : A)
  : split_idem_sect (s o r) (equiv_split_idem_retract^-1 a) = s a
    := ap s (H a).

  (** Less trivial is to show that it respects the retract homotopy. *)

  Definition equiv_split_idem_retract_issect (a : A)
  : ap equiv_split_idem_retract
       (split_idem_issect (s o r) (equiv_split_idem_retract^-1 a))
       @ eisretr equiv_split_idem_retract a
    = equiv_split_idem_retract_retr
        (split_idem_sect (s o r) (equiv_split_idem_retract^-1 a))
        @ ap r (equiv_split_idem_retract_sect a)
        @ H a.
  Proof.
    simpl.
    unfold equiv_split_idem_retract_retr, equiv_split_idem_retract_sect.
    rewrite ap_compose.
    unfold split_idem_issect, nudge_eq.
    repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idem; simpl).
    unfold isidem; fold A r s H.
    Open Scope long_path_scope.
    rewrite !concat_pp_p; apply moveR_Vp; rewrite !concat_p_pp.
    do 4 rewrite <- ap_compose.
    (** For some reason this last one needs help. *)
    rewrite <- (ap_compose (s o r o s) r (H (r (s a)))).
    rewrite <- (ap_pp (r o s) _ _).
    rewrite <- (concat_A1p H (H (r (s a)))).
    rewrite ap_pp.
    rewrite <- (ap_compose (r o s) (r o s) _).
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    rewrite (concat_A1p H (H (r (s a)))).
    rewrite !concat_pp_p; apply whiskerL.
    symmetry; refine (concat_A1p H (H a)).
    Close Scope long_path_scope.
  Qed.

  (** We will also show that it respects the homotopy to the split map.  It's unclear whether this has any use. *)
  Definition equiv_split_idem_retract_splits (x : X)
  : split_idem_splits (s o r) x
    = ap (split_idem_sect (s o r))
         (eissect equiv_split_idem_retract
                  (split_idem_retr (s o r) x))^
      @ equiv_split_idem_retract_sect
        (equiv_split_idem_retract (split_idem_retr (s o r) x))
        @ ap s (equiv_split_idem_retract_retr x).
  Proof.
    simpl.
    unfold equiv_split_idem_retract_retr, equiv_split_idem_retract_sect, split_idem_splits.
    rewrite concat_1p, concat_pp_p, ap_V; apply moveL_Vp; rewrite concat_p1.
    (** Brace yourself. *)
    unfold split_idem_issect, nudge_eq.
    repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idem; simpl).
    (** Whew, that's not so bad. *)
    unfold isidem; fold A r s H.
    Open Scope long_path_scope.
    rewrite !concat_p_pp.
    rewrite <- !ap_compose; simpl.
    apply whiskerR.
    refine (_ @ (concat_1p _)); apply whiskerR.
    apply moveR_pV; rewrite concat_1p, concat_pp_p; apply moveR_Vp.
    rewrite <- (ap_compose (s o r o s) (s o r)).
    rewrite (ap_compose (r o s) s _).
    rewrite (ap_compose (r o s) s _).
    rewrite (ap_compose (r o s o r o s) s _).
    rewrite <- !ap_pp; apply ap.
    refine (cancelR _ _ (H (r x)) _).
    rewrite (concat_pA1_p H (H (r x)) _).
    rewrite (concat_pA1_p H (H (r x)) _).
    refine ((concat_A1p H (H (r (s (r x)))) @@ 1) @ _).
    rewrite (ap_compose (r o s) (r o s) _).
    rewrite (concat_A1p H (ap (r o s) (H (r x)))).
    rewrite !concat_pp_p; apply whiskerL.
    symmetry; refine (concat_A1p H (H (r x))).
    Close Scope long_path_scope.
  Qed.

End AlreadySplit.

(** Using these facts, we can show that [RetractOf X] is a retract of [QuasiIdempotent X]. *)

Section RetractOfRetracts.
  Context `{ua : Univalence} {X : Type}.

  Definition retract_retractof_qidem : RetractOf (QuasiIdempotent X).
  Proof.
    refine (Build_RetractOf (QuasiIdempotent X)
                            (RetractOf X)
                            split_idem_retract'
                            qidem_retract _).
    intros R.
    exact (@path_retractof _ _
             (split_idem_retract' (qidem_retract R)) R
             (equiv_split_idem_retract R)
             (equiv_split_idem_retract_retr R)
             (equiv_split_idem_retract_sect R)
             (equiv_split_idem_retract_issect R)).
  Defined.

  (** We have a similar result for splittings of a fixed map [f].  *)
  Definition splitting_retractof_isqidem (f : X -> X)
  : RetractOf { I : IsPreIdempotent f & IsQuasiIdempotent f }.
  Proof.
    simple refine (@equiv_retractof'
              _ (@retractof_equiv'
                   (hfiber quasiidempotent_pr1 f) _ _
                   (retractof_hfiber
                      retract_retractof_qidem quasiidempotent_pr1 retract_idem
                      (fun _ => 1) f))
              (Splitting f) _).
    - refine ((hfiber_fibration f
                  (fun g => { I : IsPreIdempotent g & @IsQuasiIdempotent _ g I }))^-1 oE _).
      unfold hfiber.
      refine (equiv_functor_sigma' (equiv_sigma_assoc _ _)^-1 (fun a => _)); simpl.
      destruct a as [[g I] J]; unfold quasiidempotent_pr1; simpl.
      apply equiv_idmap.
    - simpl.  unfold hfiber, Splitting.
      refine (equiv_functor_sigma_id _);
        intros R; simpl.
      apply equiv_ap10.
  Defined.

  (** And also for splittings of a fixed map that also induce a given witness of pre-idempotency. *)
  Definition Splitting_PreIdempotent (f : PreIdempotent X)
  := { S : Splitting f &
       forall x, ap f (S.2 x)^
                 @ (S.2 (retract_idem S.1 x))^
                 @ ap (retract_sect S.1) (retract_issect S.1 (retract_retr S.1 x))
                 @ S.2 x
                 = (isidem f x) }.

  Definition splitting_preidem_retractof_qidem (f : PreIdempotent X)
  : RetractOf (IsQuasiIdempotent f).
  Proof.
    simple refine (@equiv_retractof'
              _ (@retractof_equiv'
                   (hfiber (@pr1 _ (fun fi => @IsQuasiIdempotent _ fi.1 fi.2)) f) _ _
                   (retractof_hfiber
                      retract_retractof_qidem pr1 preidem_retract
                      _ f))
              (Splitting_PreIdempotent f) _).
    - symmetry; refine (hfiber_fibration f _).
    - intros [[g I] J]; simpl.
      refine (path_sigma' _ 1 _); simpl.
      apply path_forall; intros x; apply split_idem_preidem.
    - simpl; unfold hfiber, Splitting.
      refine (equiv_sigma_assoc _ _ oE _).
      apply equiv_functor_sigma_id; intros R; simpl.
      refine (_ oE (equiv_path_sigma _ _ _)^-1); simpl.
      refine (equiv_functor_sigma' (equiv_ap10 _ _) _); intros H; simpl.
      destruct f as [f I]; simpl in *.
      destruct H; simpl.
      refine (_ oE (equiv_path_forall _ _)^-1);
        unfold pointwise_paths.
      apply equiv_functor_forall_id; intros x; simpl.
      unfold isidem.
      apply equiv_concat_l.
      refine (concat_p1 _ @ concat_1p _).
  Defined.

End RetractOfRetracts.

(** ** Fully coherent idempotents *)

(** This gives us a way to define fully coherent idempotents.  By Corollary 4.4.5.14 of *Higher Topos Theory*, if we assume univalence then [RetractOf X] has the correct homotopy type of the type of fully coherent idempotents on [X].  However, its defect is that it raises the universe level.  But now that we've shown that [RetractOf X] is a retract of the type [QuasiIdempotent X], which is of the same size as [X], we can obtain an equivalent type by splitting the resulting idempotent on [QuasiIdempotent X].

For convenience, we instead split the idempotent on splittings of a fixed map [f], and then sum them up to obtain the type of idempotents. *)

Section CoherentIdempotents.
  Context {ua : Univalence}.

  Class IsIdempotent {X : Type} (f : X -> X)
    := is_coherent_idem : split_idem (retract_idem (splitting_retractof_isqidem f)).

  Definition Build_IsIdempotent {X : Type} (f : X -> X)
  : Splitting f -> IsIdempotent f
    := (equiv_split_idem_retract (splitting_retractof_isqidem f))^-1.

  Definition isidem_isqidem {X : Type} (f : X -> X) `{IsQuasiIdempotent _ f}
  : IsIdempotent f
    := Build_IsIdempotent f (split_idem_split f).

  Global Instance ispreidem_isidem {X : Type} (f : X -> X)
         `{IsIdempotent _ f} : IsPreIdempotent f.
  Proof.
    refine (split_idem_sect (retract_idem (splitting_retractof_isqidem f)) _).1.
    assumption.
  Defined.

  Global Instance isqidem_isidem {X : Type} (f : X -> X)
         `{IsIdempotent _ f} : @IsQuasiIdempotent X f (ispreidem_isidem f).
  Proof.
    refine (split_idem_sect (retract_idem (splitting_retractof_isqidem f)) _).2.
  Defined.

  Definition Idempotent (X : Type) := { f : X -> X & IsIdempotent f }.

  Definition idempotent_pr1 {X : Type} : Idempotent X -> (X -> X) := pr1.
  Coercion idempotent_pr1 : Idempotent >-> Funclass.

  Global Instance isidem_idem (X : Type) (f : Idempotent X) : IsIdempotent f
    := f.2.

  (** The above definitions depend on [Univalence].  Technically this is the case by their construction, since they are a splitting of a map that we only know to be idempotent in the presence of univalence.  This map could be defined, and hence "split", without univalence; but also only with univalence do we know that they have the right homotopy type.  Thus univalence is used in two places: concluding (meta-theoretically) from HTT 4.4.5.14 that [RetractOf X] has the right homotopy type, and showing (in the next lemma) that it is equivalent to [Idempotent X].  In the absence of univalence, we don't currently have *any* provably-correct definition of the type of coherent idempotents; it ought to involve an infinite tower of coherences as defined in HTT section 4.4.5.   However, there may be some Yoneda-like meta-theoretic argument which would imply that the above-defined types do have the correct homotopy type without univalence (though almost certainly not without funext). *)

  Definition equiv_idempotent_retractof (X : Type)
  : Idempotent X <~> RetractOf X.
  Proof.
    transitivity ({ f : X -> X & Splitting f }).
    - unfold Idempotent.
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros f; simpl.
      refine (equiv_split_idem_retract (splitting_retractof_isqidem f)).
    - unfold Splitting.
      refine (_ oE equiv_sigma_symm _).
      apply equiv_sigma_contr; intros R.
      apply contr_basedhomotopy.
  Defined.

  (** For instance, here is the standard coherent idempotent structure on the identity map. *)
  Global Instance isidem_idmap (X : Type@{i})
  : @IsIdempotent@{i i j} X idmap
    := Build_IsIdempotent idmap (splitting_idmap X).

  Definition idem_idmap (X : Type@{i}) : Idempotent@{i i j} X
  := (idmap ; isidem_idmap X).
End CoherentIdempotents.

(** ** Quasi-idempotents need not be fully coherent *)

(** We have shown that every quasi-idempotent can be "coherentified" into a fully coherent idempotent, analogously to how every quasi-inverse can be coherentified into an equivalence.  However, just as for quasi-inverses, not every witness to quasi-idempotency *is itself* coherent.  This is in contrast to a witness of pre-idempotency, which (if it extends to a quasi-idempotent) can itself be extended to a coherent idempotent; this is roughly the content of [split_idem_preidem] and [splitting_preidem_retractof_qidem].

  The key step in showing this is to observe that when [f] is the identity, the retract type [Splitting_PreIdempotent f] of [splitting_preidem_retractof_qidem] is equivalent to the type of types-equivalent-to-[X], and hence contractible. *)

Definition contr_splitting_preidem_idmap {ua : Univalence} (X : Type)
: Contr (Splitting_PreIdempotent (preidem_idmap X)).
Proof.
  refine (contr_equiv' {Y : Type & X <~> Y} _).
  transitivity { S : Splitting (preidem_idmap X) &
                     forall x : X, (retract_issect S.1) (retract_retr S.1 x) = ap (retract_retr S.1) (S.2 x) }.
  1:make_equiv.
  apply equiv_functor_sigma_id; intros [[Y r s eta] ep]; cbn in *.
  apply equiv_functor_forall_id; intros x.
  unfold ispreidem_idmap; simpl.
  rewrite ap_idmap, !concat_pp_p.
  refine (equiv_moveR_Vp _ _ _ oE _).
  rewrite concat_p1, concat_p_pp.
  refine (equiv_concat_r (concat_1p _) _ oE _).
  refine (equiv_whiskerR _ _ _ oE _).
  refine (equiv_moveR_Vp _ _ _ oE _).
  rewrite concat_p1.
  pose (isequiv_adjointify s r ep eta).
  refine (_ oE equiv_ap (ap s) _ _).
  apply equiv_concat_r.
  refine (cancelR _ _ (ep x) _).
  rewrite <- ap_compose.
  refine (concat_A1p ep (ep x)).
Qed.

(** Therefore, there is a unique coherentification of the canonical witness [preidem_idmap] of pre-idempotency for the identity.  Hence, to show that not every quasi-idempotent is coherent, it suffices to give a witness of quasi-idempotency extending [preidem_idmap] which is nontrivial (i.e. not equal to [qidem_idmap]).  Such a witness is exactly an element of the 2-center, and we know that some types such as [BAut (BAut Bool)] have nontrivial 2-centers.  In [Spaces.BAut.Bool.IncoherentIdempotent] we use this to construct an explicit counterexample. *)


(** ** A pre-idempotent that is not quasi-idempotent *)

(** We can also give a specific example of a pre-idempotent that does not split, hence is not coherentifiable and not even quasi-idempotent.  The construction is inspired by Warning 1.2.4.8 in *Higher Algebra*, and can be found in [Spaces.BAut.Cantor]. *)
