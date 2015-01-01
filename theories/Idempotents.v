(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import Fibrations UnivalenceImpliesFunext.
Require Import hit.Truncations.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

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
  refine (Build_RetractOf (hfiber f y) (hfiber g y) _ _ _).
  - intros [x q].
    exists (r x).
    exact (p x @ q).
  - intros [a q].
    exists (s a).
    exact ((p (s a))^ @ ap g (H a) @ q).
  - intros [a q].
    refine (path_sigma' _ _ _).
    + exact (H a).
    + abstract (
        rewrite transport_paths_Fl, !concat_p_pp, concat_pp_V, concat_Vp, concat_1p;
        reflexivity).
Defined.

(** Like any record type, [RetractOf X] is equivalent to a nested sigma-type.  We use a product at one place in the middle, rather than a sigma, to simplify the next proof. *)
Definition issig_retractof (X : Type)
: { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}
  <~> RetractOf X.
Proof.
  refine (equiv_compose' (B := {A:Type & {r:X->A & {s:A->X & r o s == idmap}}}) _ _).
  - issig (Build_RetractOf X) (@retract_type X) (@retract_retr X) (@retract_sect X) (@retract_issect X).
  - refine (equiv_functor_sigma' (equiv_idmap _) _); intros A.
    symmetry.
    exact (equiv_sigma_prod (fun (rs:(X->A)*(A->X)) => fst rs o snd rs == idmap)).
Defined.

(** Using this equivalence, we can show how to construct paths between retracts. *)
Definition path_retractof `{ua : Univalence} {X : Type}
           {R R' : RetractOf X}
           (Ap : retract_type R' <~> retract_type R)
           (rp : Ap o retract_retr R' == retract_retr R)
           (sp : retract_sect R' o Ap^-1 == retract_sect R)
           (Hp : forall a, ap Ap (retract_issect R' (Ap^-1 a))
                           @ eisretr Ap a
                           = rp (retract_sect R' (Ap^-1 a))
                             @ ap (retract_retr R) (sp a)
                             @ retract_issect R a)
: R' = R.
Proof.
  destruct R as [A r s H]; destruct R' as [A' r' s' H']; simpl in *.
  refine (@ap _ _ (issig_retractof X) (A';((r',s');H')) (A;((r,s);H)) _).
  (** The first few components are pretty straightforward. *)
  refine (path_sigma' _ _ _).
  { apply path_universe_uncurried.
    exact Ap. }
  refine (transport_sigma _ _ @ _).
  refine (path_sigma' _ _ _); simpl.
  { refine (transport_prod _ _ @ _).
    apply path_prod; simpl.
    - apply path_arrow; intros x.
      refine (transport_arrow_fromconst _ _ _ @ _).
      refine (transport_path_universe_uncurried _ _ @ _).
      apply rp.
    - apply path_arrow; intros a.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (_ @ sp a); simpl; apply ap.
      refine (transport_path_universe_V_uncurried Ap a). }
  (** This looks messy, but we can start out with some straightforward path computation. *)
  apply path_forall; intros a.
  unfold pointwise_paths.
  rewrite transport_forall_constant; simpl.
  rewrite transport_paths_Fl; simpl.
  apply moveR_Vp.
  rewrite ap_pp, concat_pp_p.
  apply moveL_Mp.
  (** Now we break it in half at something we understand better. *)
  transitivity (transport_arrow_fromconst (path_universe_uncurried Ap) r'
                 (transport (fun Z => Z -> X) (path_universe_uncurried Ap) s' a)
                @ ap (transport idmap (path_universe_uncurried Ap) o r')
                     (transport_arrow_toconst (path_universe_uncurried Ap) s' a)
                @ ap _ (H' _)
                @ transport_pV idmap (path_universe_uncurried Ap) a).
  - (** In this half, we can just do path induction. *)
    generalize (path_universe_uncurried Ap).
    intros p; destruct p; simpl.
    rewrite !concat_1p.
    symmetry; unfold transport. rewrite ap_idmap. cbn.
    apply concat_p1.
  - (** This half is trickier because [transport_path_universe] and friends don't simplify under path induction.  We start with some more path computation. *)
    rewrite (ap_apply_FlFr _ (fun rs b => fst rs b) (fun rs => snd rs a)).
    rewrite (ap_compose (fun (rs:(X->A)*(A->X)) => snd rs)
                        (fun (s:A->X) => s a)).
    rewrite ap_snd_path_prod.
    rewrite (ap_compose (fun (rs:(X->A)*(A->X)) => fst rs)
                        (fun (r:X->A) => fun b => r b)).
    rewrite ap_fst_path_prod.
    rewrite ap_apply_l, ap10_path_arrow.
    rewrite ap11_is_ap10_ap01; simpl.
    rewrite ap_idmap.
    rewrite ap10_path_arrow; simpl.
    (** Now we can start applying naturality and peeling things off. *)
    Open Scope long_path_scope.
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    rewrite <- (concat_pA_p rp).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pA_p rp).
    (** We can use the hypothesis [Hp]. *)
    specialize (Hp a).
    rewrite concat_pp_p in Hp.
    rewrite !concat_pp_p, <- Hp, !concat_p_pp. clear Hp.
    (** More naturality and peeling-off *)
    rewrite (ap_compose r' Ap).
    rewrite !ap_pp, !concat_p_pp.
    rewrite <- (ap_compose r' Ap).
    rewrite <- (concat_Ap (fun x => transport_path_universe_uncurried Ap (r' x))).
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    rewrite <- (ap_p_pp Ap).
    rewrite <- (ap_compose s' r').
    rewrite (concat_A1p H').
    rewrite ap_pp, concat_p_pp.
    rewrite <- (concat_Ap (transport_path_universe_uncurried Ap)).
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    (** And what's left is just the odd-looking lemma [transport_path_universe_pV]. *)
    symmetry; apply transport_path_universe_pV.
    Close Scope long_path_scope.
Qed.

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

Definition ispreidem_homotopic {X : Type}
           (f : X -> X) `{IsPreIdempotent _ f} {g : X -> X} (p : f == g)
: IsPreIdempotent g.
Proof.
  intros x; refine (_ @ isidem x @ p x).
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

(** *** Quasi-idempotents *)

(** However, homotopically we may naturally expect to need some coherence on the witness [isidem] of idempotency.  And indeed, in homotopy theory there are pre-idempotents which do not split; we will see an example later on.  We expect a "coherent idempotent" to involve infinitely many data.  However, Lemma 7.3.5.14 of *Higher Algebra* suggests that for an idempotent to admit *some* coherentification, hence also a splitting, it suffices to have *one* additional datum.  By modifying the construction given there, we can show similarly in type theory that any idempotent satisfying an additional coherence datum splits.  We will call a pre-idempotent with this one additional datum a "quasi-idempotent", since it is related to a fully coherent idempotent similarly to the way having a "quasi-inverse" is related to being a coherent equivalence. *)

Class IsQuasiIdempotent {X : Type} (f : X -> X) `{IsPreIdempotent _ f}
  := isidem2 : forall x, ap f (isidem x) = isidem (f x).

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
  rewrite (concat_pA_p (fun x => (p x)^) (isidem x)).
  rewrite (concat_Ap (fun x => (p x)^) (ap f (p x)^)).
  rewrite !concat_pp_p; apply whiskerL.
  rewrite !ap_V; apply moveR_Vp.
  rewrite <- ap_compose.
  rewrite isidem2.
  symmetry; refine (concat_Ap (@isidem X f _) (p x)).
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

Global Instance preidem_retract {X : Type} (R : RetractOf X)
: IsPreIdempotent (retract_idem R).
Proof.
  exact (fun x => ap (retract_sect R) (retract_issect R (retract_retr R x))).
Defined.

Definition preidem_retract' {X : Type} (R : RetractOf X)
: PreIdempotent X
:= (retract_idem R ; preidem_retract R).

Arguments preidem_retract / .
Arguments preidem_retract' / .

Global Instance qidem_retract {X : Type} (R : RetractOf X)
: IsQuasiIdempotent (retract_idem R).
Proof.
  destruct R as [A r s H]; intros x; unfold isidem; simpl.
  refine ((ap_compose _ _ _) @ _).
  apply ap.
  refine ((ap_compose _ _ _)^ @ _).
  refine (cancelR _ _ (H (r x)) _).
  refine (concat_A1p H (H (r x))).
Defined.

Definition qidem_retract' {X : Type} (R : RetractOf X)
: QuasiIdempotent X
:= (preidem_retract' R ; qidem_retract R).

(** In particular, it follows that any split function is quasi-idempotent. *)

Global Instance preidem_split {X : Type} (f : X -> X) (S : Splitting f)
: IsPreIdempotent f.
Proof.
  destruct S as [R p].
  refine (ispreidem_homotopic _ p); exact _.
Defined.

Arguments preidem_split / .

Global Instance qidem_split {X : Type} (f : X -> X) (S : Splitting f)
: @IsQuasiIdempotent X f (preidem_split f S).
Proof.
  destruct S as [R p].
  refine (isqidem_homotopic _ p); exact _.
Defined.

Arguments qidem_split / .

(** ** Quasi-idempotents split *)

(** We now show the converse, that every quasi-idempotent splits. *)

Section Splitting.
  (** We need funext because our construction will involve a sequential limit.  We could probably also use a HIT sequential colimit, which is more like what Lurie does.  (Note that, like an interval type, HIT sequential colimits probably imply funext, so our construction uses strictly weaker hypotheses.) *)
  Context `{Funext}.
  Context {X : Type} (f : X -> X).
  Context `{IsQuasiIdempotent _ f}.

  Let I := @isidem X f _.
  Let J : forall x, ap f (I x) = I (f x)
    := @isidem2 X f _ _.

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
    refine (path_sigma' _ _ _).
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
    transitivity a'; refine (path_split_idem _ _); intros n; simpl.
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
    refine (path_split_idem _ _).
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

  (** We conjucture that the particular witness [J] of quasi-idempotence can *not* in general be recovered from the splitting.  This is analogous to how [eissect] and [eisretr] cannot both be recovered after [isequiv_adjointify]; one of them has to be modified. *)

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
    refine (BuildEquiv _ _ (r o split_idem_sect (s o r))
              (BuildIsEquiv _ _ _ (split_idem_retr (s o r) o s) _ _ _)).
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
                            qidem_retract' _).
    intros R.
    exact (@path_retractof _ _
             R (split_idem_retract' (qidem_retract' R))
             (equiv_split_idem_retract R)
             (equiv_split_idem_retract_retr R)
             (equiv_split_idem_retract_sect R)
             (equiv_split_idem_retract_issect R)).
  Defined.

  (** We have a similar result for splittings of a fixed map [f].  *)
  Definition splitting_retractof_isqidem (f : X -> X)
  : RetractOf { I : IsPreIdempotent f & IsQuasiIdempotent f }.
  Proof.
    refine (@equiv_retractof'
              _ (@retractof_equiv'
                   (hfiber quasiidempotent_pr1 f) _ _
                   (retractof_hfiber
                      retract_retractof_qidem quasiidempotent_pr1 retract_idem
                      (fun _ => 1) f))
              (Splitting f) _).
    - refine (equiv_compose' (equiv_inverse
               (hfiber_fibration f
                  (fun g => { I : IsPreIdempotent g & @IsQuasiIdempotent _ g I }))) _).
      unfold hfiber.
      refine (equiv_functor_sigma'
                (equiv_inverse
                   (equiv_sigma_assoc IsPreIdempotent
                                      (fun fi => @IsQuasiIdempotent _ fi.1 fi.2)))
                (fun a => _)); simpl.
      destruct a as [[g I] J]; unfold quasiidempotent_pr1; simpl.
      apply equiv_idmap.
    - simpl.  unfold hfiber, Splitting.
      refine (equiv_functor_sigma' (equiv_idmap (RetractOf X)) _);
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
                 = (@isidem _ f _ x) }.

  Definition splitting_preidem_retractof_qidem (f : PreIdempotent X)
  : RetractOf (IsQuasiIdempotent f).
  Proof.
    refine (@equiv_retractof'
              _ (@retractof_equiv'
                   (hfiber (@pr1 _ (fun fi => @IsQuasiIdempotent _ fi.1 fi.2)) f) _ _
                   (retractof_hfiber
                      retract_retractof_qidem pr1 preidem_retract'
                      _ f))
              (Splitting_PreIdempotent f) _).
    - symmetry; refine (hfiber_fibration f _).
    - intros [[g I] J]; simpl.
      refine (path_sigma' _ 1 _); simpl.
      apply path_forall; intros x; apply split_idem_preidem.
    - simpl; unfold hfiber, Splitting.
      refine (equiv_compose' (equiv_sigma_assoc _ _) _).
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros R; simpl.
      refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
      refine (equiv_functor_sigma' (equiv_ap10 _ _) _); intros H; simpl.
      destruct f as [f I]; simpl in *.
      destruct H; simpl.
      refine (equiv_compose' _ (equiv_inverse (equiv_path_forall _ _)));
        unfold pointwise_paths.
      refine (equiv_functor_forall' (equiv_idmap X) _); intros x; simpl.
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
      refine (equiv_compose' _ (equiv_sigma_symm _)).
      apply equiv_sigma_contr; intros R. 
      apply contr_basedhomotopy.
  Defined.      

  (** For instance, here is the standard coherent idempotent structure on the identity map. *)
  Global Instance isidem_idmap (X : Type@{i})
  : @IsIdempotent@{i i j} X idmap
    := Build_IsIdempotent idmap (splitting_idmap X).

  Definition idem_idmap (X : Type@{i}) : Idempotent@{i i j} X
  := (idmap ; isidem_idmap X).

  (** Note that [Idempotent X], unlike [RetractOf X], lives in the same universe as [X], even if we demand that it contain the identity. *)
  Check (fun (X:Type@{i}) => (idem_idmap X : (Idempotent X : Type@{i}))).

  (** By contrast, [RetractOf X] does not live in the same universe as [X] if it is required to contain the identity retraction. *)
  Fail Check (fun (X:Type@{i}) => (idmap_retractof X : (RetractOf X : Type@{i}))).
  
End CoherentIdempotents.

(** ** Quasi-idempotents need not be fully coherent *)

(** We have shown that every quasi-idempotent can be "coherentified" into a fully coherent idempotent, analogously to how every quasi-inverse can be coherentified into an equivalence.  We now show that, just as for quasi-inverses, not every witness to quasi-idempotency *is itself* coherent.  This is in contrast to a witness of pre-idempotency, which (if it extends to a quasi-idempotent) can itself be extended to a coherent idempotent; this is roughly the content of [split_idem_preidem] and [splitting_preidem_retractof_qidem]. *)

(** We begin by observing that when [f] is the identity, the retract type [Splitting_PreIdempotent f] of [splitting_preidem_retractof_qidem] is equivalent to the type of types-equivalent-to-[X], and hence contractible. *)

Definition contr_splitting_preidem_idmap {ua : Univalence} (X : Type)
: Contr (Splitting_PreIdempotent (preidem_idmap X)).
Proof.
  refine (contr_equiv' {Y : Type & X <~> Y} _).
  unfold Splitting_PreIdempotent, Splitting; simpl.
  refine (equiv_compose' (equiv_sigma_assoc _ _) _); simpl.
  refine (equiv_compose' (equiv_functor_sigma' (issig_retractof X) _) _).
  - intros [A [[r s] H]]; simpl in *.
    exact {p : s o r == idmap &
           forall x, ((ap idmap (p x)^ @ (p (s (r x)))^)
                        @ ap s (H (r x))) @ p x = isidem x }.
  - intros [A [[r s] H]]; simpl. apply equiv_idmap.
  - refine (equiv_compose' (equiv_sigma_assoc _ _) _); simpl.
    refine (equiv_functor_sigma' (equiv_idmap Type) _); intros Y; simpl.
    refine (equiv_compose' (equiv_sigma_assoc _ _) _); simpl.
    refine (equiv_compose' (equiv_sigma_prod _) _).
    refine (equiv_compose' _ (equiv_inverse (issig_equiv X Y))).
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros r; simpl.
    refine (equiv_compose' _ (equiv_inverse (issig_isequiv r))).
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros s; simpl.
    unfold Sect.
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros eta; simpl.
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros ep; simpl.
    refine (equiv_functor_forall' (equiv_idmap _) _).
    intros x; unfold isidem, ispreidem_idmap; simpl.
    rewrite ap_idmap, !concat_pp_p.
    refine (equiv_compose' (equiv_moveR_Vp _ _ _) _).
    rewrite concat_p1, concat_p_pp.
    refine (equiv_compose' (equiv_concat_r (concat_1p _) _) _).
    refine (equiv_compose' (equiv_whiskerR _ _ _) _).
    refine (equiv_compose' (equiv_moveR_Vp _ _ _) _).
    rewrite concat_p1.
    refine (equiv_compose' (equiv_concat_r (y := ap s (ap r (ep x))) _ _) _).
    { refine (cancelR _ _ (ep x) _).
      rewrite <- ap_compose.
      refine (concat_A1p ep (ep x)). }
    pose (isequiv_adjointify s r ep eta).
    exact (equiv_ap (ap s) _ _).
Qed.

(** Therefore, there is a unique coherentification of the canonical witness [preidem_idmap] of pre-idempotency for the identity.  Hence, to show that not every quasi-idempotent is coherent, it suffices to give a witness of quasi-idempotency extending [preidem_idmap] which is nontrivial (i.e. not equal to [qidem_idmap]).

TODO: Do this, using [BAut (BAut Bool)]. *)

(** ** A pre-idempotent that is not quasi-idempotent *)

(** Finally, we give a specific example of a pre-idempotent that does not split, hence is not coherentifiable and not even quasi-idempotent.  This is inspired by Warning 1.2.4.8 in *Higher Algebra*. *)

(** *** Cantor space 2^N *)

(** This should probably go somewhere else. *)

Definition cantor : Type := nat -> Bool.

Definition fold_cantor : cantor + cantor -> cantor.
Proof.
  intros [c|c]; intros n.
  - destruct n as [|n].
    + exact true.
    + exact (c n).
  - destruct n as [|n].
    + exact false.
    + exact (c n).
Defined.

Definition unfold_cantor : cantor -> cantor + cantor.
Proof.
  intros c.
  case (c 0).
  - exact (inl (fun n => c n.+1)).
  - exact (inr (fun n => c n.+1)).
Defined.

Global Instance isequiv_fold_cantor `{Funext} : IsEquiv fold_cantor.
Proof.
  refine (isequiv_adjointify fold_cantor unfold_cantor _ _).
  - intros c; apply path_arrow; intros n.
    induction n as [|n IH].
    + unfold unfold_cantor.
      case (c 0); reflexivity.
    + unfold unfold_cantor.
      case (c 0); reflexivity.
  - intros [c|c]; apply path_sum; reflexivity.
Defined.

Definition equiv_fold_cantor `{Funext} : cantor + cantor <~> cantor
  := BuildEquiv _ _ fold_cantor _.

(** *** BAut *)

(** This should probably go somewhere else too. *)
Definition BAut (C : Type) := { Z : Type & merely (Z = C) }.

Global Instance ispointed_baut C : IsPointed (BAut C)
  := (C ; tr 1).

Definition BAut_pr1 C : BAut C -> Type := pr1.
Coercion BAut_pr1 : BAut >-> Sortclass.

Definition path_baut `{Univalence} C (Z Z' : BAut C)
: (Z <~> Z') <~> (Z = Z' :> BAut C).
Proof.
  eapply equiv_compose'.
  - apply equiv_path_sigma_hprop.
  - apply equiv_path_universe.
Defined.

(** *** An idempotent on BAut(2^N) *)

(** We go into a non-exported module so that we can use short names for definitions without polluting the global namespace. *)

Module BAut_Cantor_Idempotent.
Section Assumptions.
  Context `{Univalence}.

  Definition f : BAut cantor -> BAut cantor.
  Proof.
    intros Z.
    (** Here is the important part of this definition. *)
    exists (Z + cantor).
    (** The rest is just a proof that [Z+cantor] is again equivalent to [cantor], using [fold_cantor] and the assumption that [Z] is equivalent to [cantor]. *)
    pose (e := Z.2); simpl in e; clearbody e.
    strip_truncations.
    apply tr.
    apply path_universe_uncurried.
    refine (equiv_compose' equiv_fold_cantor _).
    apply equiv_functor_sum'.
    - apply equiv_path, e.
    - apply equiv_idmap.
  Defined.

  (** For the pre-idempotence of [f], the main point is again the existence of the equivalence [fold_cantor]. *)
  Definition preidem_f : IsPreIdempotent f.
  Proof.
    intros Z.
    apply path_baut.
    unfold f; simpl.
    refine (equiv_compose' _ (equiv_sum_assoc Z cantor cantor)).
    apply (equiv_functor_sum' (equiv_idmap Z) equiv_fold_cantor).
  Defined.

  (** We record how the action of [f] and [f o f] on paths corresponds to an action on equivalences. *)
  Definition ap_f {Z Z' : BAut cantor} (p : Z = Z')
  : equiv_path _ _ (ap f p)..1
    = equiv_functor_sum' (equiv_path Z Z' p..1) (equiv_idmap cantor).
  Proof.
    destruct p. apply path_equiv, path_arrow.
    intros [z|a]; reflexivity.
  Defined.

  Definition ap_ff {Z Z' : BAut cantor} (p : Z = Z')
  : equiv_path _ _ (ap (f o f) p)..1
    = equiv_functor_sum'
        (equiv_functor_sum' (equiv_path Z Z' p..1) (equiv_idmap cantor))
        (equiv_idmap cantor).
  Proof.
    destruct p. apply path_equiv, path_arrow.
    intros [[z|a]|a]; reflexivity.
  Defined.

  (** Now let's assume [f] is quasi-idempotent, but not necessarily using the same witness of pre-idempotency. *)
  Context (Ip : IsPreIdempotent f) (Jp : @IsQuasiIdempotent _ f Ip).

  Definition I (Z : BAut cantor)
  : (Z + cantor) + cantor <~> Z + cantor
    := equiv_path _ _ (Ip Z)..1.

  Definition I0
  : cantor + cantor + cantor + cantor <~> cantor + cantor + cantor
    := I (f (point (BAut cantor))).

  (** We don't know much about [I0], but we can show that it maps the rightmost two summands to the rightmost one, using the naturality of [I].  Here is the naturality. *)
  Definition Inat (Z Z' : BAut cantor) (e : Z <~> Z')
  : equiv_compose' (I Z') (equiv_functor_sum'
                             (equiv_functor_sum' e (equiv_idmap cantor))
                             (equiv_idmap cantor))
    = equiv_compose' (equiv_functor_sum' e (equiv_idmap cantor)) (I Z).
  Proof.
    revert e; equiv_intro (equiv_path Z Z') q.
    revert q; equiv_intro (equiv_inverse (equiv_path_sigma_hprop Z Z')) p.
    simpl. rewrite <- ap_ff, <- ap_f.
    unfold I. refine ((equiv_path_pp _ _)^ @ _ @ (equiv_path_pp _ _)).
    apply ap.
    refine ((pr1_path_pp (ap (f o f) p) (Ip Z'))^ @ _ @ pr1_path_pp _ _).
    apply ap. apply (concat_Ap Ip).
  Qed.

  (** To show our claim about the action of [I0], we will apply this naturality to the flip automorphism of [cantor + cantor].  Here are the images of that automorphism under [f] and [f o f]. *)
  Definition f_flip :=
    equiv_functor_sum' (equiv_sum_symm cantor cantor)
                       (equiv_idmap cantor).
  Definition ff_flip :=
    equiv_functor_sum'
      (equiv_functor_sum' (equiv_sum_symm cantor cantor)
                          (equiv_idmap cantor))
      (equiv_idmap cantor).

  (** The naturality of [I] implies that [I0] commutes with these images of the flip. *)
  Definition I0nat_flip
        (x : ((cantor + cantor) + cantor) + cantor)
  : I0 (ff_flip x) = f_flip (I0 x)
    := ap10 (ap equiv_fun
                (Inat (f (point (BAut cantor))) (f (point (BAut cantor)))
                      (equiv_sum_symm cantor cantor)))
            x.

  (** The value of this is that we can detect which summand an element is in depending on whether or not it is fixed by [f_flip] or [ff_flip]. *)
  Definition f_flip_fixed_iff_inr (x : cantor + cantor + cantor)
  : (f_flip x = x) <-> is_inr x.
  Proof.
    split; intros p; destruct x as [[c|c]|c]; simpl in p.
    - apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p^).
    - apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p).
    - exact tt.
    - elim p.
    - elim p.
    - reflexivity.
  Defined.

  Definition ff_flip_fixed_iff_inr
        (x : cantor + cantor + cantor + cantor)
  : (ff_flip x = x) <-> (is_inr x + is_inl_and is_inr x).
  Proof.
    split; intros p; destruct x as [[[c|c]|c]|c]; simpl in p.
    - do 2 apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p^).
    - do 2 apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p).
    - exact (inr tt).
    - exact (inl tt).
    - destruct p as [e|e]; elim e.
    - destruct p as [e|e]; elim e.
    - destruct p as [e|_]; [ elim e | reflexivity ].
    - destruct p as [_|e]; [ reflexivity | elim e ].
  Defined.
  
  (** And the naturality guarantees that [I0] preserves fixed points. *)
  Definition I0_fixed_iff_fixed
        (x : cantor + cantor + cantor + cantor)
  : (ff_flip x = x) <-> (f_flip (I0 x) = I0 x).
  Proof.
    split; intros p.
    - refine ((I0nat_flip x)^ @ ap I0 p).
    - apply (equiv_inj I0).
      refine (I0nat_flip x @ p).
  Defined.

  (** Putting it all together, here is the proof of our claim about [I0]. *)
  Definition I0_preserves_inr
        (x : cantor + cantor + cantor + cantor)
  : (is_inr x + is_inl_and is_inr x) <-> is_inr (I0 x).
  Proof.
    refine (iff_compose (f_flip_fixed_iff_inr (I0 x)) _).
    refine (iff_compose (I0_fixed_iff_fixed x) _).
    apply iff_inverse, ff_flip_fixed_iff_inr.
  Defined.

  (** Now we bring quasi-idempotence into play. *)
  Definition J (Z : BAut cantor)
  : equiv_functor_sum' (I Z) (equiv_idmap cantor)
    = I (f Z).
  Proof.
    unfold I; simpl.
    refine ((ap_f (Ip Z))^ @ _).
    do 2 apply ap.
    apply Jp.
  Defined.

  (** We reach a contradiction by showing that the two maps which [J] claims are equal send elements of the third summand of the domain into different summands of the codomain. *)
  Definition impossible : Empty.
  Proof.
    pose (x := inl (inr (fun n => true))
               : ((f (point (BAut cantor))) + cantor) + cantor).
    apply (not_is_inl_and_inr' (I (f (point (BAut cantor))) x)).
    - exact (transport is_inl
                       (ap10 (ap equiv_fun (J (point (BAut cantor)))) x) tt).
    - exact (fst (I0_preserves_inr x) (inr tt)).
  Defined.
  
End Assumptions.
End BAut_Cantor_Idempotent.

(** Let's make the important conclusions available globally. *)

Definition baut_cantor_idem `{Univalence}
: BAut cantor -> BAut cantor
  := BAut_Cantor_Idempotent.f.

Definition preidem_baut_cantor_idem `{Univalence}
: IsPreIdempotent baut_cantor_idem
  := BAut_Cantor_Idempotent.preidem_f.

Definition not_qidem_baut_cantor_idem `{Univalence}
: ~ { I : IsPreIdempotent baut_cantor_idem
        & IsQuasiIdempotent baut_cantor_idem }
  := fun IJ => BAut_Cantor_Idempotent.impossible IJ.1 IJ.2.
