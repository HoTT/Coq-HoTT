Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Fibrations.
Require Import Factorization.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pEquiv.
Require Import Pointed.pHomotopy.

Import TrM.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A) : IsPointed (a = a) := 1.

Definition loops (A : pType) : pType
  := Build_pType (point A = point A) _.

Fixpoint iterated_loops (n : nat) (A : pType) : pType
  := match n with
       | O => A
       | S p => loops (iterated_loops p A)
     end.

(* Inner unfolding for iterated loops *)
Lemma unfold_iterated_loops (n : nat) (X : pType)
  : iterated_loops n.+1 X = iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  by refine (ap loops IHn @ _).
Defined.

(** The loop space decreases the truncation level by one.  We don't bother making this an instance because it is automatically found by typeclass search, but we record it here in case anyone is looking for it. *)
Definition istrunc_loops {n} (A : pType) `{IsTrunc n.+1 A}
  : IsTrunc n (loops A) := _.

(** Similarly for connectedness. *)
Definition isconnected_loops `{Univalence} {n} (A : pType)
  `{IsConnected n.+1 A} : IsConnected n (loops A) := _.

(** ** Functoriality of loop spaces *)

Definition loops_functor {A B : pType} (f : A ->* B)
: (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Fixpoint iterated_loops_functor {A B : pType} (n : nat) 
  : (A ->* B) -> (iterated_loops n A) ->* (iterated_loops n B).
Proof.
  destruct n.
  1: exact idmap.
  refine (loops_functor o _).
  apply iterated_loops_functor.
Defined.

(* Loops functor respects composition *)
Definition loops_functor_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : (loops_functor (pmap_compose g f))
  ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
  serapply Build_pHomotopy.
  { intros p.
    pointed_reduce.
    apply ap_compose. }
  by pointed_reduce.
Defined.

(* Iterated loops functor respects composition *)
Lemma iterated_loops_functor_compose `{Univalence} n A B C (f : B ->* C)
  (g : A ->* B) : iterated_loops_functor n (f o* g)
  ==* (iterated_loops_functor n f) o* (iterated_loops_functor n g).
Proof.
  induction n; cbn.
  1: reflexivity.
  destruct (path_pmap IHn)^.
  apply loops_functor_compose.
Defined.

(* Loops functor respects identity *)
Definition loops_functor_idmap (A : pType)
  : loops_functor (@pmap_idmap A) ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  { intro p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _). }
  reflexivity.
Defined.

(* Loops functor distributes over concatenation *)
Lemma loops_functor_pp {X Y : pType} (f : pMap X Y) (x y : loops X)
  : loops_functor f (x @ y) = loops_functor f x @ loops_functor f y.
Proof.
  pointed_reduce.
  apply ap_pp.
Defined.

Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
  : (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  serapply Build_pHomotopy; cbn.
  { intro q.
    refine (_ @ (concat_p1 _)^ @ (concat_1p _)^).
    apply moveR_Vp, concat_Ap. }
  hott_simpl.
Defined.

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_loops_functor {n} (A B : pType) (f : A ->* B)
  `{IsTruncMap n.+1 _ _ f} : IsTruncMap n (loops_functor f).
Proof.
  intro p.
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_Vp _ _ _))).
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_pM _ _ _))).
Defined.

(** And likewise the connectedness.  *)
(* Note: We give the definition explicitly since it was slow before. *)
Global Instance isconnected_loops_functor `{Univalence} {n : trunc_index}
  (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
  : IsConnMap n (loops_functor f) := fun (p : loops B) =>
    isconnected_equiv' n _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_Vp _ p _)) (isconnected_equiv' n _
    (equiv_functor_sigma' 1 (fun q => equiv_moveR_pM _ _ _))
    (isconnected_equiv' n _ (hfiber_ap _)^-1 (isconnected_paths _ _))).

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} n {A B : pType} (f : A ->* B)
  : loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
  <~> image n (loops_functor f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization
    (@IsConnMap n) (@MapIn n) (loops_functor f))).
  { refine (@Build_Factorization (@IsConnMap n) (@MapIn n)
      (loops A) (loops B) (loops_functor f) (loops C)
      (loops_functor g) (loops_functor h) _ _ _).
    intros x; symmetry.
    refine (_ @ pointed_htpy (loops_functor_compose h g) x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate (path_factor (O_factsys n) (loops_functor f) I
    (image n (loops_functor f)))).
Defined.

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  serapply Build_pEquiv.
  1: exact (Build_pMap (loops A) (loops A) inverse 1).
  apply isequiv_path_inverse.
Defined.

(* Loops functor preserves equivalences *)
Definition pequiv_loops_functor `{Funext} {A B : pType}
  : A <~>* B -> loops A <~>* loops B.
Proof.
  intro f.
  serapply pequiv_adjointify.
  1: apply loops_functor, f.
  1: apply loops_functor, (pequiv_inverse f).
  1,2: refine ((loops_functor_compose _ _)^* @* _ @* loops_functor_idmap _).
  1,2: apply phomotopy_ap.
  1: apply peisretr.
  apply peissect.
Defined.

Lemma pequiv_iterated_loops_functor `{Funext} {A B n} : A <~>* B
  -> iterated_loops n A <~>* iterated_loops n B.
Proof.
  intros f.
  induction n.
  1: apply f.
  by apply pequiv_loops_functor.
Defined.

(* Loops preserves products *)
Lemma loops_prod (X Y : pType) : loops (X * Y) <~>* loops X * loops Y.
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: symmetry; refine (equiv_path_prod (point _) (point (X * Y))).
  reflexivity.
Defined.

(* Iterated loops products preserve products *)
Lemma iterated_loops_prod `{Univalence} (X Y : pType) {n}
  : iterated_loops n (X * Y) <~>* (iterated_loops n X) * (iterated_loops n Y).
Proof.
  induction n.
  1: reflexivity.
  refine (pequiv_compose _ (loops_prod _ _)).
  by apply pequiv_loops_functor.
Defined.

(* A dependent form of loops *)
Definition loopsD A : pFam A -> pFam (loops A)
  := fun Pp => (fun q => transport Pp.1 q Pp.2 = Pp.2; 1).

(* Loops for pointed type families *)
Definition pfam_loops : {A : pType & pFam A} -> {A : pType & pFam A}
  := functor_sigma loops loopsD.

(* psigma and loops 'commute' *)
Lemma loops_psigma_commute `{Univalence}
  : loops o psigma == psigma o pfam_loops.
Proof.
  intros x.
  apply path_ptype.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: exact (equiv_path_sigma _ _ _)^-1%equiv.
  reflexivity.
Defined.

(* pforall and loops 'commute' *)
Lemma loops_pforall_commute `{Univalence} (A : Type) (F : A -> pType)
  : loops (pforall (A; F)) = pforall (A; loops o F).
Proof.
  apply path_ptype.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: apply equiv_apD10.
  reflexivity.
Defined.

(* pforall and iterated loops commute *)
Lemma iterated_loops_pforall_commute `{Univalence} (A : Type) (F : A -> pType) (n : nat)
  : iterated_loops n (pforall (A; F)) = pforall (A; iterated_loops n o F).
Proof.
  induction n; cbn.
  1: reflexivity.
  refine (ap loops IHn @ _).
  apply loops_pforall_commute.
Defined.

(* Loops neutralise sigmas when truncated *)
Lemma loops_psigma_trunc `{Univalence} (n : nat) : forall (Aa : pType)
  (Pp : pFam Aa) (istrunc_Pp : IsTrunc_pFam (nat_to_trunc_index_2 n) Pp),
  iterated_loops n (psigma (Aa; Pp))
  = iterated_loops n Aa.
Proof.
  induction n.
  { intros A P p.
    serapply path_ptype.
    srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
    1: refine (@equiv_sigma_contr _ _ p).
    reflexivity. }
  intros A P p.
  refine (unfold_iterated_loops _ _ @ _).
  refine (ap _ (loops_psigma_commute _) @ _).
  refine (IHn _ _ _ @ (unfold_iterated_loops _ _)^).
  intro; refine (@istrunc_paths _ _ (p (point A)) _ _).
Defined.

(* We declare this local notation to make it easier to write pointed types *)
Local Notation "( X , x )" := (Build_pType X x).

(* Here are some path lemmas we will need *)
Local Lemma path_ptype_path_equiv `{Univalence} (A : Type)
  : (A = A, 1) = (A <~> A, 1%equiv).
Proof.
  apply path_ptype.
  refine (Build_pEquiv _ _ (Build_pMap (A = A, 1)
    (A <~> A, 1%equiv) (equiv_path A A) 1) _).
  exact (isequiv_equiv_path A A).
Defined.

Local Lemma path_ptype_issig_equiv `{Univalence} (A : Type)
  : (A <~> A, 1%equiv) = Build_pType
    {f : A -> A & IsEquiv f} (idmap; isequiv_idmap A).
Proof.
  symmetry.
  apply path_ptype.
  refine (Build_pEquiv _ _ (Build_pMap
    ({f : A -> A & IsEquiv f}, (idmap; isequiv_idmap A))
    (A <~> A, 1%equiv) (issig_equiv _ _) 1) _).
Defined.

(* We can convert between families of loops in a type and
   loops in Type at that type *)
Lemma local_global_looping `{Univalence} (A : Type) (n : nat)
  : iterated_loops n.+2 (Type, A)
  = pforall (A; fun a => iterated_loops n.+1 (A, a)).
Proof.
  refine (unfold_iterated_loops _ _ @ _).
  change (loops (Type, A)) with (A = A, 1).
  refine (ap _ (path_ptype_path_equiv A) @ _).
  refine (ap _ (path_ptype_issig_equiv A) @ _).
  change ({f : A -> A & IsEquiv f}, (idmap; isequiv_idmap A)) with
    (psigma ((A -> A, idmap); (IsEquiv; isequiv_idmap A))).
  refine (loops_psigma_trunc n.+1 (A -> A, idmap)
    (IsEquiv; isequiv_idmap A) _ @ _).
  { intros x.
    induction n.
    1: apply hprop_isequiv.
    apply trunc_succ. }
  change (A -> A, idmap) with (pforall (A; fun a => (A, a))).
  apply (iterated_loops_pforall_commute _ _ n.+1).
Defined.

(* 7.2.7 *)
Theorem equiv_istrunc_istrunc_loops `{Univalence} n X
  : IsTrunc n.+2 X <~> forall x, IsTrunc n.+1 (loops (X, x)).
Proof.
  serapply equiv_iff_hprop.
  intro tr_loops.
  intros x y p.
  destruct p.
  apply tr_loops.
Defined.

(* This is slightly different to 7.2.9 in that we ommit n = -1, which is
   inhabited hsets are contractible. *)
Theorem equiv_istrunc_contr_iterated_loops `{Univalence} (n : nat)
  : forall A, IsTrunc n A <~> forall a : A,
    Contr (iterated_loops n.+1 (A, a)).
Proof.
  induction n.
  { intro A.
    refine (equiv_composeR' equiv_hset_axiomK _).
    refine (equiv_iff_hprop (fun K a => BuildContr _ 1 (fun x => (K a x)^)) _).
    intros ? ? ?; apply path_contr. }
  intro A.
  transitivity (forall x, IsTrunc n (loops (A, x))).
  1: destruct n; apply equiv_istrunc_istrunc_loops.
  serapply equiv_functor_forall_id.
  intro a.
  apply (equiv_composeR' (IHn (loops (A, a)))).
  cbn; refine (equiv_iff_hprop _ _).
  1: change ((forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))
      -> Contr (iterated_loops n.+2 (A, a))).
  1: refine (fun X => (ap _ (unfold_iterated_loops n.+1 _))^ # X 1).
  change (Contr (iterated_loops n.+2 (A, a))
    -> (forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))).
  intros X p.
  refine (@contr_equiv' _ _ _ X).
  rewrite !unfold_iterated_loops.
  apply pointed_equiv_equiv.
  apply pequiv_iterated_loops_functor.
  symmetry.
  transitivity (p @ p^ = p @ p^, 1).
  { srefine (Build_pEquiv' _ _).
    1: exact (equiv_ap (equiv_concat_r _ _) _ _).
    reflexivity. }
  serapply Build_pEquiv'.
  { apply equiv_concat_lr.
    1: symmetry; apply concat_pV.
    apply concat_pV. }
  cbn; by rewrite concat_p1, concat_Vp.
Qed.
