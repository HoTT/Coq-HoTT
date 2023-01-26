Require Import Basics Types WildCat Truncations.Core Truncations.SeparatedTrunc
  Pointed.Core Pointed.pEquiv Pointed.Loops Pointed.pModality.

Local Open Scope pointed_scope.

(** * Truncations of pointed types *)

Definition pTr (n : trunc_index) (A : pType) : pType
  := [Tr n A, _].

(** We specialize [pto] and [pequiv_pto] from pModalities.v to truncations. *)

Definition ptr {n : trunc_index} {A : pType} : A ->* pTr n A
  := pto (Tr n) _.

Definition pequiv_ptr {n : trunc_index} {A : pType} `{IsTrunc n A}
  : A <~>* pTr n A := @pequiv_pto (Tr n) A _.

(** We could specialize [pO_rec] to give the following result, but since maps induced by truncation-recursion compute on elements of the form [tr _], we can give a better proof of pointedness than the one coming from [pO_rec]. *)
Definition pTr_rec n {X Y : pType} `{IsTrunc n Y} (f : X ->* Y)
  : pTr n X ->* Y
  := Build_pMap (pTr n X) Y (Trunc_rec f) (point_eq f).

(** Note that we get an equality of pointed functions here, without Funext, while [pO_rec_beta] only gives a pointed homotopy. This is because [pTr_rec] computes on elements of the form [tr _]. *)
Definition pTr_rec_beta_path n {X Y : pType} `{IsTrunc n Y} (f : X ->* Y)
  : pTr_rec n f o* ptr = f.
Proof.
  unfold pTr_rec, "o*"; cbn.
  (* Since [f] is definitionally equal to [Build_pMap _ _ f (point_eq f)], this works: *)
  apply (ap (Build_pMap _ _ f)).
  apply concat_1p.
Defined.

(** The version with a pointed homotopy. *)
Definition pTr_rec_beta n {X Y : pType} `{IsTrunc n Y} (f : X ->* Y)
  : pTr_rec n f o* ptr ==* f
  := phomotopy_path (pTr_rec_beta_path n f).

(** A pointed version of the induction principle. *)
Definition pTr_ind n {X : pType} {Y : pFam (pTr n X)} `{forall x, IsTrunc n (Y x)} (f : pForall X (Y.1 o tr; Y.2))
  : pForall (pTr n X) Y
  := Build_pForall (pTr n X) Y (Trunc_ind Y f) (dpoint_eq f).

Definition equiv_ptr_rec `{Funext} {n} {X Y : pType} `{IsTrunc n Y}
  : (pTr n X ->* Y) <~> (X ->* Y).
Proof.
  srapply equiv_adjointify.
  { intro f.
    exact (f o* ptr). }
  1: srapply pTr_rec.
  1: nrapply pTr_rec_beta_path.
  intro f.
  apply path_pforall.
  srapply Build_pHomotopy.
  1: by rapply Trunc_ind.
  cbn.
  symmetry; apply concat_pp_V.
Defined.

(** ** Functoriality of [pTr] *)

Global Instance is0functor_ptr n : Is0Functor (pTr n).
Proof.
  apply Build_Is0Functor.
  intros X Y f.
  exact (pTr_rec _ (ptr o* f)).
Defined.

Global Instance is1functor_ptr n : Is1Functor (pTr n).
Proof.
  apply Build_Is1Functor.
  - intros X Y f g p.
    srapply pTr_ind; cbn.
    snrapply Build_pForall.
    + cbn. exact (fun x => ap tr (p x)).
    + pointed_reduce.
      exact (concat_p1 _ @ concat_p1 _ @ ap _ (concat_p1 _))^.
  - intros X.
    srapply Build_pHomotopy.
    1: apply Trunc_rec_tr.
    cbn. reflexivity.
  - intros X Y Z f g.
    srapply Build_pHomotopy.
    1: by rapply Trunc_ind.
    by pointed_reduce.
Defined.

(** Naturality of [ptr].  Note that we get a equality of pointed functions, not just a pointed homotopy. *)
Definition ptr_natural_path (n : trunc_index) {X Y : pType} (f : X ->* Y)
  : fmap (pTr n) f o* ptr = ptr o* f
  := pTr_rec_beta_path n (ptr o* f).

(** The version with a pointed homotopy. *)
Definition ptr_natural (n : trunc_index) {X Y : pType} (f : X ->* Y)
  : fmap (pTr n) f o* ptr ==* ptr o* f
  := phomotopy_path (ptr_natural_path n f).

Definition ptr_functor_pconst {X Y : pType} n
  : fmap (pTr n) (@pconst X Y) ==* pconst.
Proof.
  srapply Build_pHomotopy.
  1: by rapply Trunc_ind.
  reflexivity.
Defined.

Definition ptr_pequiv {X Y : pType} (n : trunc_index) (f : X <~>* Y)
  : pTr n X <~>* pTr n Y
  := emap (pTr n) f.

Definition ptr_loops `{Univalence} (n : trunc_index) (A : pType)
  : pTr n (loops A) <~>* loops (pTr n.+1 A).
Proof.
  srapply Build_pEquiv'.
  1: apply equiv_path_Tr.
  reflexivity.
Defined.

Definition ptr_iterated_loops `{Univalence} (n : trunc_index)
  (k : nat) (A : pType)
  : pTr n (iterated_loops k A) <~>* iterated_loops k (pTr (trunc_index_inc' n k) A).
Proof.
  revert A n.
  induction k.
  { intros A n; cbn.
    reflexivity. }
  intros A n.
  cbn; etransitivity.
  1: apply ptr_loops.
  rapply (emap loops).
  apply IHk.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
  : pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).

Definition pequiv_ptr_functor {X Y : pType} n
  : X <~>* Y -> pTr n X <~>* pTr n Y.
Proof.
  intro e.
  srapply Build_pEquiv.
  1: rapply (fmap (pTr _) e).
  exact _.
Defined.

(* This lemma generalizes a goal that appears in [ptr_loops_commutes], allowing us to prove it by path induction. *)
Definition path_Tr_commutes (n : trunc_index) (A : Type) (a0 a1 : A)
  : (@path_Tr n A a0 a1) o tr == ap tr.
Proof.
  intro p; induction p.
  reflexivity.
Defined.

(* [ptr_loops] commutes with the two [ptr] maps. *)
Definition ptr_loops_commutes `{Univalence} (n : trunc_index) (A : pType)
  : (ptr_loops n A) o* ptr ==* fmap loops ptr.
Proof.
  srapply Build_pHomotopy.
  - intro p.
    simpl.
    refine (_ @ _).
    + apply path_Tr_commutes.
    + symmetry; refine (_ @ _).
      * apply concat_1p.
      * apply concat_p1.
  - simpl.
    reflexivity.
Defined.

