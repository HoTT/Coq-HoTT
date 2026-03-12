From HoTT Require Import Basics Types Truncations
  Pointed.Core Pointed.pEquiv Pointed.Loops Pointed.pModality.
From HoTT.WildCat Require Import Core Equiv.

Local Open Scope pointed_scope.

(** * Truncations of pointed types *)

(** TODO: Many things here can be generalized to any modality or any reflective subuniverse, and could be moved to pModality.v *)

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
  := Build_pMap (Trunc_rec f) (point_eq f).

(** Note that we get an equality of pointed functions here, without Funext, while [pO_rec_beta] only gives a pointed homotopy. This is because [pTr_rec] computes on elements of the form [tr _]. *)
Definition pTr_rec_beta_path n {X Y : pType} `{IsTrunc n Y} (f : X ->* Y)
  : pTr_rec n f o* ptr = f.
Proof.
  unfold pTr_rec, "o*"; cbn.
  (* Since [f] is definitionally equal to [Build_pMap _ _ f (point_eq f)], this works: *)
  apply (ap (Build_pMap f)).
  apply concat_1p.
Defined.

(** The version with a pointed homotopy. *)
Definition pTr_rec_beta n {X Y : pType} `{IsTrunc n Y} (f : X ->* Y)
  : pTr_rec n f o* ptr ==* f
  := phomotopy_path (pTr_rec_beta_path n f).

(** A pointed version of the induction principle. *)
Definition pTr_ind n {X : pType} {Y : pFam (pTr n X)} `{forall x, IsTrunc n (Y x)}
  (f : pForall X (Build_pFam (Y o tr) (dpoint Y)))
  : pForall (pTr n X) Y
  := Build_pForall (pTr n X) Y (Trunc_ind Y f) (dpoint_eq f).

Definition pequiv_ptr_rec `{Funext} {n} {X Y : pType} `{IsTrunc n Y}
  : (pTr n X ->** Y) <~>* (X ->** Y)
  := pequiv_o_pto_O _ X Y.

(** ** Functoriality of [pTr] *)

Instance is0functor_ptr n : Is0Functor (pTr n).
Proof.
  apply Build_Is0Functor.
  intros X Y f.
  exact (pTr_rec _ (ptr o* f)).
Defined.

Instance is1functor_ptr n : Is1Functor (pTr n).
Proof.
  apply Build_Is1Functor.
  - intros X Y f g p.
    srapply pTr_ind; cbn.
    snapply Build_pForall.
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

Definition pequiv_ptr_functor {X Y : pType} (n : trunc_index) (f : X <~>* Y)
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
  tapply (emap loops).
  apply IHk.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
  : pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).

(* This lemma generalizes a goal that appears in [ptr_loops_commutes], allowing us to prove it by path induction. *)
Definition path_Tr_commutes (n : trunc_index) (A : Type) (a0 a1 : A) (p : a0 = a1)
  : path_Tr (n:=n) (tr p) = ap tr p.
Proof.
  by destruct p.
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

(** Pointed truncation preserves binary products. *)
Definition pequiv_ptr_prod (n : trunc_index) (A B : pType)
  : pTr n (A * B) <~>* pTr n A * pTr n B.
Proof.
  snapply Build_pEquiv'.
  1: napply equiv_Trunc_prod_cmp.
  reflexivity.
Defined.

(** ** Truncatedness of [pForall] and [pMap] *)

(** Buchholtz-van Doorn-Rijke, Theorem 4.2:  Let [j >= -1] and [n >= -2].  When [X] is [j]-connected and [Y] is a pointed family of [j+n+1]-truncated types, the type of pointed sections is [n]-truncated.  We formalize it with [j] replaced with a trunc index [m.+1] to enforce [j >= -1]. This version also allows [n] to be one smaller than BvDR allow. *)
Definition istrunc_pforall `{Univalence} {m n : trunc_index}
  (X : pType@{u}) {iscX : IsConnected m.+1 X}
  (Y : pFam@{u v} X) {istY : forall x, IsTrunc (n +2+ m) (Y x)}
  : IsTrunc@{w} n (pForall X Y).
Proof.
  napply (istrunc_equiv_istrunc _ (equiv_extension_along_pforall@{v w u} Y)).
  rapply (istrunc_extension_along_conn (n:=m) _ Y (HP:=istY)).
Defined.

(** From this we deduce the non-dependent version, which is Corollary 4.3 of BvDR.  We include [n = -2] here as well, but in this case it is not interesting.  Since [X ->* Y] is inhabited, the [n = -1] case also gives contractibility, with weaker hypotheses. *)
Definition istrunc_pmap `{Univalence} {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X} `{!IsTrunc (n +2+ m) Y}
  : IsTrunc n (X ->* Y)
  := istrunc_pforall X (pfam_const Y).

(** We can give a different proof of the [n = -1] case (with the conclusion upgraded to contractibility).  This proof works with [Tr (m.+1)] replaced with any reflective subuniverse [O] and doesn't require univalence.  Is it possible to generalize this to dependent functions while still avoiding univalence and/or keeping [O] a general RSU or modality?  Can [istrunc_pmap] be proven without univalence?  What about [istrunc_pforall]?  If the [n = -2] or [n = -1] cases can be proven without univalence, the rest can be done inductively without univalence. *)
Definition contr_pmap_isconnected_inO `{Funext} (O : ReflectiveSubuniverse)
  (X : pType) `{IsConnected O X} (Y : pType) `{In O Y}
  : Contr (X ->* Y).
Proof.
  srapply (contr_equiv' ([O X, _] ->* Y)).
  rapply pequiv_o_pto_O.
Defined.

(** Every pointed type is (-1)-connected. *)
Instance is_minus_one_connected_pointed (X : pType)
  : IsConnected (Tr (-1)) X
  := contr_inhabited_hprop _ (tr pt).
