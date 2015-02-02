(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.
Require Import hit.Truncations.

Local Open Scope equiv_scope.
Local Open Scope path_scope.
Local Open Scope pointed_scope.

(** * More about pointed types *)

(** ** Equivalences *)

Definition issig_ptype : { X : Type & X } <~> pType.
Proof.
  issig Build_pType pointed_type ispointed_type.
Defined.

Definition issig_pmap (A B : pType)
: { f : A -> B & f (point A) = point B } <~> (A ->* B).
Proof.
  issig (@Build_pMap A B) (@pointed_fun A B) (@point_eq A B).
Defined.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) @ point_eq g = point_eq f } <~> (f ==* g).
Proof.
  issig (@Build_pHomotopy A B f g) (@pointed_htpy A B f g) (@point_htpy A B f g).
Defined.

Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
: (f ==* g) <~> (f = g).
Proof.
  refine ((equiv_ap' (issig_pmap A B)^-1 f g)^-1 o _); cbn.
  refine (_ o (issig_phomotopy f g)^-1).
  refine (equiv_path_sigma _ _ _ o _); cbn.
  refine (equiv_functor_sigma' (equiv_path_arrow f g) _); intros p. cbn.
  refine (_ o equiv_moveL_Vp _ _ _).
  refine (_ o equiv_path_inverse _ _).
  apply equiv_concat_l.
  refine (transport_paths_Fl (path_forall f g p) (point_eq f) @ _).
  apply whiskerR, inverse2.
  refine (ap_apply_l (path_forall f g p) (point A) @ _).
  apply ap10_path_forall.
Defined.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
: (f ==* g) -> (f = g)
  := equiv_path_pmap f g.

Definition issig_pequiv (A B : pType)
: { f : A <~> B & f (point A) = point B } <~> (A <~>* B).
Proof.
  transitivity { f : A ->* B & IsEquiv f }.
  2:issig (@Build_pEquiv A B) (@pointed_equiv_fun A B) (@pointed_isequiv A B).
  refine ((equiv_functor_sigma'
             (P := fun f => IsEquiv f.1)
             (issig_pmap A B) (fun f => equiv_idmap _)) o _).
  refine (_ o (equiv_functor_sigma'
                 (Q := fun f => f.1 (point A) = point B)
                 (issig_equiv A B)^-1
                 (fun f => equiv_idmap _))).
  refine (_ o (equiv_sigma_assoc _ _)^-1).
  refine (equiv_sigma_assoc _ _ o _).
  refine (equiv_functor_sigma' 1 _); intros f; simpl.
  apply equiv_sigma_symm0.
Defined.

Definition equiv_path_ptype `{Univalence} (A B : pType)
: (A <~>* B) <~> (A = B :> pType).
Proof.
  destruct A as [A a]. destruct B as [B b].
  refine (equiv_ap issig_ptype (A;a) (B;b) o _).
  refine (equiv_path_sigma _ _ _ o _).
  refine (_ o (issig_pequiv _ _)^-1); simpl.
  refine (equiv_functor_sigma' (equiv_path_universe A B) _); intros f.
  apply equiv_concat_l.
  apply transport_path_universe.
Defined.

Definition path_ptype `{Univalence} {A B : pType}
: (A <~>* B) -> (A = B :> pType)
  := equiv_path_ptype A B.

(** ** Loop spaces *)

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  refine (Build_pEquiv _ _ (Build_pMap (loops A) (loops A) inverse 1)
                       (isequiv_path_inverse _ _)).
Defined.

(** ** Pointed fibers *)

Definition pfiber {A B : pType} (f : A ->* B) : pType.
Proof.
  refine (Build_pType (hfiber f (point B)) _); try exact _.
  exists (point A).
  apply point_eq.
Defined.

Definition pfib {A B : pType} (f : A ->* B) : pfiber f ->* A
  := (Build_pMap (pfiber f) A pr1 1).

(** The double fiber object is equivalent to loops on the base. *)
Definition pfiber2_loops {A B : pType} (f : A ->* B)
: pfiber (pfib f) <~>* loops B.
Proof.
  apply issig_pequiv; refine (_;_).
  - simpl; unfold hfiber.
    refine (_ o (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ o (equiv_functor_sigma'
                   (P := fun a => {_ : f a = point B & a = point A})
                   (Q := fun a => {_ : a = point A & f a = point B })
                   1 (fun a => equiv_sigma_symm0 _ _))).
    refine (_ o equiv_sigma_assoc _ (fun a => f a.1 = point B)).
    refine (_ o equiv_contr_sigma _); simpl.
    apply equiv_concat_l.
    symmetry; apply point_eq.
  - simpl.
    apply concat_Vp.
Defined.

(** The triple-fiber functor is equal to the negative of the loopspace functor. *)
Definition pfiber2_loops_functor {A B : pType} (f : A ->* B)
: loops_inv _ o* pfiber2_loops f o* pfib (pfib (pfib f))
  ==* loops_functor f o* pfiber2_loops (pfib f).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _).
  - intros [[xp q] r]. simpl in *.
    rewrite !transport_paths_Fl.
    rewrite inv_pp, !ap_V, !inv_V, ap_compose, !ap_pp, inv_pp.
    simpl; rewrite !concat_1p, !concat_p1.
    rewrite ap_pr1_path_basedpaths'.
    rewrite ap_V, inv_V; apply whiskerR.
    match goal with
        |- ?a = ap f (ap ?g ?z) =>
        change (a = ap f (ap (pr1 o pr1) z))
    end.
    rewrite (ap_compose pr1 pr1).
    rewrite ap_pr1_path_basedpaths'.
    (** In order to destruct [r], we have to invert it to match Paulin-Mohring path induction.  I don't know why the [set] fails to catch the [r^] in the conclusion. *)
    set (s := r^); change ((xp.2)^ = ap f (ap pr1 s)).
    clearbody s; clear r; destruct s; reflexivity.
  - reflexivity.
Qed.

(** ** Truncations *)

Global Instance ispointed_tr (n : trunc_index) (A : Type) `{IsPointed A}
: IsPointed (Tr n A)
  := tr (point A).

Definition pTr (n : trunc_index) (A : pType) : pType
  := Build_pType (Tr n A) _.

Definition ptr_loops `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) <~>* loops (pTr n.+1 A).
Proof.
  refine (issig_pequiv _ _ (_;_)).
  - apply equiv_path_Tr.
  - reflexivity.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).
