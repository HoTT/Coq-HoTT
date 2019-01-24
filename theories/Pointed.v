(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations Factorization.
Require Import Modalities.Modality HIT.Truncations HIT.Connectedness.
Import TrM.

Local Open Scope path_scope.
Local Open Scope trunc_scope.

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** ** Constructions of pointed types *)

(** Any contractible type is pointed. *)
Global Instance ispointed_contr `{Contr A} : IsPointed A := center A.

(** A pi type with a pointed target is pointed. *)
Global Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => point (B a).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A)
: IsPointed (a = a)
  := idpath.

(** We can build an iterated loop space *)
Definition loops (A : pType) : pType :=
  Build_pType (point A = point A) idpath.

Fixpoint iterated_loops (n : nat) (A : Type) `{H : IsPointed A}
         {struct n} : pType
  := match n with
       | O => Build_pType A (@point A H)
       | S p => iterated_loops p (point A = point A)
     end.

(** The loop space decreases the truncation level by one.  We don't bother making this an instance because it is automatically found by typeclass search, but we record it here in case anyone is looking for it. *)
Definition istrunc_loops {n} (A : pType) `{IsTrunc n.+1 A}
: IsTrunc n (loops A).
Proof.
  exact _.
Defined.

(** Similarly for connectedness. *)
Definition isconnected_loops `{Univalence} {n} (A : pType)
           `{IsConnected n.+1 A}
: IsConnected n (loops A).
Proof.
  exact _.
Defined.

(** ** Pointed functions *)

Record pMap (A B : pType) :=
  { pointed_fun : A -> B ;
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.
Coercion pointed_fun : pMap >-> Funclass.

Declare Scope pointed_scope.
Infix "->*" := pMap : pointed_scope.
Local Open Scope pointed_scope.

Definition pmap_idmap (A : pType): A ->* A
  := Build_pMap A A idmap 1.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose : pointed_scope.

(** Another option would be
<<
Delimit Scope pmap_scope with pmap.
Bind Scope pmap_scope with pMap.
Infix "o" := pmap_compose : pmap_scope.
>>
which would allow us to use [o] for pointed maps as well most of the time.  However, it would sometimes require adding [%pmap] scoping markers. *)

(** ** Pointed homotopies *)

Record pHomotopy {A B : pType} (f g : pMap A B) :=
  { pointed_htpy : f == g ;
    point_htpy : pointed_htpy (point A) @ point_eq g = point_eq f }.

Arguments Build_pHomotopy {A B f g} p q : rename.
Arguments point_htpy {A B f g} p : rename.
Arguments pointed_htpy {A B f g} p x.

Coercion pointed_htpy : pHomotopy >-> pointwise_paths.

Infix "==*" := pHomotopy : pointed_scope.

(** The following tactic often allows us to "pretend" that pointed maps and homotopies preserve basepoints strictly.  We have carefully defined [pMap] and [pHomotopy] so that when destructed, their second components are paths with right endpoints free, to which we can apply Paulin-Morhing path-induction. *)
Ltac pointed_reduce :=
  unfold pointed_fun, pointed_htpy; cbn;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?]
           | [ phi : pMap ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => destruct alpha as [alpha ?]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn;
  (** TODO: [pointed_reduce] uses [rewrite], and thus according to our current general rules, it should only be used in opaque proofs.  We don't yet need any of the proofs that use it to be transparent, but there's a good chance we will eventually.  At that point we can consider whether to allow it in transparent proofs, modify it to not use [rewrite], or exclude it from proofs that need to be transparent. *)
  rewrite ?concat_p1, ?concat_1p.

(** ** Functoriality of loop spaces *)

Definition loops_functor {A B : pType} (f : A ->* B)
: (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
: (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); simpl.
  - intros q.
    refine (_ @ (concat_1p _)^).
    refine (_ @ (concat_p1 _)^).
    apply moveR_Vp.
    refine (concat_Ap p q).
  - simpl.
    abstract (rewrite !concat_p1; reflexivity).
Qed.

(** ** Associativity of pointed map composition *)

Definition pmap_compose_assoc {A B C D : pType}
           (h : C ->* D) (g : B ->* C) (f : A ->* B)
: (h o* g) o* f ==* h o* (g o* f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap A ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap B o* f ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
           (h : B ->* C) (p : f ==* g)
: h o* f ==* h o* g.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - reflexivity.
Qed.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
           {g h : B ->* C} (p : g ==* h)
: g o* f ==* h o* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - refine (concat_p1 _ @ (concat_1p _)^).
Qed.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
           (p : f ==* g) (q : g ==* h)
: f ==* h.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact (p x @ q x).
  - apply concat_p1.
Qed.

Infix "@*" := phomotopy_compose : pointed_scope.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_Vp.
Qed.

Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

(** ** Functoriality of loop spaces *)

Definition loops_functor_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: (loops_functor (pmap_compose g f))
   ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); simpl.
  - intros p.
    apply whiskerL, whiskerR.
    refine (_ @ ap (ap g) (concat_1p _)^).
    refine (_ @ ap (ap g) (concat_p1 _)^).
    apply ap_compose.
  - reflexivity.
Qed.

Definition loops_functor_idmap (A : pType)
: loops_functor (pmap_idmap A) ==* pmap_idmap (loops A).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); simpl.
  - intros p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _).
  - reflexivity.
Qed.

(** ** Loop spaces and truncation and connectedness *)

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_loops_functor {n : trunc_index}
       (A B : pType) (f : A ->* B) `{IsTruncMap n.+1 _ _ f}
: IsTruncMap n (loops_functor f).
Proof.
  intros p. unfold hfiber; simpl.
  refine (trunc_equiv' _ (equiv_functor_sigma' 1 (fun q => equiv_moveR_Vp _ _ _))); simpl.
  refine (trunc_equiv' _ (equiv_functor_sigma' 1 (fun q => equiv_moveR_pM _ _ _))).
Defined.

(** And likewise the connectedness.  *)
Global Instance isconnected_loops_functor `{Univalence} {n : trunc_index}
       (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
: IsConnMap n (loops_functor f).
Proof.
  intros p. unfold hfiber; simpl.
  refine (isconnected_equiv' n _ (equiv_functor_sigma' 1 (fun q => equiv_moveR_Vp _ _ _)) _); simpl.
  refine (isconnected_equiv' n _ (equiv_functor_sigma' 1 (fun q => equiv_moveR_pM _ _ _)) _); simpl.
  refine (isconnected_equiv' n _ (hfiber_ap _)^-1 _).
Defined.

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} (n : trunc_index)
           {A B : pType} (f : A ->* B)
: loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
        <~> image n (loops_functor f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization (@IsConnMap n) (@MapIn n) (loops_functor f))).
  { refine (@Build_Factorization
              (@IsConnMap n) (@MapIn n) (loops A) (loops B) (loops_functor f)
              (loops C) (loops_functor g) (loops_functor h) _ _ _).
    intros x; symmetry.
    refine (_ @ pointed_htpy (loops_functor_compose h g) x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate
           (path_factor (O_factsys n) (loops_functor f) I (image n (loops_functor f)))).
Defined.

(** ** Pointed equivalences *)

Record pEquiv (A B : pType) :=
  { pointed_equiv_fun : A ->* B ;
    pointed_isequiv : IsEquiv pointed_equiv_fun
  }.

Infix "<~>*" := pEquiv : pointed_scope.

Coercion pointed_equiv_fun : pEquiv >-> pMap.
Global Existing Instance pointed_isequiv.

Definition pointed_equiv_equiv {A B} (f : A <~>* B)
: A <~> B
  := BuildEquiv A B f _.

Coercion pointed_equiv_equiv : pEquiv >-> Equiv.

Definition pequiv_inverse {A B} (f : A <~>* B)
: B <~>* A.
Proof.
  refine (Build_pEquiv B A
            (Build_pMap _ _ f^-1 _)
            _).
  apply moveR_equiv_V; symmetry; apply point_eq.
Defined.

Definition pequiv_compose {A B C : pType}
           (f : A <~>* B) (g : B <~>* C)
: A <~>* C
  := (Build_pEquiv A C (g o* f) isequiv_compose).

Notation "g o*E f" := (pequiv_compose f g) : pointed_scope.


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
  refine ((equiv_ap' (issig_pmap A B)^-1 f g)^-1 oE _); cbn.
  refine (_ oE (issig_phomotopy f g)^-1).
  refine (equiv_path_sigma _ _ _ oE _); cbn.
  refine (equiv_functor_sigma' (equiv_path_arrow f g) _); intros p. cbn.
  refine (_ oE equiv_moveL_Vp _ _ _).
  refine (_ oE equiv_path_inverse _ _).
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
             (issig_pmap A B) (fun f => equiv_idmap _)) oE _).
  refine (_ oE (equiv_functor_sigma'
                 (Q := fun f => f.1 (point A) = point B)
                 (issig_equiv A B)^-1
                 (fun f => equiv_idmap _))).
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  refine (equiv_sigma_assoc _ _ oE _).
  refine (equiv_functor_sigma' 1 _); intros f; simpl.
  apply equiv_sigma_symm0.
Defined.

Definition equiv_path_ptype `{Univalence} (A B : pType)
: (A <~>* B) <~> (A = B :> pType).
Proof.
  destruct A as [A a]. destruct B as [B b].
  refine (equiv_ap issig_ptype (A;a) (B;b) oE _).
  refine (equiv_path_sigma _ _ _ oE _).
  refine (_ oE (issig_pequiv _ _)^-1); simpl.
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
  apply issig_pequiv; simple refine (_;_).
  - simpl; unfold hfiber.
    refine (_ oE (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ oE (equiv_functor_sigma'
                   (P := fun a => {_ : f a = point B & a = point A})
                   (Q := fun a => {_ : a = point A & f a = point B })
                   1 (fun a => equiv_sigma_symm0 _ _))).
    refine (_ oE equiv_sigma_assoc _ (fun a => f a.1 = point B)).
    refine (_ oE equiv_contr_sigma _); simpl.
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
  simple refine (Build_pHomotopy _ _).
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

Definition pTr_functor {X Y : pType} (n : trunc_index) (f : X ->* Y)
: pTr n X ->* pTr n Y.
Proof.
  refine (Build_pMap (pTr n X) (pTr n Y) (Trunc_functor n f) _).
  exact (ap (@tr n Y) (point_eq f)).
Defined.

Definition pTr_pequiv {X Y : pType} (n : trunc_index) (f : X <~>* Y)
: pTr n X <~>* pTr n Y
  := Build_pEquiv _ _ (pTr_functor n f) _.

Definition ptr_loops `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) <~>* loops (pTr n.+1 A).
Proof.
  simple refine (issig_pequiv _ _ (_;_)).
  - apply equiv_path_Tr.
  - reflexivity.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).
