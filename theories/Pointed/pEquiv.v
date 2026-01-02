From HoTT Require Import Basics.
Require Import Types.
From HoTT.WildCat Require Import Core Equiv Yoneda.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* Pointed equivalence is a reflexive relation. *)
Instance pequiv_reflexive : Reflexive pEquiv.
Proof.
  intro; exact pequiv_pmap_idmap.
Defined.

(* We can probably get rid of the following notation, and use ^-1$ instead. *)
Notation "f ^-1*" := (@cate_inv pType _ _ _ _ hasequivs_ptype _ _ f) : pointed_scope.

(* Pointed equivalence is a symmetric relation. *)
Instance pequiv_symmetric : Symmetric pEquiv.
Proof.
  intros ? ?; exact pequiv_inverse.
Defined.

(* Pointed equivalences compose. *)
Definition pequiv_compose {A B C : pType} (f : A <~>* B) (g : B <~>* C)
  : A <~>* C
  := g $oE f.

(* Pointed equivalence is a transitive relation. *)
Instance pequiv_transitive : Transitive pEquiv.
Proof.
  intros ? ? ?; exact pequiv_compose.
Defined.

Notation "g o*E f" := (pequiv_compose f g) : pointed_scope.

(* Sometimes we wish to construct a pEquiv from an equiv and a proof that it is pointed. *)
Definition Build_pEquiv' {A B : pType} (f : A <~> B)
  (p : f (point A) = point B)
  : A <~>* B := Build_pEquiv (Build_pMap f p) _.

(** The [&] is a bidirectionality hint that tells Coq to unify with the typing context after type checking the arguments to the left.  In practice, this allows Coq to infer [A] and [B] from the context. *)
Arguments Build_pEquiv' {A B} & f p.

(* A version of equiv_adjointify for pointed equivalences where all data is pointed. There is a lot of unnecessary data here but sometimes it is easier to prove equivalences using this. *)
Definition pequiv_adjointify {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : f o* f' ==* pmap_idmap) (s : f' o* f == pmap_idmap) : A <~>* B
  := (Build_pEquiv f (isequiv_adjointify f f' r s)).

(* In some situations you want the back and forth maps to be pointed but not the sections. *)
Definition pequiv_adjointify' {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : f o f' == idmap) (s : f' o f == idmap) : A <~>* B
  := (Build_pEquiv f (isequiv_adjointify f f' r s)).

(** Pointed versions of [moveR_equiv_M] and friends. *)
Definition moveR_pequiv_Mf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : g ==* f^-1* o* h)
  : (f o* g ==* h).
Proof.
  refine (pmap_postwhisker f p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker h (peisretr f) @* _).
  apply pmap_postcompose_idmap.
Defined.

Definition moveL_pequiv_Mf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : f^-1* o* h ==* g)
  : (h ==* f o* g).
Proof.
  refine (_ @* pmap_postwhisker f p).
  refine (_ @* (pmap_compose_assoc _ _ _)).
  refine ((pmap_postcompose_idmap _)^* @* _).
  apply pmap_prewhisker.
  symmetry; apply peisretr.
Defined.

Definition moveL_pequiv_Vf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : f o* g ==* h)
  : g ==* f^-1* o* h.
Proof.
  refine (_ @* pmap_postwhisker f^-1* p).
  refine (_ @* (pmap_compose_assoc _ _ _)).
  refine ((pmap_postcompose_idmap _)^* @* _).
  apply pmap_prewhisker.
  symmetry; apply peissect.
Defined.

Definition moveR_pequiv_Vf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : h ==* f o* g)
   : f^-1* o* h ==* g.
Proof.
  refine (pmap_postwhisker f^-1* p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker g (peissect f) @* _).
  apply pmap_postcompose_idmap.
Defined.

Definition moveR_pequiv_fV {A B C} (f : B ->* C) (g : A <~>* B) (h : A ->* C)
           (p : f o* g ==* h)
  : (f ==* h o* g^-1*).
Proof.
  refine (_ @* pmap_prewhisker g^-1* p).
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  refine ((pmap_precompose_idmap _)^* @* _).
  apply pmap_postwhisker.
  symmetry; apply peisretr.
Defined.

Definition pequiv_pequiv_precompose `{Funext} {A B C : pType} (f : A <~>* B)
  : (B ->** C) <~>* (A ->** C).
Proof.
  srapply Build_pEquiv'.
  - exact (equiv_precompose_cat_equiv f).
  - (* By using [pelim f], we can avoid [Funext] in this part of the proof. *)
    cbn; unfold "o*", point_pforall; cbn.
    by pelim f.
Defined.

Definition pequiv_pequiv_postcompose `{Funext} {A B C : pType} (f : B <~>* C)
  : (A ->** B) <~>* (A ->** C).
Proof.
  srapply Build_pEquiv'.
  - exact (equiv_postcompose_cat_equiv f).
  - cbn; unfold "o*", point_pforall; cbn.
    by pelim f.
Defined.

Proposition equiv_pequiv_inverse `{Funext} {A B : pType}
  : (A <~>* B) <~> (B <~>* A).
Proof.
  refine (issig_pequiv' _ _ oE _ oE (issig_pequiv' A B)^-1).
  srapply (equiv_functor_sigma' (equiv_equiv_inverse _ _)); intro e; cbn.
  exact (equiv_moveR_equiv_V _ _ oE equiv_path_inverse _ _).
Defined.
