(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import PathAny.
Require Import WildCat.

Declare Scope pointed_scope.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** ** Pointed Types *)

(** The unit type is pointed *)
Global Instance ispointed_unit : IsPointed Unit := tt.

(** The Unit pType *)
Definition pUnit : pType := (Build_pType Unit _).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** We override the notation for products in pointed_scope *)
Notation "X * Y" := (Build_pType (X * Y) ispointed_prod) : pointed_scope.

(** A pointed type family consists of a type family over a pointed type and a section of that family at the basepoint. *)
Definition pFam (A : pType) := {P : A -> Type & P (point A)}.

(** We make the first projection of a [pFam] a coercion. *)
Definition pfam_pr1 {A : pType} (P : pFam A) : A -> Type := pr1 P.
Coercion pfam_pr1 : pFam >-> Funclass.

(** We call the section of a pointed type family at the basepoint a [dpoint]. *)
Definition dpoint {A : pType} (P : pFam A) : P (point A) := pr2 P.

(** The constant pointed family *)
Definition pfam_const {A : pType} (B : pType) : pFam A :=
  (fun _ => pointed_type B; point B).

(** [IsTrunc] for a pointed type family *)
Class IsTrunc_pFam n {A} (X : pFam A)
  := trunc_pfam_is_trunc : forall x, IsTrunc n (X.1 x).

(** Pointed dependent functions *)
Record pForall (A : pType) (P : pFam A) := {
  pointed_fun : forall x, P x ;
  dpoint_eq : pointed_fun (point A) = dpoint P ;
}.

Arguments dpoint_eq {A P} f : rename.
Arguments pointed_fun {A P} f : rename.
Coercion pointed_fun : pForall >-> Funclass.


(** ** Pointed functions *)

(** A pointed map is a map with a proof that it preserves the point. We define it as as a notion for a non-dependent version of [pForall]. *)
Notation "A ->* B" := (pForall A (pfam_const B)) : pointed_scope.

Definition Build_pMap (A B : pType) (f : A -> B) (p : f (point A) = point B)
  : A ->* B
  := Build_pForall A (pfam_const B) f p.

(** Pointed maps perserve the base point *)
Definition point_eq {A B : pType} (f : A ->* B)
  : f (point A) = point B
  := dpoint_eq f.

(** The identity pointed map *)
Definition pmap_idmap {A : pType} : A ->* A
  := Build_pMap A A idmap 1.

(** Composition of pointed maps *)
Definition pmap_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : A ->* C
  := Build_pMap A C (g o f) (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose : pointed_scope.

(** ** Pointed homotopies *)

Definition pfam_phomotopy {A : pType} {P : pFam A} (f g : pForall A P) : pFam A
  := (fun x => f x = g x; dpoint_eq f @ (dpoint_eq g)^).

(* A pointed homotopy is a homotopy with a proof that the presevation paths agree. We define it instead as a special case of a [pForall]. This means that we can define pointed homotopies between pointed homotopies. *)
Definition pHomotopy {A : pType} {P : pFam A} (f g : pForall A P) : Type
  := pForall A (pfam_phomotopy f g).

Infix "==*" := pHomotopy : pointed_scope.

Definition Build_pHomotopy {A : pType} {P : pFam A} {f g : pForall A P}
  (p : f == g) (q : p (point A) = dpoint_eq f @ (dpoint_eq g)^)
  : f ==* g
  := Build_pForall A (pfam_phomotopy f g) p q.

(** The underlying homotopy of a pointed homotopy *)
Coercion pointed_htpy {A : pType} {P : pFam A} {f g : pForall A P} (h : f ==* g)
  : f == g
  := h.

(** This is the form that the underlying proof of a pointed homotopy used to take before we changed it to be defined in terms of pForall. *)
Definition point_htpy {A : pType} {P : pFam A} {f g : pForall A P}
  (h : f ==* g) : h (point A) @ dpoint_eq g = dpoint_eq f.
Proof.
  apply moveR_pM.
  exact (dpoint_eq h).
Defined.

(** ** Pointed equivalences *)

(* A pointed equivalence is a pointed map and a proof that it is
  an equivalence *)
Record pEquiv (A B : pType) := {
  pointed_equiv_fun : pForall A (pfam_const B) ;
  pointed_isequiv : IsEquiv pointed_equiv_fun ;
}.

(* TODO: It might be better behaved to define pEquiv as an equivalence and a proof that this equivalence is pointed. In pEquiv.v we have another constructor Build_pEquiv' which coq can infer faster than Build_pEquiv. *)

Infix "<~>*" := pEquiv : pointed_scope.

(* Note: because we define pMap as a special case of pForall, we must declare
  all coercions into pForall, *not* into pMap. *)
Coercion pointed_equiv_fun : pEquiv >-> pForall.
Global Existing Instance pointed_isequiv.

Coercion pointed_equiv_equiv {A B} (f : A <~>* B)
  : A <~> B := Build_Equiv A B f _.

(** Pointed sigma types *)
Definition psigma {A : pType} (P : pFam A) : pType
  := Build_pType (sig P) (point A; P.2).

(** Pointed pi types, note that the domain is not pointed *)
Definition pproduct {A : Type} (F : A -> pType) : pType
  := Build_pType (forall (a : A), pointed_type (F a)) (ispointed_type o F).

(** The following tactics often allow us to "pretend" that pointed maps and homotopies preserve basepoints strictly. *)

(** First a version with no rewrites, which leaves some cleanup to be done but which can be used in transparent proofs. *)
Ltac pointed_reduce :=
  (*TODO: are these correct? *)
  unfold pointed_fun, pointed_htpy;
  cbn in *;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?point]
           | [ P : pFam ?X |- _ ] => destruct P as [P ?]
           | [ phi : pForall ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => let H := fresh in destruct alpha as [alpha H]; try (apply moveR_pM in H)
           | [ equiv : pEquiv ?X ?Y |- _ ] => destruct equiv as [equiv ?iseq]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn.

(** Next a version that uses [rewrite], and should only be used in opaque proofs. *)
Ltac pointed_reduce_rewrite :=
  pointed_reduce;
  rewrite ?concat_p1, ?concat_1p.

(** Finally, a version that just strictifies a single map or equivalence.  This has the advantage that it leaves the context more readable. *)
Ltac pointed_reduce_pmap f
  := try match type of f with
    | pEquiv ?X ?Y => destruct f as [f ?iseq]
    end;
    match type of f with
    | _ ->* ?Y => destruct Y as [Y ?], f as [f p]; cbn in *; destruct p; cbn
    end.

(** ** Equivalences to sigma-types. *)

(** pType *)
Definition issig_ptype : { X : Type & X } <~> pType := ltac:(issig).

(** pForall *)
Definition issig_pforall (A : pType) (P : pFam A)
  : {f : forall x, P x & f (point A) = dpoint P} <~> (pForall A P)
  := ltac:(issig).

(** pMap *)
Definition issig_pmap (A B : pType)
  : {f : A -> B & f (point A) = point B} <~> (A ->* B)
  := ltac:(issig).

(** pHomotopy *)
Definition issig_phomotopy {A : pType} {P : pFam A} (f g : pForall A P)
  : {p : f == g & p (point A) = dpoint_eq f @ (dpoint_eq g)^} <~> (f ==* g)
  := ltac:(issig).

(** pEquiv *)
Definition issig_pequiv (A B : pType)
  : {f : A ->* B & IsEquiv f} <~> (A <~>* B)
  := ltac:(issig).

(** The record for pointed equivalences is equivalently a different sigma type *)
Definition issig_pequiv' (A B : pType)
  : {f : A <~> B & f (point A) = point B} <~> (A <~>* B)
  := ltac:(make_equiv).

(** ** Various operations with pointed homotopies *)

(** [pHomotopy] is a reflexive relation *)
Global Instance phomotopy_reflexive {A : pType} {P : pFam A}
  : Reflexive (@pHomotopy A P)
  := fun X => Build_pHomotopy (fun x => 1) (concat_pV _)^.

(** [pHomotopy] is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B).
Proof.
  intros f g p.
  snrefine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - refine (inverse2 (dpoint_eq p) @ inv_pV _ _).
Defined.

Notation "p ^*" := (phomotopy_symmetric _ _ p) : pointed_scope.

(** [pHomotopy] is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B).
Proof.
  intros x y z p q.
  snrefine (Build_pHomotopy (fun x => p x @ q x) _).
  nrefine (dpoint_eq p @@ dpoint_eq q @ concat_pp_p _ _ _ @ _).
  nrapply whiskerL; nrapply concat_V_pp.
Defined.

Notation "p @* q" := (phomotopy_transitive _ _ _ p q) : pointed_scope.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g)
  : h o* f ==* h o* g.
Proof.
  snrefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => ap h (p x)).
  - nrefine (ap _ (dpoint_eq p) @ ap_pp _ _ _ @ whiskerL _ (ap_V _ _) @ _^).
    nrefine (whiskerL _ (inv_pp _ _) @ concat_pp_p _ _ _ @ _).
    exact (whiskerL _ (concat_p_Vp _ _)).
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h)
  : g o* f ==* h o* f.
Proof.
  snrefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => p (f x)).
  - apply moveL_pV.
    nrefine (concat_p_pp _ _ _ @ whiskerR (concat_Ap p (point_eq f))^ _ @ _).
    exact (concat_pp_p _ _ _ @ whiskerL _ (point_htpy p)).
Defined.

(** ** 1-categorical properties of [pType]. *)

(** Composition of pointed maps is associative up to pointed homotopy *)
Definition pmap_compose_assoc {A B C D : pType} (h : C ->* D)
  (g : B ->* C) (f : A ->* B)
  : (h o* g) o* f ==* h o* (g o* f).
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  pointed_reduce_pmap f.
  pointed_reduce_pmap g.
  pointed_reduce_pmap h.
  reflexivity.
Defined.

(** precomposition of identity pointed map *)
Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap ==* f.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  symmetry.
  apply concat_pp_V.
Defined.

(** postcomposition of identity pointed map *)
Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  symmetry.
  apply moveR_pV.
  simpl.
  refine (concat_p1 _ @ _ @ (concat_1p _)^).
  nrapply ap_idmap.
Defined.

(** ** Funext for pointed types and direct consequences. *)

(** By funext pointed homotopies are equivalent to paths *)
Definition equiv_path_pforall `{Funext} {A : pType}
  {P : pFam A} (f g : pForall A P)
  : (f ==* g) <~> (f = g).
Proof.
  refine (_ oE (issig_phomotopy f g)^-1).
  revert f g; apply (equiv_path_issig_contr (issig_pforall A P)).
  { intros [f feq]; cbn.
    exists (fun a => 1%path).
    exact (concat_pV _)^. }
  intros [f feq]; cbn.
  contr_sigsig f (fun a:A => idpath (f a)); cbn.
  refine (contr_equiv' {feq' : f (point A) = dpoint P & feq = feq'} _).
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p.
  refine (_^-1 oE equiv_path_inverse _ _).
  apply equiv_moveR_1M.
Defined.

Definition path_pforall `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
  : (f ==* g) -> (f = g) := equiv_path_pforall f g.

(** Here is the inverse map without assuming funext *)
Definition phomotopy_path {A : pType} {P : pFam A} {f g : pForall A P}
  : (f = g) -> (f ==* g) := ltac:(by intros []).

(** And we prove that it agrees with the inverse of [equiv_path_pforall] *)
Definition path_equiv_path_pforall_phomotopy_path `{Funext} {A : pType}
  {P : pFam A} {f g : pForall A P}
  : phomotopy_path (f:=f) (g:=g) = (equiv_path_pforall f g)^-1%equiv
  := ltac:(by funext []).

(* We note that the inverse of [path_pmap] computes definitionally on reflexivity, and hence [path_pmap] itself computes typally so. *)
Definition equiv_inverse_path_pforall_1 `{Funext} {A : pType} {P : pFam A} (f : pForall A P)
  : (equiv_path_pforall f f)^-1%equiv 1%path = reflexivity f
  := 1.

Definition path_pforall_1 `{Funext} {A : pType} {P : pFam A} {f : pForall A P}
  : equiv_path_pforall _ _ (reflexivity f) = 1%path
  := moveR_equiv_M _ _ (equiv_inverse_path_pforall_1 f)^.

Definition equiv_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : path_pforall (reflexivity f) = 1%path
  := path_pforall_1.

(** Since pointed homotopies are equivalent to equalities, we can act as if
  they are paths and define a path induction for them *)
Definition phomotopy_ind `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> Type)
  (q : Q k (reflexivity k)) (k' : pForall A P)
  : forall (H : k ==* k'), Q k' H.
Proof.
  equiv_intro (equiv_path_pforall k k')^-1%equiv p.
  induction p.
  exact q.
Defined.

(** Sometimes you have a goal with both a pointed homotopy [H] and [path_pforall H].
  This is an induction principle that allows us to replace both of them by reflexivity
  at the same time. *)
Definition phomotopy_ind' `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> (k = k') -> Type)
  (q : Q k (reflexivity k) 1 % path) (k' : pForall A P) (H : k ==* k')
  (p : k = k') (r : path_pforall H = p)
  : Q k' H p.
Proof.
  induction r.
  revert k' H.
  rapply phomotopy_ind.
  exact (transport (Q _ (reflexivity _)) path_pforall_1^ q).
Defined.

Definition phomotopy_ind_1 `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> Type)
  (q : Q k (reflexivity k)) :
  phomotopy_ind Q q k (reflexivity k) = q.
Proof.
  change (reflexivity k) with ((equiv_path_pforall k k)^-1%equiv (idpath k)).
  apply equiv_ind_comp.
Defined.

Definition phomotopy_ind_1' `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> (k = k') -> Type)
  (q : Q k (reflexivity k) 1 % path)
  : phomotopy_ind' Q q k (reflexivity k) (path_pforall (reflexivity k)) (1 % path)
  = transport (Q k (reflexivity k)) path_pforall_1^ q.
Proof.
  srapply phomotopy_ind_1.
Defined.

(** ** Operations on equivalences needed to make pType a wild category with equivalences *)

(** The inverse equivalence of a pointed equivalence is again a pointed equivalence *)
Definition pequiv_inverse {A B} (f : A <~>* B) : B <~>* A.
Proof.
  snrapply Build_pEquiv.
  1: apply (Build_pMap _ _ f^-1).
  1: apply moveR_equiv_V; symmetry; apply point_eq.
  exact _.
Defined.

(* A pointed equivalence is a section of its inverse *)
Definition peissect {A B : pType} (f : A <~>* B)
  : (pequiv_inverse f) o* f ==* pmap_idmap. 
Proof.
  srefine (Build_pHomotopy _ _).
  1: apply (eissect f). 
  simpl. unfold moveR_equiv_V.
  pointed_reduce.
  symmetry.
  refine (concat_p1 _ @ concat_1p _ @ concat_1p _).
Defined.

(* A pointed equivalence is a retraction of its inverse *)
Definition peisretr {A B : pType} (f : A <~>* B)
  : f o* (pequiv_inverse f) ==* pmap_idmap.
Proof.
  srefine (Build_pHomotopy _ _).
  1: apply (eisretr f).
  pointed_reduce.
  unfold moveR_equiv_V.
  refine (eisadj f _ @ _).
  symmetry.
  exact (concat_p1 _ @ concat_p1 _ @ ap _ (concat_1p _)).
Defined.

(** Univalence for pointed types *)
Definition equiv_path_ptype `{Univalence} (A B : pType) : A <~>* B <~> A = B.
Proof.
  destruct A as [A a], B as [B b].
  refine (equiv_ap issig_ptype (A;a) (B;b) oE _).
  refine (equiv_path_sigma _ _ _ oE _).
  refine (_ oE (issig_pequiv' _ _)^-1); simpl.
  refine (equiv_functor_sigma' (equiv_path_universe A B) _); intros f.
  apply equiv_concat_l.
  apply transport_path_universe.
Defined.

Definition path_ptype `{Univalence} {A B : pType} : (A <~>* B) -> A = B
  := equiv_path_ptype A B.

Definition pequiv_path {A B : pType} : (A = B) -> (A <~>* B).
Proof.
  intros p; apply (ap issig_ptype^-1) in p.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (equiv_path A B p..1) p..2) _).
Defined.

(** Two pointed equivalences are equal if their underlying pointed functions are pointed homotopic. *)
Definition equiv_path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) <~> (f = g).
Proof.
  transitivity ((issig_pequiv A B)^-1 f = (issig_pequiv A B)^-1 g).
  - refine (equiv_path_sigma_hprop _ _ oE _).
    apply (equiv_path_pforall f g).
  - symmetry; exact (equiv_ap' (issig_pequiv A B)^-1 f g).
Defined.

Definition path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) -> (f = g)
  := fun p => equiv_path_pequiv f g p.

(** Pointed types of pointed maps *)

(** A family of pointed types gives rise to a [pFam]. *)
Definition pointed_fam {A : pType} (B : A -> pType) : pFam A
  := (pointed_type o B; point (B (point A))).

(** The section of a family of pointed types *)
Definition point_pforall {A : pType} (B : A -> pType) : pForall A (pointed_fam B)
  := Build_pForall A (pointed_fam B) (fun x => point (B x)) 1.

(** The pointed type of pointed maps. For dependent pointed maps we need a family of pointed types, not just a family of types with a point over the basepoint of [A]. *)
Definition ppForall (A : pType) (B : A -> pType) : pType
  := Build_pType (pForall A (pointed_fam B)) (point_pforall B).

Definition ppMap (A B : pType) : pType
  := ppForall A (fun _ => B).

Infix "->**" := ppMap : pointed_scope.
Notation "'ppforall'  x .. y , P"
  := (ppForall _ (fun x => .. (ppForall _ (fun y => P)) ..))
     (at level 200, x binder, y binder, right associativity)
     : pointed_scope.

(** ** 1-categorical properties of [pForall]. *)
(** TODO: remove funext *)

Definition phomotopy_postwhisker `{Funext} {A : pType} {P : pFam A}
  {f g h : pForall A P} {p p' : f ==* g} (r : p ==* p') (q : g ==* h)
  : p @* q ==* p' @* q.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => whiskerR (r x) (q x)).
  revert p' r. srapply phomotopy_ind.
  revert h q. srapply phomotopy_ind.
  revert g p. srapply phomotopy_ind.
  pointed_reduce. reflexivity.
Defined.

Definition phomotopy_prewhisker `{Funext} {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f ==* g) {q q' : g ==* h} (s : q ==* q')
  : p @* q ==* p @* q'.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => whiskerL (p x) (s x)).
  revert q' s. srapply phomotopy_ind.
  revert h q. srapply phomotopy_ind.
  revert g p. srapply phomotopy_ind.
  pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_assoc `{Funext} {A : pType} {P : pFam A}
  {f g h k : pForall A P} (p : f ==* g) (q : g ==* h) (r : h ==* k)
  : p @* (q @* r) ==* (p @* q) @* r.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => concat_p_pp (p x) (q x) (r x)).
  revert k r. srapply phomotopy_ind.
  revert h q. srapply phomotopy_ind.
  revert g p. srapply phomotopy_ind.
  pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_p1 {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* reflexivity g ==* p.
Proof.
  srapply Build_pHomotopy.
  1: intro; apply concat_p1.
  pointed_reduce.
  rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _).
  clear H. intros H. destruct H.
  generalize (p point); generalize (g point).
  intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_compose_1p {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : reflexivity f @* p ==* p.
Proof.
  srapply Build_pHomotopy.
  + intro x. apply concat_1p.
  + pointed_reduce.
    rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _).
    clear H. intros H. destruct H.
    generalize (p point). generalize (g point).
    intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_compose_pV `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* p ^* ==* phomotopy_reflexive f.
Proof.
  srapply Build_pHomotopy.
  + intro x. apply concat_pV.
  + revert g p. srapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_Vp `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p ^* @* p ==* phomotopy_reflexive g.
Proof.
  srapply Build_pHomotopy.
  + intro x. apply concat_Vp.
  + revert g p. srapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

(** ** The pointed category structure of [pType] *)

(** The constant (zero) map *)
Definition pconst {A B : pType} : A ->* B
  := point_pforall (fun _ => B).

Lemma pmap_punit_pconst {A : pType} (f : A ->* pUnit) : f ==* pconst.
Proof.
  srapply Build_pHomotopy.
  1: intro; apply path_unit.
  apply path_contr.
Defined.

Lemma punit_pmap_pconst {A : pType} (f : pUnit ->* A) : f ==* pconst.
Proof.
  srapply Build_pHomotopy.
  1: intros []; exact (point_eq f).
  exact (concat_p1 _)^.
Defined.

(** * pType as a wild category *)

(** pType is a graph *)
Global Instance isgraph_ptype : IsGraph pType
  := Build_IsGraph pType (fun X Y => X ->* Y).

(** pType is a 0-coherent 1-category *)
Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType _ (@pmap_idmap) (@pmap_compose).

(** pForall is a graph *)
Global Instance isgraph_pforall (A : pType) (P : pFam A) : IsGraph (pForall A P)
  := Build_IsGraph _ pHomotopy.

(** pForall is a 0-coherent 1-category *)
Global Instance is01cat_pforall (A : pType) (P : pFam A) : Is01Cat (pForall A P).
Proof.
  econstructor.
  - exact phomotopy_reflexive.
  - intros a b c f g. exact (phomotopy_transitive _ _ _ g f).
Defined.

(** pForall is a 0-coherent 1-groupoid *)
Global Instance is0gpd_pforall (A : pType) (P : pFam A) : Is0Gpd (pForall A P).
Proof.
  srapply Build_Is0Gpd. intros ? ? h. exact (phomotopy_symmetric _ _ h).
Defined.

(** pType is a 1-coherent 1-category *)
Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  econstructor.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_postwhisker; assumption.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_prewhisker; assumption.
  - intros ? ? ? ? f g h; exact (pmap_compose_assoc h g f).
  - intros ? ? f; exact (pmap_postcompose_idmap f).
  - intros ? ? f; exact (pmap_precompose_idmap f).
Defined.

(** Under funext, pType has morphism extensionality *)
Global Instance hasmorext_ptype `{Funext} : HasMorExt pType.
Proof.
  srapply Build_HasMorExt; intros A B f g.
  refine (isequiv_homotopic (equiv_path_pforall f g)^-1%equiv _).
  intros []; reflexivity.
Defined.

(** pType has equivalences *)
Global Instance hasequivs_ptype : HasEquivs pType.
Proof.
  srapply (Build_HasEquivs _ _ _ _ pEquiv (fun A B f => IsEquiv f));
    intros A B f; cbn; intros.
  - exact f.
  - exact _.
  - exact (Build_pEquiv _ _ f _).
  - reflexivity.
  - exact (pequiv_inverse f).
  - apply peissect.
  - cbn. refine (peisretr f).
  - rapply (isequiv_adjointify f g).
    + intros x; exact (r x).
    + intros x; exact (s x).
Defined.

(** TODO: finish *)
(** pType is a univalent 1-coherent 1-category *)
Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
  refine (isequiv_homotopic (equiv_path_ptype A B)^-1 % equiv _).
  intros []; apply path_pequiv.
  srefine (Build_pHomotopy _ _).
  - intros x; reflexivity.
  - (* Some messy path algebra here. *)
Abort.

(** pType is a pointed category *)
Global Instance ispointedcat_ptype : IsPointedCat pType.
Proof.
  srapply Build_IsPointedCat.
  + exact pUnit.
  + intro A.
    exists pconst.
    exact punit_pmap_pconst.
  + intro B.
    exists pconst.
    exact pmap_punit_pconst.
Defined.

(** The constant map is definitionally equal to the zero_morphism of a pointed category *)
Definition path_zero_morphism_pconst (A B : pType)
  : (@pconst A B) = zero_morphism := idpath.

(** pForall is a 1-category *)
Global Instance is1cat_pforall `{Funext} (A : pType) (P : pFam A) : Is1Cat (pForall A P).
Proof.
  econstructor.
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_postwhisker s p).
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_prewhisker p s).
  - intros ? ? ? ? p q r. simpl. exact (phomotopy_compose_assoc p q r).
  - intros ? ? p; exact (phomotopy_compose_p1 p).
  - intros ? ? p; exact (phomotopy_compose_1p p).
Defined.

(** pForall is a 1-groupoid *)
Global Instance is1gpd_pforall `{Funext} (A : pType) (P : pFam A) : Is1Gpd (pForall A P).
Proof.
  econstructor.
  + intros ? ? p. exact (phomotopy_compose_pV p).
  + intros ? ? p. exact (phomotopy_compose_Vp p).
Defined.

(** The forgetful map from pType to Type is a 0-functor *)
Global Instance is0functor_pointed_type : Is0Functor pointed_type.
Proof.
  apply Build_Is0Functor. intros. exact f.
Defined.

(** The forgetful map from pType to Type is a 1-functor *)
Global Instance is1functor_pointed_type : Is1Functor pointed_type.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact h.
  + intros. reflexivity.
  + intros. reflexivity.
Defined.
