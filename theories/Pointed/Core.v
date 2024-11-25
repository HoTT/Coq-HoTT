Require Import Basics Types.
Require Import Homotopy.IdentitySystems.
Require Import WildCat.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse.
Require Import Extensions.

Local Set Polymorphic Inductive Cumulativity.

Declare Scope pointed_scope.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** ** Pointed Types *)

Notation "'pt'" := (point _) : pointed_scope.
Notation "[ X , x ]" := (Build_pType X x) : pointed_scope.

(** The unit type is pointed *)
Global Instance ispointed_unit : IsPointed Unit := tt.

(** The Unit pType *)
Definition pUnit : pType := [Unit, tt].

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sig B)
  := (point A; point (B (point A))).

(** A product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** We override the notation for products in pointed_scope *)
Notation "X * Y" := ([X * Y, ispointed_prod]) : pointed_scope.

(** A pointed type family consists of a type family over a pointed type and a section of that family at the basepoint. By making this a Record, it has one fewer universe variable, and is cumulative. We declare [pfam_pr1] to be a coercion [pFam >-> Funclass]. *)
Record pFam (A : pType) := { pfam_pr1 :> A -> Type; dpoint : pfam_pr1 (point A)}.

Arguments Build_pFam {A} _ _.
Arguments pfam_pr1 {A} P : rename.
Arguments dpoint {A} P : rename.

(** The constant pointed family *)
Definition pfam_const {A : pType} (B : pType) : pFam A
  := Build_pFam (fun _ => pointed_type B) (point B).

(** [IsTrunc] for a pointed type family *)
Class IsTrunc_pFam n {A} (P : pFam A)
  := trunc_pfam_is_trunc : forall x, IsTrunc n (P x).

(** Pointed dependent functions *)
Record pForall (A : pType) (P : pFam A) := {
  pointed_fun : forall x, P x ;
  dpoint_eq : pointed_fun (point A) = dpoint P ;
}.

Arguments dpoint_eq {A P} f : rename.
Arguments pointed_fun {A P} f : rename.
Coercion pointed_fun : pForall >-> Funclass.

(** ** Pointed functions *)

(** A pointed map is a map with a proof that it preserves the point. We define it as as a notation for a non-dependent version of [pForall]. *)
Notation "A ->* B" := (pForall A (pfam_const B)) : pointed_scope.

Definition Build_pMap (A B : pType) (f : A -> B) (p : f (point A) = point B)
  : A ->* B
  := Build_pForall A (pfam_const B) f p.

(** The [&] tells Coq to use the context to infer the later arguments (in this case, all of them). *)
Arguments Build_pMap & _ _ _ _.

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

(** A pointed homotopy is a homotopy with a proof that the presevation paths agree. We define it instead as a special case of a [pForall]. This means that we can define pointed homotopies between pointed homotopies. *)
Definition pfam_phomotopy {A : pType} {P : pFam A} (f g : pForall A P) : pFam A
  := Build_pFam (fun x => f x = g x) (dpoint_eq f @ (dpoint_eq g)^).

Definition pHomotopy {A : pType} {P : pFam A} (f g : pForall A P)
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

(** A pointed equivalence is a pointed map and a proof that it is an equivalence *)
Record pEquiv (A B : pType) := {
  pointed_equiv_fun : pForall A (pfam_const B) ;
  pointed_isequiv : IsEquiv pointed_equiv_fun ;
}.

(** TODO: It might be better behaved to define pEquiv as an equivalence and a proof that this equivalence is pointed. In pEquiv.v we have another constructor Build_pEquiv' which coq can infer faster than Build_pEquiv. *)

Infix "<~>*" := pEquiv : pointed_scope.

(** Note: because we define pMap as a special case of pForall, we must declare all coercions into pForall, *not* into pMap. *)
Coercion pointed_equiv_fun : pEquiv >-> pForall.
Global Existing Instance pointed_isequiv.

Coercion pointed_equiv_equiv {A B} (f : A <~>* B)
  : A <~> B := Build_Equiv A B f _.

(** The pointed identity is a pointed equivalence *)
Definition pequiv_pmap_idmap {A} : A <~>* A
  := Build_pEquiv _ _ pmap_idmap _.

(** Pointed sigma types *)
Definition psigma {A : pType} (P : pFam A) : pType
  := [sig P, (point A; dpoint P)].

(** *** Pointed products *)

(** Pointed pi types; note that the domain is not pointed *)
Definition pproduct {A : Type} (F : A -> pType) : pType
  := [forall (a : A), pointed_type (F a), ispointed_type o F].

Definition pproduct_corec `{Funext} {A : Type} (F : A -> pType)
  (X : pType) (f : forall a, X ->* F a)
  : X ->* pproduct F.
Proof.
  snrapply Build_pMap.
  - intros x a.
    exact (f a x).
  - cbn.
    funext a.
    apply point_eq.
Defined.

Definition pproduct_proj {A : Type} {F : A -> pType} (a : A)
  : pproduct F ->* F a.
Proof.
  snrapply Build_pMap.
  - intros x.
    exact (x a).
  - reflexivity.
Defined.

(** The projections from a pointed product are pointed maps. *)
Definition pfst {A B : pType} : A * B ->* A
  := Build_pMap (A * B) A fst idpath.

Definition psnd {A B : pType} : A * B ->* B
  := Build_pMap (A * B) B snd idpath.

Definition pprod_corec {X Y} (Z : pType) (f : Z ->* X) (g : Z ->* Y)
  : Z ->* (X * Y)
  := Build_pMap Z (X * Y) (fun z => (f z, g z))
      (path_prod' (point_eq _) (point_eq _)).

Definition pprod_corec_beta_fst {X Y} (Z : pType) (f : Z ->* X) (g : Z ->* Y)
  : pfst o* pprod_corec Z f g ==* f.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  apply moveL_pV.
  refine (concat_1p _ @ _^ @ (concat_p1 _)^).
  apply ap_fst_path_prod'.
Defined.

Definition pprod_corec_beta_snd {X Y} (Z : pType) (f : Z ->* X) (g : Z ->* Y)
  : psnd o* pprod_corec Z f g ==* g.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  apply moveL_pV.
  refine (concat_1p _ @ _^ @ (concat_p1 _)^).
  apply ap_snd_path_prod'.
Defined.

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
    | _ ->* ?Y => let p := fresh in destruct Y as [Y ?], f as [f p]; cbn in *; destruct p; cbn
    end.

(** A general tactic to replace pointedness paths in a pForall with reflexivity.  Because it generalizes [f pt], it can usually only be applied once the function itself is not longer needed.  Compared to [pointed_reduce], an advantage is that the pointed types do not need to be destructed. *)
Ltac pelim f :=
  try match type of f with
    | pEquiv ?X ?Y => destruct f as [f ?iseq]; unfold pointed_fun in *
  end;
  destruct f as [f ?ptd];
  cbn in f, ptd |- *;
  match type of ptd with ?fpt = _ => generalize dependent fpt end;
  nrapply paths_ind_r;
  try clear f.

Tactic Notation "pelim" constr(x0) := pelim x0.
Tactic Notation "pelim" constr(x0) constr(x1) := pelim x0; pelim x1.
Tactic Notation "pelim" constr(x0) constr(x1) constr(x2) := pelim x0; pelim x1 x2.
Tactic Notation "pelim" constr(x0) constr(x1) constr(x2) constr(x3) := pelim x0; pelim x1 x2 x3.
Tactic Notation "pelim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) := pelim x0; pelim x1 x2 x3 x4.
Tactic Notation "pelim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) := pelim x0; pelim x1 x2 x3 x4 x5.
Tactic Notation "pelim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) := pelim x0; pelim x1 x2 x3 x4 x5 x6.

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

(** pForall can also be described as a type of extensions. *)
Definition equiv_extension_along_pforall `{Funext} {A : pType} (P : pFam A)
  : ExtensionAlong@{Set _ _ _} (unit_name (point A)) P (unit_name (dpoint P)) <~> pForall A P.
Proof.
  unfold ExtensionAlong.
  refine (issig_pforall A P oE _).
  apply equiv_functor_sigma_id; intro s.
  symmetry; apply equiv_unit_rec.
Defined.

(** This is [equiv_prod_coind] for pointed families. *)
Definition equiv_pprod_coind {A : pType} (P Q : pFam A)
  : (pForall A P * pForall A Q) <~>
      (pForall A (Build_pFam (fun a => prod (P a) (Q a)) (dpoint P, dpoint Q))).
Proof.
  transitivity {p : prod (forall a:A, P a) (forall a:A, Q a)
                    & prod (fst p _ = dpoint P) (snd p _ = dpoint Q)}.
  1: make_equiv.
  refine (issig_pforall _ _ oE _).
  srapply equiv_functor_sigma'.
  1: apply equiv_prod_coind.
  intro f; cbn.
  unfold prod_coind_uncurried.
  exact (equiv_path_prod (fst f _, snd f _) (dpoint P, dpoint Q)).
Defined.

Definition functor_pprod {A A' B B' : pType} (f : A ->* A') (g : B ->* B')
  : A * B ->* A' * B'.
Proof.
  snrapply Build_pMap.
  - exact (functor_prod f g).
  - apply path_prod; apply point_eq.
Defined.

(** [isequiv_functor_prod] applies, and is a Global Instance. *)
Definition equiv_functor_pprod {A A' B B' : pType} (f : A <~>* A') (g : B <~>* B')
  : A * B <~>* A' * B'
  := Build_pEquiv _ _ (functor_pprod f g) _.

(** ** Various operations with pointed homotopies *)

(** For the following three instances, the typeclass (e.g. [Reflexive]) requires a third universe variable, the maximum of the universe of [A] and the universe of the values of [P].  Because of this, in each case we first prove a version not mentioning the typeclass, which avoids a stray universe variable. *)

(** [pHomotopy] is a reflexive relation *)
Definition phomotopy_reflexive {A : pType} {P : pFam A} (f : pForall A P)
  : f ==* f
  := Build_pHomotopy (fun x => 1) (concat_pV _)^.

Global Instance phomotopy_reflexive' {A : pType} {P : pFam A}
  : Reflexive (@pHomotopy A P)
  := @phomotopy_reflexive A P.

(** [pHomotopy] is a symmetric relation *)
Definition phomotopy_symmetric {A P} {f g : pForall A P} (p : f ==* g)
  : g ==* f.
Proof.
  snrefine (Build_pHomotopy _ _); cbn.
  1: intros x; exact ((p x)^).
  by pelim p f g.
Defined.

Global Instance phomotopy_symmetric' {A P}
  : Symmetric (@pHomotopy A P)
  := @phomotopy_symmetric A P.

Notation "p ^*" := (phomotopy_symmetric p) : pointed_scope.

(** [pHomotopy] is a transitive relation *)
Definition phomotopy_transitive {A P} {f g h : pForall A P} (p : f ==* g) (q : g ==* h)
  : f ==* h.
Proof.
  snrefine (Build_pHomotopy (fun x => p x @ q x) _).
  nrefine (dpoint_eq p @@ dpoint_eq q @ concat_pp_p _ _ _ @ _).
  nrapply whiskerL; nrapply concat_V_pp.
Defined.

Global Instance phomotopy_transitive' {A P} : Transitive (@pHomotopy A P)
  := @phomotopy_transitive A P.

Notation "p @* q" := (phomotopy_transitive p q) : pointed_scope.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g)
  : h o* f ==* h o* g.
Proof.
  snrefine (Build_pHomotopy _ _); cbn.
  1: exact (fun x => ap h (p x)).
  by pelim p f g h.
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h)
  : g o* f ==* h o* f.
Proof.
  snrefine (Build_pHomotopy _ _); cbn.
  1: exact (fun x => p (f x)).
  by pelim f p g h.
Defined.

(** ** 1-categorical properties of [pType]. *)

(** Composition of pointed maps is associative up to pointed homotopy *)
Definition pmap_compose_assoc {A B C D : pType} (h : C ->* D)
  (g : B ->* C) (f : A ->* B)
  : (h o* g) o* f ==* h o* (g o* f).
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  by pelim f g h.
Defined.

(** precomposition of identity pointed map *)
Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap ==* f.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  by pelim f.
Defined.

(** postcomposition of identity pointed map *)
Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  snrapply Build_pHomotopy.
  1: reflexivity.
  by pelim f.
Defined.

(** ** 1-categorical properties of [pForall]. *)

Definition phomotopy_postwhisker {A : pType} {P : pFam A}
  {f g h : pForall A P} {p p' : f ==* g} (r : p ==* p') (q : g ==* h)
  : p @* q ==* p' @* q.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => whiskerR (r x) (q x)).
  by pelim q r p p' f g h.
Defined.

Definition phomotopy_prewhisker {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f ==* g) {q q' : g ==* h} (s : q ==* q')
  : p @* q ==* p @* q'.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => whiskerL (p x) (s x)).
  by pelim s q q' p f g h.
Defined.

Definition phomotopy_compose_assoc {A : pType} {P : pFam A}
  {f g h k : pForall A P} (p : f ==* g) (q : g ==* h) (r : h ==* k)
  : p @* (q @* r) ==* (p @* q) @* r.
Proof.
  snrapply Build_pHomotopy.
  1: exact (fun x => concat_p_pp (p x) (q x) (r x)).
  by pelim r q p f g h k.
Defined.

Definition phomotopy_compose_p1 {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* reflexivity g ==* p.
Proof.
  srapply Build_pHomotopy.
  1: intro; apply concat_p1.
  by pelim p f g.
Defined.

Definition phomotopy_compose_1p {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : reflexivity f @* p ==* p.
Proof.
  srapply Build_pHomotopy.
  1: intro x; apply concat_1p.
  by pelim p f g.
Defined.

Definition phomotopy_compose_pV {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* p ^* ==* phomotopy_reflexive f.
Proof.
  srapply Build_pHomotopy.
  1: intro x; apply concat_pV.
  by pelim p f g.
Defined.

Definition phomotopy_compose_Vp {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p ^* @* p ==* phomotopy_reflexive g.
Proof.
  srapply Build_pHomotopy.
  1: intro x; apply concat_Vp.
  by pelim p f g.
Defined.

(** ** The pointed category structure of [pType] *)

(** Pointed types of pointed maps *)

(** A family of pointed types gives rise to a [pFam]. *)
Definition pointed_fam {A : pType} (B : A -> pType) : pFam A
  := Build_pFam (pointed_type o B) (point (B (point A))).

(** The section of a family of pointed types *)
Definition point_pforall {A : pType} (B : A -> pType) : pForall A (pointed_fam B)
  := Build_pForall A (pointed_fam B) (fun x => point (B x)) 1.

(** The pointed type of dependent pointed maps. Note that we need a family of pointed types, not just a family of types with a point over the basepoint of [A]. *)
Definition ppForall (A : pType) (B : A -> pType) : pType
  := [pForall A (pointed_fam B), point_pforall B].

Notation "'ppforall'  x .. y , P"
  := (ppForall _ (fun x => .. (ppForall _ (fun y => P)) ..))
     : pointed_scope.

(** The constant (zero) map *)
Definition pconst {A B : pType} : A ->* B
  := point_pforall (fun _ => B).

(** The pointed type of pointed maps.  This is a special case of [ppForall]. *)
Definition ppMap (A B : pType) : pType
  := [A ->* B, pconst].

Infix "->**" := ppMap : pointed_scope.

Lemma pmap_punit_pconst {A : pType} (f : A ->* pUnit) : pconst ==* f.
Proof.
  srapply Build_pHomotopy.
  1: intro; apply path_unit.
  apply path_contr.
Defined.

Lemma punit_pmap_pconst {A : pType} (f : pUnit ->* A) : pconst ==* f.
Proof.
  srapply Build_pHomotopy.
  1: intros []; exact (point_eq f)^.
  exact (concat_1p _)^.
Defined.

Global Instance contr_pmap_from_contr `{Funext} {A B : pType} `{C : Contr A}
  : Contr (A ->* B).
Proof.
  rapply (contr_equiv' { b : B & b = pt }).
  refine (issig_pmap A B oE _).
  exact (equiv_functor_sigma_pb (equiv_arrow_from_contr A B)^-1%equiv).
Defined.

(** * pType and pForall as wild categories *)

(** Note that the definitions for [pForall] are also used for the higher structure in [pType]. *)

(** pType is a graph *)
Global Instance isgraph_ptype : IsGraph pType
  := Build_IsGraph pType (fun X Y => X ->* Y).

(** pForall is a graph *)
Global Instance isgraph_pforall (A : pType) (P : pFam A)
  : IsGraph (pForall A P)
  := Build_IsGraph _ pHomotopy.

(** pType is a 0-coherent 1-category *)
Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType _ (@pmap_idmap) (@pmap_compose).

(** pForall is a 0-coherent 1-category *)
Global Instance is01cat_pforall (A : pType) (P : pFam A) : Is01Cat (pForall A P).
Proof.
  econstructor.
  - exact phomotopy_reflexive.
  - intros a b c f g. exact (g @* f).
Defined.

Global Instance is2graph_ptype : Is2Graph pType := fun f g => _.

Global Instance is2graph_pforall (A : pType) (P : pFam A)
  : Is2Graph (pForall A P)
  := fun f g => _.

(** pForall is a 0-coherent 1-groupoid *)
Global Instance is0gpd_pforall (A : pType) (P : pFam A) : Is0Gpd (pForall A P).
Proof.
  srapply Build_Is0Gpd. intros ? ? h. exact h^*.
Defined.

(** pType is a 1-coherent 1-category *)
Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  snrapply Build_Is1Cat'.
  1, 2: exact _.
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

(** pType is a pointed category *)
Global Instance ispointedcat_ptype : IsPointedCat pType.
Proof.
  snrapply Build_IsPointedCat.
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
Global Instance is1cat_pforall (A : pType) (P : pFam A) : Is1Cat (pForall A P) | 10.
Proof.
  snrapply Build_Is1Cat'.
  1, 2: exact _.
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_postwhisker s p).
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_prewhisker p s).
  - intros ? ? ? ? p q r. simpl. exact (phomotopy_compose_assoc p q r).
  - intros ? ? p; exact (phomotopy_compose_p1 p).
  - intros ? ? p; exact (phomotopy_compose_1p p).
Defined.

(** pForall is a 1-groupoid *)
Global Instance is1gpd_pforall (A : pType) (P : pFam A) : Is1Gpd (pForall A P) | 10.
Proof.
  econstructor.
  + intros ? ? p. exact (phomotopy_compose_pV p).
  + intros ? ? p. exact (phomotopy_compose_Vp p).
Defined.

Global Instance is3graph_ptype : Is3Graph pType
  := fun f g => is2graph_pforall _ _.

Global Instance is21cat_ptype : Is21Cat pType.
Proof.
  unshelve econstructor.
  - exact _.
  - intros A B C f; nrapply Build_Is1Functor.
    + intros g h p q r.
      srapply Build_pHomotopy.
      1: exact (fun _ => ap _ (r _)).
      by pelim r p q g h f.
    + intros g.
      srapply Build_pHomotopy.
      1: reflexivity.
      by pelim g f.
    + intros g h i p q.
      srapply Build_pHomotopy.
      1: cbn; exact (fun _ => ap_pp _ _ _).
      by pelim p q g h i f.
  - intros A B C f; nrapply Build_Is1Functor.
    + intros g h p q r.
      srapply Build_pHomotopy.
      1: intro; exact (r _).
      by pelim f r p q g h.
    + intros g.
      srapply Build_pHomotopy.
      1: reflexivity.
      by pelim f g.
    + intros g h i p q.
      srapply Build_pHomotopy.
      1: reflexivity.
      by pelim f p q i g h.
  - intros A B C f g h k p q.
    snrapply Build_pHomotopy.
    + intros x.
      exact (concat_Ap q _)^.
    + by pelim p f g q h k.
  - intros A B C D f g.
    snrapply Build_Is1Natural.
    intros r1 r2 s1.
    srapply Build_pHomotopy.
    1: exact (fun _ => concat_p1 _ @ (concat_1p _)^).
    by pelim f g s1 r1 r2.
  - intros A B C D f g.
    snrapply Build_Is1Natural.
    intros r1 r2 s1.
    srapply Build_pHomotopy.
    1: exact (fun _ => concat_p1 _ @ (concat_1p _)^).
    by pelim f s1 r1 r2 g.
  - intros A B C D f g.
    snrapply Build_Is1Natural.
    intros r1 r2 s1.
    srapply Build_pHomotopy.
    1: cbn; exact (fun _ => concat_p1 _ @ ap_compose _ _ _ @ (concat_1p _)^).
    by pelim s1 r1 r2 f g.
  - intros A B.
    snrapply Build_Is1Natural.
    intros r1 r2 s1.
    srapply Build_pHomotopy.
    1: exact (fun _ => concat_p1 _ @ ap_idmap _ @ (concat_1p _)^).
    by pelim s1 r1 r2.
  - intros A B.
    snrapply Build_Is1Natural.
    intros r1 r2 s1.
    srapply Build_pHomotopy.
    1: exact (fun _ => concat_p1 _ @ (concat_1p _)^).
    simpl; by pelim s1 r1 r2.
  - intros A B C D E f g h j.
    srapply Build_pHomotopy.
    1: reflexivity.
    by pelim f g h j.
  - intros A B C f g.
    srapply Build_pHomotopy.
    1: reflexivity.
    by pelim f g.
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

(** pType has binary products *)
Global Instance hasbinaryproducts_ptype : HasBinaryProducts pType.
Proof.
  intros X Y.
  snrapply Build_BinaryProduct.
  - exact (X * Y).
  - exact pfst.
  - exact psnd.
  - exact pprod_corec.
  - exact pprod_corec_beta_fst.
  - exact pprod_corec_beta_snd.
  - intros Z f g p q.
    simpl.
    snrapply Build_pHomotopy.
    { intros a.
      apply path_prod'; cbn.
      - exact (p a).
      - exact (q a). }
    simpl.
    by pelim p q f g.
Defined.

(** pType has I-indexed product. *)
Global Instance hasallproducts_ptype `{Funext} : HasAllProducts pType.
Proof.
  intros I x.
  snrapply Build_Product.
  - exact (pproduct x).
  - exact pproduct_proj. 
  - exact (pproduct_corec x).
  - intros Z f i.
    snrapply Build_pHomotopy.
    1: reflexivity.
    apply moveL_pV.
    apply equiv_1p_q1.
    exact (apD10_path_forall _ _ (fun a => point_eq (f a)) i)^.
  - intros Z f g p.
    snrapply Build_pHomotopy.
    1: intros z; funext i; apply p.
    cbn; apply moveR_equiv_V.
    funext i.
    rhs nrapply ap_pp.
    lhs nrapply (dpoint_eq (p i)).
    cbn; f_ap.
    + apply concat_p1.
    + rhs nrapply (ap_V _ (dpoint_eq g)).
      apply inverse2.
      apply concat_p1.
Defined.

(** Some higher homotopies *)

(** Horizontal composition of homotopies. *)
Notation "p @@* q" := (p $@@ q).

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

(** We note that the inverse of [path_pforall] computes definitionally on reflexivity, and hence [path_pforall] itself computes typally so. *)
Definition equiv_inverse_path_pforall_1 `{Funext} {A : pType} {P : pFam A} (f : pForall A P)
  : (equiv_path_pforall f f)^-1%equiv 1%path = reflexivity f
  := 1.

Definition path_pforall_1 `{Funext} {A : pType} {P : pFam A} {f : pForall A P}
  : equiv_path_pforall _ _ (reflexivity f) = 1%path
  := moveR_equiv_M _ _ (equiv_inverse_path_pforall_1 f)^.

(** Here is the inverse map without assuming funext *)
Definition phomotopy_path {A : pType} {P : pFam A} {f g : pForall A P}
  : (f = g) -> (f ==* g) := ltac:(by intros []).

(** And we prove that it agrees with the inverse of [equiv_path_pforall] *)
Definition path_equiv_path_pforall_phomotopy_path `{Funext} {A : pType}
  {P : pFam A} {f g : pForall A P}
  : phomotopy_path (f:=f) (g:=g) = (equiv_path_pforall f g)^-1%equiv
  := ltac:(by funext []).

(** TODO: The next few results could be proven for [GpdHom_path] in any WildCat. *)

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_p1.
Defined.

(** ** [phomotopy_path] respects 2-cells. *)
Definition phomotopy_path2 {A : pType} {P : pFam A}
  {f g : pForall A P} {p p' : f = g} (q : p = p')
  : phomotopy_path p ==* phomotopy_path p'.
Proof.
  induction q. reflexivity.
Defined.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V {A : pType} {P : pFam A}
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. exact gpd_rev_1.
Defined.

(** Since pointed homotopies are equivalent to equalities, we can act as if they are paths and define a path induction for them. *)
Definition phomotopy_ind `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> Type)
  (q : Q k (reflexivity k)) (k' : pForall A P)
  : forall (H : k ==* k'), Q k' H.
Proof.
  equiv_intro (equiv_path_pforall k k')^-1%equiv p.
  induction p.
  exact q.
Defined.

(** Sometimes you have a goal with both a pointed homotopy [H] and [path_pforall H].  This is an induction principle that allows us to replace both of them by reflexivity at the same time. *)
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

(** Every homotopy between pointed maps of sets is a pointed homotopy. *)
Definition phomotopy_homotopy_hset {X Y : pType} `{IsHSet Y} {f g : X ->* Y} (h : f == g)
  : f ==* g.
Proof.
  apply (Build_pHomotopy h).
  apply path_ishprop.
Defined.

(** Pointed homotopies in a set form an HProp. *)
Global Instance ishprop_phomotopy_hset `{Funext} {X Y : pType} `{IsHSet Y} (f g : X ->* Y)
  : IsHProp (f ==* g)
  := inO_equiv_inO' (O:=Tr (-1)) _ (issig_phomotopy f g).

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
Definition equiv_path_ptype `{Univalence} (A B : pType@{u}) : A <~>* B <~> A = B.
Proof.
  refine (equiv_path_from_contr A (fun C => A <~>* C) pequiv_pmap_idmap _ B).
  nrapply (contr_equiv' { X : Type@{u} & { f : A <~> X & {x : X & f pt = x} }}).
  1: make_equiv.
  rapply (contr_equiv' { X : Type@{u} &  A <~> X }).
  nrapply equiv_functor_sigma_id; intro X; symmetry.
  rapply equiv_sigma_contr.
  (** If you replace the type in the second line with { Xf : {X : Type & A <~> X} & {x : Xf.1 & Xf.2 pt = x} }, then the third line completes the proof, but that results in an extra universe variable. *)
Defined.

Definition path_ptype `{Univalence} {A B : pType} : (A <~>* B) -> A = B
  := equiv_path_ptype A B.

(** The inverse map can be defined without Univalence. *)
Definition pequiv_path {A B : pType} (p : A = B) : (A <~>* B)
  := match p with idpath => pequiv_pmap_idmap end.

(** This just confirms that it is definitionally the inverse map. *)
Definition pequiv_path_equiv_path_ptype_inverse `{Univalence} {A B : pType}
  : @pequiv_path A B = (equiv_path_ptype A B)^-1
  := idpath.

Global Instance isequiv_pequiv_path `{Univalence} {A B : pType}
  : IsEquiv (@pequiv_path A B)
  := isequiv_inverse (equiv_path_ptype A B).

(** Two pointed equivalences are equal if their underlying pointed functions are equal. This requires [Funext] for knowing that [IsEquiv] is an [HProp]. *)
Definition equiv_path_pequiv' `{Funext} {A B : pType} (f g : A <~>* B)
  : (f = g :> (A ->* B)) <~> (f = g :> (A <~>* B)).
Proof.
  refine ((equiv_ap' (issig_pequiv A B)^-1%equiv f g)^-1%equiv oE _); cbn.
  match goal with |- _ <~> ?F = ?G => exact (equiv_path_sigma_hprop F G) end.
Defined.

(** Two pointed equivalences are equal if their underlying pointed functions are pointed homotopic. *)
Definition equiv_path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) <~> (f = g)
  := equiv_path_pequiv' f g oE equiv_path_pforall f g.

Definition path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) -> (f = g)
  := equiv_path_pequiv f g.

Definition equiv_phomotopy_concat_l `{Funext} {A B : pType}
  (f g h : A ->* B) (K : g ==* f)
  : f ==* h <~> g ==* h.
Proof.
  refine ((equiv_path_pforall _ _)^-1%equiv oE _ oE equiv_path_pforall _ _).
  rapply equiv_concat_l.
  apply equiv_path_pforall.
  exact K.
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
  srapply (
    Build_HasEquivs _ _ _ _ _ pEquiv (fun A B f => IsEquiv f));
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

Global Instance hasmorext_core_ptype `{Funext} : HasMorExt (core pType).
Proof.
  rapply hasmorext_core.
  intros A B f g.
  snrapply isequiv_homotopic'.
  1: exact (equiv_path_pequiv' f g)^-1%equiv.
  by intros [].
Defined.

(** pType is a univalent 1-coherent 1-category *)
Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
  (* [cate_equiv_path] is almost definitionally equal to [pequiv_path].  Both are defined by path induction, sending [idpath A] to [id_cate A] and [pequiv_pmap_idmap A], respectively.  [id_cate A] is almost definitionally equal to [pequiv_pmap_idmap A], except that the former uses [catie_adjointify], so the adjoint law is different. However, the underlying pointed maps are definitionally equal. *)
  refine (isequiv_homotopic pequiv_path _).
  intros [].
  apply equiv_path_pequiv'.  (* Change to equality as pointed functions. *)
  reflexivity.
Defined.

(** The free base point added to a type. This is in fact a functor and left adjoint to the forgetful functor pType to Type. *)
Definition pointify (S : Type) : pType := [S + Unit, inr tt].

Global Instance is0functor_pointify : Is0Functor pointify.
Proof.
  apply Build_Is0Functor.
  intros A B f.
  srapply Build_pMap.
  1: exact (functor_sum f idmap).
  reflexivity.
Defined.

(** pointify is left adjoint to forgetting the basepoint in the following sense *)
Theorem equiv_pointify_map `{Funext} (A : Type) (X : pType)
  : (pointify A ->* X) <~> (A -> X).
Proof.
  snrapply equiv_adjointify.
  1: exact (fun f => f o inl).
  { intros f.
    snrapply Build_pMap.
    { intros [a|].
      1: exact (f a).
      exact pt. }
    reflexivity. }
  1: intro x; reflexivity.
  intros f.
  cbv.
  pointed_reduce.
  rapply equiv_path_pforall.
  snrapply Build_pHomotopy.
  1: by intros [a|[]].
  reflexivity.
Defined.

Lemma natequiv_pointify_r `{Funext} (A : Type)
  : NatEquiv (opyon (pointify A)) (opyon A o pointed_type).
Proof.
  snrapply Build_NatEquiv.
  1: rapply equiv_pointify_map.
  snrapply Build_Is1Natural.
  cbv; reflexivity.
Defined.

(** * Pointed categories give rise to pointed structures *)

(** Pointed categories have pointed hom sets *)
Definition pHom {A : Type} `{IsPointedCat A} (a1 a2 : A)
  := [Hom a1 a2, zero_morphism].

(** Pointed functors give pointed maps on morphisms *)
Definition pfmap {A B : Type} (F : A -> B)
  `{IsPointedCat A, IsPointedCat B, !HasEquivs B, !HasMorExt B}
  `{!Is0Functor F, !Is1Functor F, !IsPointedFunctor F}
  {a1 a2 : A}
  : pHom a1 a2 ->* pHom (F a1) (F a2).
Proof.
  snrapply Build_pMap.
  - exact (fmap F).
  - apply path_hom.
    snrapply fmap_zero_morphism; assumption.
Defined.
