Require Import ssreflect ssrfun ssrbool.
Require Import Paths Fibrations Contractible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.

(* assia : it proves convenient to import also Cyril's alternate constructors *)
(* of inhabitants of a hfiber *)

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

Definition hfiber_def {A B} (f : A -> B) (y : B) 
           (x : A) (Hx : f x = y) : hfiber f y := exist (fun x => f x = _) _ Hx.

(* nice constructors for elements of the preimage: *)

(* If (Hx : f x = y), the element of the fiber (x, Hx) *)
Notation Hfiber f Hx := (@hfiber_def _ _ f _ _ Hx).

(* The element (f x, 1) of the fiber above f x *)
Notation in_hfiber f x := (@hfiber_def _ _ f _ x (erefl _)).

Lemma hfiberP {A B} (f : A -> B) (y : B) (x : hfiber f y) : f (projT1 x) = y.
Proof. by case: x. Qed.

(* We diverge from the original Equivalence.v file by defining is_equiv *)
(* what was previously called adjoint_equiv. We bet it should prove more*)
(* efficient as an interface because it exposes the inverse of the *)
(* equivalence as an element of the signature, which we can provide *)
(* by hand or built generically at our convenience. *)

(* Infrastructure is really absent for the moment...*)
Record equiv A B := Equiv {
  equiv_fun :> A -> B ;
  equiv_adjoint : B -> A ;
  equiv_section : cancel equiv_adjoint equiv_fun; 
  equiv_retraction : cancel equiv_fun equiv_adjoint;
  equiv_coh : forall x, equiv_section (equiv_fun x) = resp equiv_fun (equiv_retraction x)
}.

Delimit Scope equiv_scope with equiv.

Notation "A <~> B" := (equiv A B) (at level 85) : equiv_scope.

Local Open Scope equiv_scope.

Definition equiv_clone A B := 
  fun (f : A -> B) (ef : A <~> B) & (f = ef :> (A -> B)) => ef.

Notation "[ 'equiv' 'of' f ]" := (@equiv_clone _ _ f _ (erefl _))
  (at level 0, format "[ 'equiv'  'of'  f ]") : form_scope.


(* Warning : in ssreflect libs, bijective means the constructive existence of a *)
(* function g such that cancel f g and cancel g f. Otherwise said, *)
(* bijective is what is called hequiv in the original Equivalence.v file. *)
(* Hence the folloing lemma bij_is_equiv is the previous adjointify. *)

(* We first define how to correct a cancel operation so that it satifies the*)
(* coherence condition wrt the application of functions on paths *)
Definition adjointify {A B}(f : A -> B) g (fK : cancel f g)(gK : cancel g f) := 
   fun a => (resp g (resp f (fK a))^-1) * (resp g (gK (f a))) * (fK a).

(* Definition alt_adjointify {A B}(f : A -> B) g (fK : cancel f g)(gK : cancel g f) :=  *)
(*   fun a => (g`_* (gK (f a))) ^ fK. *)

(* Lemma alt_adjointifyP A B (f : A -> B) g  *)
(*   (fK : cancel f g)(gK : cancel g f)(fK' := alt_adjointify fK gK) a : *)
(*    gK (f a) = f`_* (fK' a). *)
(* Proof. *)
(* rewrite /fK' /alt_adjointify. *)

(* rewrite -resp_eqp. *)

(* pose gKV : id =1 f \o g :=  (fun x => (gK x)^-1). *)
(*  rewrite  !resppM !(conj_canV gKV) -(conjpM gKV). conjpE mulpK mulpVK invpK. *)
(* Qed. *)

Lemma adjointifyP A B (f : A -> B) g 
  (fK : cancel f g)(gK : cancel g f)(fK' := adjointify fK gK) a :
   gK (f a) = f`_* (fK' a).
Proof.
pose gKV : id =1 f \o g :=  (fun x => (gK x)^-1).
rewrite  !resppM.
About conj_canV.
rewrite !(conj_canV gKV).
rewrite -(conjpM gKV). 
rewrite conjpE.
rewrite mulpK.
rewrite mulpVK.
by rewrite invpK.
Qed.

(* A function whose fibers are all contractible *)
(* This was the main definition taken in the original Equivalence.v *)
(* I should probably change its name now *)
Definition is_equiv {A B} (e : A -> B) := forall y : B, is_contr (hfiber e y).

Canonical equiv_refl A : A <~> A := @Equiv _ _ idfun idfun
  (fun _ => erefl) (fun _ => erefl) (fun _ => erefl).

(* And now we prove that we can get an equivalence from a bijection *)
Definition can2_equiv A B (h1 : A -> B)(h2 : B -> A)(h1K : cancel h1 h2)
  (h2K : cancel h2 h1) : A <~> B := Equiv (adjointifyP h1K h2K).

Section EquivTheory.

Variables (A B : Type).
Variable (f : A <~> B).


(* An equivalence in the main sens is an equivalence in wrt to the contractible
   fibers definitions.*)
Lemma equiv_is_equiv : is_equiv f.
Proof.
move=> b; exists (Hfiber f (equiv_section f b)).
case=> a; case: _ / => {b}; rewrite (equiv_coh f).
by case (equiv_retraction f a).
Qed.

Definition inverse := nosimpl (@equiv_adjoint _ _ f).
Definition inverse_of (phf : phantom (A -> B) f) := inverse.
Local Notation "f ^-1" := (inverse_of (@Phantom (_ -> _) f)).

(* Lemma hfiber_eq x y : f x = y -> pr1 {elt hfiber f y} = x. *)
(* Proof. by move=> Hx; rewrite -[x]/(pr1 (Hfiber f Hx)) !hContrE. Qed. *)

Definition equivK : cancel f f^-1 := @equiv_retraction _ _ f.
Definition inverseK : cancel f^-1 f := @equiv_section _ _ f.

(* is_equiv implies bijective *)
Definition equiv_bij := Bijective equivK inverseK.

Canonical equiv_sym : (B <~> A) := @can2_equiv _ _ f^-1 f inverseK equivK.

End EquivTheory.
Notation "f ^-1" := (@inverse_of _ _ _ (@Phantom (_ -> _) f)) : equiv_scope.

Lemma inverseKE (A B : Type) (f : A <~> B) : (f^-1)^-1 = f. Proof. by []. Qed.

Section IsEquivEquiv.
Variables (A B : Type) (f : A -> B) (f_is_equiv : is_equiv f).

(*Canonical f_is_equiv_hContr b := ContrType _ (f_is_equiv b).  *)
Definition is_equiv_inverse (b : B) : A := pr1 (pr1 (f_is_equiv b)). 

Lemma is_equiv_directK : cancel f is_equiv_inverse.
Proof.
move=> x; rewrite /is_equiv_inverse.
by case: f_is_equiv => u /= /(_ (in_hfiber f x)) <-.
Qed.

Lemma is_equiv_inverseK : cancel is_equiv_inverse f.
Proof.
by move=> x; rewrite /is_equiv_inverse; case: f_is_equiv => [] []. 
Qed.

Definition is_equiv_equiv := can2_equiv is_equiv_directK is_equiv_inverseK.

End IsEquivEquiv.

Definition to_unit {A} (x : A) : unit := tt.

Section EquivUnit.
Variable A : hContr.

Lemma to_unitK : cancel (@to_unit A) (fun _ => {elt A}). 
Proof. by move=> x /=; rewrite hContrE. Qed.

Lemma to_unitVK : cancel (fun _ => {elt A}) (@to_unit A). Proof. by case. Qed.

Canonical equiv_unit : A <~> unit := can2_equiv to_unitK to_unitVK.

End EquivUnit.

Lemma equiv_contr_is_contr (A : hContr) B : A <~> B -> is_contr B.
Proof.
move=> f; exists (f {elt A}) => b.
by apply: (canRL (inverseK _)); rewrite hContrE.
Qed.

Lemma contr_equiv_is_contr A (B : hContr) : A <~> B -> is_contr A.
Proof.
move=> f; exists (inverse f {elt B}) => a.
by apply: (canRL (equivK _)); rewrite hContrE.
Qed.

Definition to_hContr (A : Type) (B : hContr) of A := {elt B}.

Lemma to_hContrK (A B : hContr) : cancel (@to_hContr A B) (@to_hContr _ _).
Proof. by move=> x; rewrite !hContrE. Qed.

Canonical equiv_to_hContr (A B : hContr) :=
  can2_equiv (@to_hContrK A B) (@to_hContrK B A).

Section EquivTransport.
Variables (T : Type).

(* TODO: put the LHS of # in path_scope *)
Definition transport_backward (x y : T) (P : T -> Type)
  (p : x = y) (py : P y) : P x := (p^-1)%path # py.

Lemma transportK (x y : T) (P : T -> Type) p :
  cancel (transport P p) (@transport_backward x y P p).
Proof. by case: _ / p. Qed.

Lemma transport_backwardK (x y : T) (P : T -> Type) p :
  cancel (@transport_backward x y P p) (transport P p).
Proof. by case: _ / p. Qed.

Canonical equiv_transport (x y : T) (P : T -> Type) p : P x <~> P y :=
  can2_equiv (transportK p) (@transport_backwardK x y P p).

End EquivTransport.

Lemma compA A B C D (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. reflexivity. Qed.

Section Diagonal.
Context {A : Type}.

Definition diag_sq := {xy : A * A & xy.1 = xy.2}.

Definition Diag_sq {x y} (h : x = y) : diag_sq := existT _ (x, y) h.

Definition diag_pi1 (aa : diag_sq) : A := (pr1 aa).1.
Definition diag_pi2 (aa : diag_sq) : A := (pr1 aa).2.
Definition to_diag (a : A) : diag_sq := exist _ (a, a) (erefl _).

Lemma diag_pi1K : cancel to_diag diag_pi1. Proof. by []. Qed.
Lemma diag_pi2K : cancel to_diag diag_pi2. Proof. by []. Qed.
Lemma to_diagK1 : cancel diag_pi1 to_diag.
Proof. by move=> [[x1 x2] /=]; case: _ /. Qed.
Lemma to_diagK2 : cancel diag_pi2 to_diag.
Proof. by move=> [[x1 x2] /=]; case: _ /. Qed.

Canonical diag_sq_id1 : diag_sq <~> A := can2_equiv to_diagK1 diag_pi1K.
Canonical diag_sq_id2 : diag_sq <~> A := can2_equiv to_diagK2 diag_pi2K.


End Diagonal.

(* This does not rely on univalence... *)

(* Definition equiv_inj A B (e : A <~> B) : injective e := can_inj (equivK [equiv of e]). *)

Notation equiv_inj e := (can_inj (equivK [equiv of e])).

Definition eq_equiv (U V : Type) (p : U = V) : U <~> V := p # (equiv_refl U).

Implicit Arguments eq_equiv [[U] [V]].

Definition univalent U V := is_equiv (@eq_equiv U V).

Module UnivalenceAxiom.

Section UnivalenceAxiom.

Variable univalence : forall U V, univalent U V.

Canonical eq_equiv_equiv U V := @is_equiv_equiv _ _ (@eq_equiv U V) (@univalence U V).

(* Since there is no elimination principle on the (inductive) type equiv, we*)
(* prove the one which makes sense. Because of the debatable choice made by *)
(* Coq in order to find the elimination scheme used by the elim tactic, the *)
(* choice of this _rect postfixed name makes this scheme the default one *)
(* for elimination on an object of type equiv. See the proof of compK for *)
(* an example. *)

Lemma equiv_rect (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_refl T)) -> (forall U V (e : U <~> V), P U V e).
Proof.
move=> PTT U V f; have <- /= := inverseK [equiv of eq_equiv] f.
by case: _ /(eq_equiv^-1 f) => /=.
Qed.

Definition compV A B C (e : A <~> B) (h : C -> B) : C -> A := e^-1 \o h.

Lemma compK A B C (e : A <~> B) : cancel (comp e) (@compV _ _ C e).
Proof. by elim: e. Qed.

Lemma compVK A B C (e : A <~> B) : cancel (@compV _ _ C e) (comp e).
Proof. by elim: e. Qed.

Canonical equiv_comp A B C (e : A <~> B) : (C -> A) <~> (C -> B) :=
  can2_equiv (@compK _ _ C e) (@compVK _ _ C e).

Definition precomp (X X' Y : Type) (f : X -> X') : (X' -> Y) -> (X -> Y) := comp^~ f.
Definition precompV A B C (e : A <~> B) (h : A -> C) : B -> C := h \o e^-1.

Lemma precompK A B C (e : A <~> B) : cancel (precomp e) (@precompV _ _ C e).
Proof. by elim: e. Qed.

Lemma precompVK A B C (e : A <~> B) : cancel (@precompV _ _ C e) (precomp e).
Proof. by elim: e. Qed.

Canonical equiv_precomp A B C (e : A <~> B) : (C -> A) <~> (C -> B) :=
  can2_equiv (@compK _ _ C e) (@compVK _ _ C e).

Lemma comp_equivV A B (e : A <~> B) : e \o e^-1 = id.
Proof. by elim: e. Qed.

Lemma comp_Vequiv A B (e : A <~> B) : e^-1 \o e = id.
Proof. by elim: e. Qed.

Lemma  comp_inverseK A B C (e : A <~> B) (f : C -> B) : e \o (e^-1 \o f) = f.
Proof. by elim: e f. Qed.

Lemma  comp_equivK A B C (e : A <~> B) (f : C -> A) : e^-1 \o (e \o f) = f.
Proof. by elim: e f. Qed.

Lemma  precomp_inverseK A B C (e : A <~> B) (f : B -> C) : (f \o e) \o e^-1 = f.
Proof. by elim: e f. Qed.

Lemma  precomp_equivK A B C (e : A <~> B) (f : A -> C) : (f \o e^-1) \o e = f.
Proof. by elim: e f. Qed.

Lemma diag_pi12 A : @diag_pi1 A = diag_pi2.
Proof. by rewrite -[RHS](precomp_equivK [equiv of diag_pi1]). Qed.

(* Proof that univalence -> fun ext *)
Lemma funext (X Y : Type)  (f g : X -> Y) : f =1 g -> f = g.
Proof.
move=> eq_fg; pose fg x : diag_sq  := Diag_sq (eq_fg x).
by have: diag_pi1 \o fg = diag_pi2 \o fg by rewrite diag_pi12.
Qed.

(* The goal here is to show that UIP does _not_ hold when we have univalence *)
Canonical equiv_negb : bool <~> bool :=
  @can2_equiv _ _ negb _ negbK negbK.

Lemma not_eq_negb_id : (eq_equiv^-1 [equiv of idfun]) <> (eq_equiv^-1 [equiv of negb]).
Proof.
move => eqN1. (* bug? why does move/(equiv_inj _) does not work? *)
by have /(congr1 (fun f : _ <~> _ => f true)) := equiv_inj _ eqN1.
Qed.

(* This means that bool = bool is not contractible *)
Lemma niscontr_eqbool : ~ is_contr (bool = bool :> Type).
Proof.
case=> f Hf; have := Hf (eq_equiv^-1 [equiv of idfun]).
by rewrite -(Hf (eq_equiv^-1 [equiv of negb])); apply: not_eq_negb_id.
Qed.

(* Uniqueness of identity proofs *)
Definition UIP := forall U (a b : U) (p q : a = b :> U), p = q.

(* As we have two _different_ proofs that "bool = bool" UIP cannot hold *)
Lemma UIP_false : ~ UIP.
Proof. by move => *; apply: not_eq_negb_id. Qed.

(* As we have
      Eq_rect_eq <-> Eq_dep_eq <-> UIP <-> UIP_refl <-> K
   This means that all of them are incompatible with univalence *)


End UnivalenceAxiom.
End UnivalenceAxiom.
