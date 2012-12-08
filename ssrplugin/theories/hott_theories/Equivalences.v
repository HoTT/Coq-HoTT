Require Import ssreflect ssrfun ssrbool.
Require Import Paths Fibrations Contractible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.


(* We diverge from the original Equivalence.v file by defining is_equiv *)
(* what was previously called adjoint_equiv. We bet it should prove more*)
(* efficient as an interface because it exposes the inverse of the *)
(* equivalence as an element of the signature, which we can provide *)
(* by hand or built generically at our convenience. Hence this inverse can *)
(* be retrieved by the canonical structure lookup mechanism, which proves *)
(* very convenient in proofs.*)

Record equiv A B := Equiv {
  equiv_fun :> A -> B ;
  equiv_adjoint : B -> A ;
  equiv_section : cancel equiv_adjoint equiv_fun; 
  equiv_retraction : cancel equiv_fun equiv_adjoint;
  equiv_coh : forall x, 
    equiv_section (equiv_fun x) = resp equiv_fun (equiv_retraction x)
}.

(* Don't ask :-), but this is an ingredient for the notation below. *)
Definition equiv_clone A B := 
  fun (f : A -> B) (ef : equiv A B) & (f = ef :> (A -> B)) => ef.

(* Lookup notation to infer the structure of equiv declared as canonical on a *)
(* given f (f should be the equiv_fun of the candidate instance found in the *)
(* database.*)
Notation "[ 'equiv' 'of' f ]" := (@equiv_clone _ _ f _ (erefl _))
  (at level 0, format "[ 'equiv'  'of'  f ]") : form_scope.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

(* Infix notation, similar to what was in HoTT *)
Notation "A <~> B" := (equiv A B) (at level 85) : equiv_scope.


(* Canonical reflexivity of equiv *)
Canonical equiv_refl A : A <~> A := @Equiv _ _ idfun idfun
  (fun _ => erefl) (fun _ => erefl) (fun _ => erefl).

(* We first define how to correct a cancel operation so that it satifies the*)
(* coherence condition wrt the application of functions on paths *)

Definition adjointify {A B}(f : A -> B) g (fK : cancel f g)(gK : cancel g f) := 
   fun a => (g `_* (f `_* (fK a))^-1) * (resp g (gK (f a))) * (fK a).

(* Now the coherence. It is still strange that I neeed invpK at the end. May
  be the definition of adjointify is not the best. *)
Lemma adjointifyP A B (f : A -> B) g 
  (fK : cancel f g)(gK : cancel g f)(fK' := adjointify fK gK) a :
   gK (f a) = f`_* (fK' a).
Proof.
pose gKV : id =1 f \o g :=  (fun x => (gK x)^-1).
by rewrite  !resppM !(conj_canV gKV) -(conjpM gKV) conjpE mulpK mulpVK invpK.
Qed.

(* And now we prove that we can get an equivalence from a bijection *)
(* This will often be our preferred way to obain a new equivalence, by 
   proving two cancellations lemma and using the can2_equiv equivalence
   builder to correct one of them behind the scene using adjointify. *)
Definition can2_equiv A B (h1 : A -> B)(h2 : B -> A)(h1K : cancel h1 h2)
  (h2K : cancel h2 h1) : A <~> B := Equiv (adjointifyP h1K h2K).

(* A function whose fibers are all contractible. *)
(* This was the main definition taken in the original Equivalence.v *)
(* I should probably change its name now. *)
Definition is_equiv {A B} (e : A -> B) := forall y : B, is_contr (hfiber e y).

Section EquivTheory.

Variables (A B : Type).
Variable (f : A <~> B).

(* Equivalence have contractible fibers.*)
Lemma equiv_is_equiv : is_equiv f.
Proof.
move=> b; exists (Hfiber f (equiv_section f b)) => [[a]].
by case: _ / => {b}; rewrite (equiv_coh f); case (equiv_retraction f a).
Qed.

(* We define a nice constant to access the inverse of an equivalence, *)
(* and a notation  local to the section to access the inverse of a *)
(* canonical equivalence from its function. This means that if f is a *)
(* function, then (f^-1) looks up for a canonical structure of equiv *)
(* having f as equiv_fun in the database, and extracts the second *)
(* (equiv_adjoint) component out of it.*)

Definition inverse := nosimpl (@equiv_adjoint _ _ f).

Definition inverse_of (phf : phantom (A -> B) f) := inverse.
Local Notation "f ^-1" := (inverse_of (@Phantom (_ -> _) f)).

Definition equivK : cancel f f^-1 := @equiv_retraction _ _ f.
Definition inverseK : cancel f^-1 f := @equiv_section _ _ f.

(* Canonical symmetry property of the equiv operation. *)
Canonical equiv_sym : (B <~> A) := @can2_equiv _ _ f^-1 f inverseK equivK.

End EquivTheory.

(* Global notation for the inverse.*)
Notation "f ^-1" := (@inverse_of _ _ _ (@Phantom (_ -> _) f)) : equiv_scope.

(* We could not state this lemma with this notation inside the section since
  the structure/notation was attached to a fixed f and we need it two time here. *)
Lemma inverseKE (A B : Type) (f : A <~> B) : (f^-1)^-1 = f. Proof. by []. Qed.

(* From contractibility of fibers to equivalences. *)
Section IsEquivEquiv.

Variables (A B : Type) (f : A -> B) (f_is_equiv : is_equiv f).

(* This is the inverse of the function with contractible fibers*)
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

(* Now we can forge the equivalence. Theres is no point of having this as a 
   canonical construction though. *)
Definition is_equiv_equiv := can2_equiv is_equiv_directK is_equiv_inverseK.

End IsEquivEquiv.

Definition to_unit {A} (x : A) : unit := tt.

(* A contractible type is equivalent to unit. *)
Section EquivUnit.

Variable A : hContr.

Lemma to_unitK : cancel (@to_unit A) (fun _ => {elt A}). 
Proof. by move=> x /=; rewrite hContrE. Qed.

Lemma to_unitVK : cancel (fun _ => {elt A}) (@to_unit A). Proof. by case. Qed.

(* Unit is canonically equivalent to a type equipped with  a structure of *)
(* contractile (hContr) *) 
Canonical equiv_unit : A <~> unit := can2_equiv to_unitK to_unitVK.

End EquivUnit.

(* A type equivalent to a contractible is itself contractible *)
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

(* Two contractible types (equipped with the hContr structure) are
  canonically equivalent.*)
Canonical equiv_to_hContr (A B : hContr) :=
  can2_equiv (@to_hContrK A B) (@to_hContrK B A).

Section EquivTransport.
Variables (T : Type)(P : T -> Type).

(* Transporting backward. May be should this be in Fibrations. Here we need it *)
(* (only) to define the inverse of the transport in a fiber along a path, . *)
(* to be given to the equivalence constructor. Notice the benfit of tunning the*)
(* behaviour of the arguments of transport. *)
Definition transport_backward (x y : T) (p : x = y) (py : P y) : P x 
  := (p^-1) # py.

Lemma transportK (x y : T)  p :
 cancel (transport P p) (@transport_backward x y p).
Proof. by case: _ / p. Qed.

Lemma transport_backwardK (x y : T)  p :
  cancel (@transport_backward x y p) (transport P p).
Proof. by case: _ / p. Qed.

(* Fibers above two points connected by a path are equivalent. *)
Canonical equiv_transport (x y : T)  p : P x <~> P y :=
  can2_equiv (transportK p) (@transport_backwardK x y p).

End EquivTransport.

(* Since Coq did not have definitional eta, at that time, MathCom libraries*)
(* could not provide the associativity of the composition of functions. *)
(* We do it now, and this lemme should probably be moved somewhere else. *)
Lemma compA A B C D (f : C -> D) (g : B -> C) (h : A -> B) : 
  f \o (g \o h) = (f \o g) \o h.
Proof. reflexivity. Qed.

(* Definition of the diagonals of a type and proof that the two associated *)
(* projections define both an equivalence with the type itself. *)
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

(* The two projections diag_pi1 and diag_pi2 hence define each an equivalences *)
(* bewteen type A and its diagonal. We declare them as canonical. *)
Canonical diag_sq_id1 : diag_sq <~> A := can2_equiv to_diagK1 diag_pi1K.
Canonical diag_sq_id2 : diag_sq <~> A := can2_equiv to_diagK2 diag_pi2K.


End Diagonal.

(* An equivalence is injective. *)
Notation equiv_inj e := (can_inj (equivK [equiv of e])).

(* The equivalence induced by transporting the trivial (reflexive) equivalence *)
(* of U with itself along an path from U to V. *)
Definition eq_equiv (U V : Type) (p : U = V) : U <~> V := p # (equiv_refl U).

Implicit Arguments eq_equiv [[U] [V]].

(* U and V are in univalent correspondance it eq_equiv itself is an eqivalence *)
(* between types U = V and U <~> V *)
Definition univalent U V := is_equiv (@eq_equiv U V).

Module UnivalenceAxiom.

Section UnivalenceAxiomImpliesFunExt.

(* A very strong assumption : forall U V : Type, U and V are in univalent *)
(* correspondance*)
Hypothesis univalence : forall U V, univalent U V.

(* We declare this equivalence as canonical for the purpose of this section. *)
Canonical eq_equiv_equiv U V : U = V <~> (U <~> V) := 
  @is_equiv_equiv _ _ (@eq_equiv U V) (@univalence U V).

(* Since there is no elimination principle on the (inductive) type equiv, we*)
(* prove the one which makes sense (under univalence hypothesis). *)
(* Because of the (debatable) choice made by *)
(* Coq in order to find the elimination scheme used by the elim tactic, the *)
(* choice of this _rect postfixed name makes this scheme the default one *)
(* for elimination on an object of type equiv. See the proofs below *)

Lemma equiv_rect (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_refl T)) -> (forall U V (e : U <~> V), P U V e).
Proof.
move=> PTT U V f; have <- /= := inverseK [equiv of eq_equiv] f.
by case: _ /(eq_equiv^-1 f) => /=.
Qed.

(* A list of small lemmas about the cancellation of an equivalence when *)
(* composed with its inverse.*)
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

(* Now a (very short) proof that the two projections of a diagonal are equal. *)
Lemma diag_pi12 A : @diag_pi1 A = diag_pi2.
Proof. by rewrite -[RHS](precomp_equivK [equiv of diag_pi1]). Qed.

(* As a consequence, we obtain a proof that univalence -> fun ext *)
Lemma funext (X Y : Type)  (f g : X -> Y) : f =1 g -> f = g.
Proof.
move=> eq_fg; pose fg x : diag_sq  := Diag_sq (eq_fg x).
by have: diag_pi1 \o fg = diag_pi2 \o fg by rewrite diag_pi12.
Qed.

(* We now study the elementary theory of the  composition of *)
(* functions with equivalences.*)

Definition compV A B C (e : A <~> B) (h : C -> B) : C -> A := e^-1 \o h.
(* This following choice for the status of the arguments of compV make C not *)
(* implicit, even if the function h is provided. But this is the best choice *)
(* for the purpose of this section. *)
Arguments compV {A B} C e h _.
 
Lemma compK A B C (e : A <~> B) : cancel (comp e) (compV C e).
Proof. by elim: e. Qed.

Lemma compVK A B C (e : A <~> B) : cancel (compV C e) (comp e).
Proof. by elim: e. Qed.

(* Two function spaces with equivalent codomains are equivalent *)
Canonical equiv_comp A B C (e : A <~> B) : (C -> A) <~> (C -> B) :=
  can2_equiv (@compK _ _ C e) (@compVK _ _ C e).

(* Same thing for pre-composition.*)

Definition precomp (X X' Y : Type) (f : X -> X') : (X' -> Y) -> (X -> Y) 
  := comp^~ f.
Definition precompV A B C (e : A <~> B) (h : A -> C) : B -> C := h \o e^-1.

Lemma precompK A B C (e : A <~> B) : cancel (precomp e) (@precompV _ _ C e).
Proof. by elim: e. Qed.

Lemma precompVK A B C (e : A <~> B) : cancel (@precompV _ _ C e) (precomp e).
Proof. by elim: e. Qed.

(* Two function spaces with equivalent domains are equivalent *)
Canonical equiv_precomp A B C (e : A <~> B) : (C -> A) <~> (C -> B) :=
  can2_equiv (@compK _ _ C e) (@compVK _ _ C e).


(* The final goal here is to show that UIP does _not_ hold when we have *)
(* univalence *)
(* We first forge the non-trivial equivalence bool <~> bool via negb *)
Canonical equiv_negb : bool <~> bool :=
  @can2_equiv _ _ negb _ negbK negbK.

(* The inverse contained in the datas of the equivalence defined by idfun is *)
(* not the same as the one contained in the datas of the equivalence defined *)
(* by negb. *)
Lemma not_eq_negb_id : 
  (eq_equiv^-1 [equiv of idfun]) <> (eq_equiv^-1 [equiv of negb]).
Proof.
move => eqN1. (* bug? why does move/(equiv_inj _) does not work? *)
by have /(congr1 (fun f : _ <~> _ => f true)) := equiv_inj _ eqN1.
Qed.

(* Corollary:  bool = bool is not contractible *)
Lemma niscontr_eqbool : ~ is_contr (bool = bool :> Type).
Proof.
case=> f Hf; have := Hf (eq_equiv^-1 [equiv of idfun]).
by rewrite -(Hf (eq_equiv^-1 [equiv of negb])); apply: not_eq_negb_id.
Qed.

(* Uniqueness of identity proofs predicate *)
Definition UIP := forall U (a b : U) (p q : a = b :> U), p = q.

(* As we have two _different_ proofs that "bool = bool" UIP cannot hold *)
Lemma UIP_false : ~ UIP.
Proof. by move => *; apply: not_eq_negb_id. Qed.

(* Anders: As we have
      Eq_rect_eq <-> Eq_dep_eq <-> UIP <-> UIP_refl <-> K
   This means that all of them are incompatible with univalence *)


End UnivalenceAxiomImpliesFunExt.
End UnivalenceAxiom.
