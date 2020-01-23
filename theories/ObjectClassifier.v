(** We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
*)

Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations HProp EquivalenceVarieties UnivalenceImpliesFunext Pullback.

Local Open Scope path_scope.

Section AssumeUnivalence.
Context `{ua:Univalence}.

Section FamPow.
(** We consider Families and Powers over a fixed type [A] *)
Variable A : Type.
Definition Fam A:=sigT (fun I:Type  => I->A).
Definition p2f: (A->Type)-> Fam A:=  fun Q:(A->Type) => ( (sigT Q) ; @pr1 _ _).
Definition f2p: Fam A -> (A->Type):=
 fun F => let (I, f) := F in (fun a => (hfiber f a)).

(* This is generalized in Functorish.v *)
Theorem transport_exp (U V:Type)(w:U<~>V): forall (f:U->A),
  (transport (fun I:Type => I->A) (path_universe w) f) = (f o w^-1).
Proof.
  intros f; apply path_arrow; intros y.
  refine (transport_arrow_toconst _ _ _ @ _).
  apply ap.
  by apply transport_path_universe_V.
Qed.

Theorem FamequivPow : (A->Type)<~>(Fam A).
Proof.
apply (equiv_adjointify p2f f2p).
(* Theorem right (F:Fam A) : F = (p2ff2p F) *)
 +intros [I f]. set (e:=equiv_path_sigma _ (@existT Type (fun I0 : Type => I0 -> A) I f)
  ({a : A & hfiber f a} ; @pr1 _ _)). simpl in e.
  enough (X:{p : I = {a : A & @hfiber I A f a} &
     @transport _ (fun I0 : Type => I0 -> A) _ _ p f = @pr1 _ _}) by apply (e X)^.
  set (w:=@equiv_fibration_replacement A I f).
  exists (path_universe w). 
  transitivity (f o w^-1);[apply transport_exp|apply path_forall;by (intros [a [i p]])].
 (* Theorem left (P:A -> Type) : (f2pp2f P) = P *)
 + intro P. by_extensionality a.
 apply ((path_universe (@hfiber_fibration  _ a P))^).
Defined.

(** We construct the universal diagram for the object classifier *)
Definition topmap {B} (f:B->A) (b:B): pType :=
  Build_pType (hfiber f (f b)) (b ; idpath (f b)).

Local Definition help_objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P)->
  (Pullback P (@pr1 _ (fun u :Type => u))):=
(fun (X : {a : A & P a}) => (fun (a : A) (q : P a) => (a; ((P a; q); 1))) X.1 X.2).

Local Definition help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
 (Pullback P (@pr1 _ (fun u :Type => u))) -> (sigT P).
intros [a [[T t] p]]. exact (a;(transport (fun X => X) (p^) t)).
Defined.

Lemma objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) <~> (Pullback P (@pr1 _ (fun u :Type => u))).
Proof.
exists (help_objclasspb_is_fibrantreplacement P).
apply isequiv_biinv. split; exists (help_objclasspb_is_fibrantreplacement2 P); intros [a p].
- apply idpath.
- destruct p as [[T t] p].
  refine (path_sigma' _ (idpath a) _).
  simpl in p. by path_induction.
Qed.

End FamPow.

Section Subobjectclassifier.
(** We prove that hProp is the subobject classifier *)
(** In fact, the proof works for general mere predicates on [Type], 
not just [IsHProp], truncations and modalities are important examples.*)
Variable A : Type.
Variable isP : Type -> Type.
Variable ishprop_isP : forall I, IsHProp (isP I).
Definition IsPfibered {I} (f:I->A):=forall i, isP (hfiber f i).
Definition PFam := (sig (fun F:Fam A => IsPfibered (pr2 F))).
(* Bug: abstract should accept more than one tactic.
https://coq.inria.fr/bugs/show_bug.cgi?id=3609
Alternatively, we would like to use [Program] here.
6a99db1c31fe267fdef7be755fa169fb6a87e3cf
Instead we split the [Definition] and first make a [Local Definition] *)
Local Definition pow2Pfam_pf (P:forall a:A, {X :Type & isP X}): 
           IsPfibered (pr2 (p2f A (pr1 o P))). 
Proof.
intro i. cbn. 
rewrite <- (path_universe_uncurried (@hfiber_fibration A i (pr1 o P))).
apply ((P i).2).
Qed.

Definition pow2Pfam (P:forall a:A, {X :Type & isP X}): PFam:=
  (p2f A (fun a => (pr1 (P a))); pow2Pfam_pf P).

Local Definition Pfam2pow_pf (F:PFam)(a:A):isP (f2p A F.1 a). 
unfold f2p. by destruct F as [[I f] p].
Qed.

Definition Pfam2pow (F:PFam) (a:A): {X :Type & isP X}:=
   ((f2p A F.1 a); (Pfam2pow_pf F a)).

Theorem PowisoPFam : (forall a:A, {X :Type & isP X})<~>PFam.
Proof.
apply (equiv_adjointify pow2Pfam Pfam2pow).
 + intros [[B f] q]. apply path_sigma_hprop. cbn.
  refine (@eisretr _ _ (FamequivPow A) _ (B;f)).
+ intro P. apply path_forall. intro a.
 assert (f2p A (p2f A (pr1 o P)) a = (pr1 (P a))).
- set (p:=@eissect _ _ (FamequivPow A) _).
  apply (ap10 (p (pr1 o P)) a).
- by apply path_sigma_hprop.
Defined.
End Subobjectclassifier.

End AssumeUnivalence.
