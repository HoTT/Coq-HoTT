(** We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
*)

Require Import Overture types.Universe types.Sigma Fibrations EquivalenceVarieties Equivalences PathGroupoids UnivalenceImpliesFunext.

Section AssumeUnivalence.
Context `{ua:Univalence}.

Definition pullback {A0 B C} (f:B-> A0) (g:C->A0):= {b:B & {c:C & f b = g c}}.

Section FamPow.
(** We consider Families and Powers over a fixed type [A] *)
Variable A:Type.
Definition Fam A:=sigT (fun I:Type  => I->A).
Definition p2f: (A->Type)-> Fam A:=  fun Q:(A->Type) => ( (sigT Q) ; @pr1 _ _).
Definition f2p: Fam A -> (A->Type):=
 fun F => let (I, f) := F in (fun a => (hfiber f a)).

Open Scope equiv_scope.

Definition exp {U V:Type}(w:U<~>V):(U->A)<~>(V->A).
exists (fun f:(U->A)=> (fun x => (f (w^-1 x)))).
apply equiv_biinv. split;
 exists (fun f:(V->A)=> (fun x => (f (w x)))); intro f; apply path_forall; intro u;
apply ap; by apply moveR_E.
Defined.

(** For completeness *)
Definition exp' {U V:Type}(w:U<~>V):(A->U)<~>(A->V).
exists (fun f :A->U => (fun a => (w (f a)))).
apply  equiv_biinv. split;
 exists (fun f:(A->V )=> (fun x => (w^-1 (f x)))); intro f; apply path_forall; intro u;
by apply moveR_E.
Defined.

Theorem equiv_induction (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_idmap T)) -> (forall U V (w : U <~> V), P U V w).
Proof.
intros H0???.
apply (equiv_rect (equiv_path _ _)).
(* The intro pattern: intros ->. replies eq not found. This is a bug. *)
intro x. case x. apply H0.
Defined.

(* This is generalized in Functorish.v *)
Theorem transport_exp (U V:Type)(w:U<~>V): forall (f:U->A),
  (@transport _ (fun I:Type => I->A) _ _ (path_universe w) f) = (exp w f).
set (p:=equiv_induction (fun (U:Type) (V:Type) w => forall f : U -> A,
 (@transport _ (fun I : Type => I -> A) U V (path_universe w) f) = (exp w f))).
apply p.
intros T f. path_via f.
path_via (@transport _ (fun I : Type => I -> A) _ _
  (path_universe (equiv_path _ _ (idpath T) )) f).
path_via (@transport Type (fun I : Type => I -> A) T T (idpath T) f ).
apply (@transport2 Type (fun I:Type => I-> A) T T).
apply eta_path_universe.
Qed.

Open Local Scope path_scope.

Theorem PowisoFam : BiInv p2f.
split.
 (** Theorem left (P:A -> Type) : (f2pp2f P) = P *)
 exists f2p. intro P. by_extensionality a.
apply ((path_universe (@hfiber_fibration  _ a P))^).

exists f2p. intros [I f].
(** Theorem right (F:Fam A) : F = (p2ff2p F) *)

set (e:=equiv_path_sigma _ (@existT Type (fun I0 : Type => I0 -> A) I f)
({a : A & hfiber f a} ; @pr1 _ _)). simpl in e.
cut ( {p : I = {a : A & @hfiber I A f a} &
     @transport _ (fun I0 : Type => I0 -> A) _ _ p f = @pr1 _ _}).
intro X. apply (e X)^.
set (w:=@equiv_fibration_replacement A I f).
exists (path_universe w). transitivity (exp w f). apply transport_exp.
apply path_forall. by  (intros [a [i p]]).
Qed.

Corollary FamequivPow : (A->Type)<~>(Fam A).
exists p2f.
apply (equiv_biinv_equiv _).  exact PowisoFam.
Qed.

(** We construct the universal diagram for the object classifier *)
Definition topmap {B} (f:B->A) (b:B): pointedType :=
  (hfiber f (f b) ; (b ; idpath (f b))).
Let help_objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) ->
  (pullback P (@pr1 _ (fun u :Type => u))).
intros [a q]. exists a.
exists (existT (fun u:Type=> u) (P a) q). apply idpath.
Defined.

(* This is not optimal *)
Let bla {B C} (b:B): B=C-> C.
intro. by path_induction.
Defined.

Open Local Scope path_scope.
Let help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
 (pullback P (@pr1 _ (fun u :Type => u))) -> (sigT P).
intros [a [[T t] p]]. exact (a;(bla t (p^))).
Defined.

Lemma objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) <~> (pullback P (@pr1 _ (fun u :Type => u))).
exists (help_objclasspb_is_fibrantreplacement P).
apply equiv_biinv. split; exists (help_objclasspb_is_fibrantreplacement2 P); intros [a p]. apply idpath.
destruct p as [[T t] p].
eapply (@total_path A (fun b : A =>
          sigT (fun c : sigT (fun u : Type => u) => paths (P b) (pr1 c)))
(existT
     (fun b : A =>
      sigT (fun c : sigT (fun u : Type => u) => paths (P b) (pr1 c))) a
     (existT (fun c : sigT (fun u : Type => u) => paths (P a) (pr1 c))
        (existT (fun u : Type => u) (P a) (bla t (p^)))
        (idpath (P a))))
(existT
     (fun b : A =>
      sigT (fun c : sigT (fun u : Type => u) => paths (P b) (pr1 c))) a
     (existT (fun c : sigT (fun u : Type => u) => paths (P a) (pr1 c))
        (existT (fun u : Type => u) T t) p)) (idpath a)).
simpl in p. by path_induction.
Qed.

End FamPow.
End AssumeUnivalence.
