(** We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
*)

Require Import Overture types.Universe types.Sigma types.Arrow Fibrations EquivalenceVarieties Equivalences PathGroupoids UnivalenceImpliesFunext.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

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

(* This is generalized in Functorish.v *)
Theorem transport_exp (U V:Type)(w:U<~>V): forall (f:U->A),
  (transport (fun I:Type => I->A) (path_universe w) f) = (f o w^-1).
Proof.
  intros f; apply path_arrow; intros y.
  refine (transport_arrow_toconst _ _ _ @ _).
  unfold compose; apply ap.
  by apply transport_path_universe_V.
Qed.

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
exists (path_universe w). transitivity (f o w^-1). apply transport_exp.
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

Let help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
 (pullback P (@pr1 _ (fun u :Type => u))) -> (sigT P).
intros [a [[T t] p]]. exact (a;(transport (fun X => X) (p^) t)).
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
        (existT (fun u : Type => u) (P a) (transport (fun X => X) (p^) t))
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
