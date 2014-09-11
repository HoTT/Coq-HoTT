(** We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
*)

Require Import Overture types.Universe types.Sigma types.Arrow Fibrations 
EquivalenceVarieties Equivalences PathGroupoids UnivalenceImpliesFunext.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

Section AssumeUnivalence.
Context `{ua:Univalence}.

(** This should be moved. *)
Definition pullback {A0 B C} (f:B-> A0) (g:C->A0):= {b:B & {c:C & f b = g c}}.

Section FamPow.
(* This seems like a useful strengthening of [BiInv]. 
It is easier to work with than [Equiv]. *)
Definition BiInvPair {A B} `(f : A -> B) `(g : B -> A) : Type
  := Sect f g * Sect g f.
Lemma BiInvPairBiInv {A B} `(f : A -> B) `(g : B -> A) : 
   BiInvPair f g -> BiInv f.
intros [H1 H2]. split; exists g;auto.
Defined.

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

Theorem PowisoFam : BiInvPair p2f f2p.
split.
 (** Theorem left (P:A -> Type) : (f2pp2f P) = P *)
 + intro P. by_extensionality a.
 apply ((path_universe (@hfiber_fibration  _ a P))^).
(** Theorem right (F:Fam A) : F = (p2ff2p F) *)
+intros [I f]. set (e:=equiv_path_sigma _ (@existT Type (fun I0 : Type => I0 -> A) I f)
({a : A & hfiber f a} ; @pr1 _ _)). simpl in e.
enough (X:{p : I = {a : A & @hfiber I A f a} &
     @transport _ (fun I0 : Type => I0 -> A) _ _ p f = @pr1 _ _}) by apply (e X)^.
set (w:=@equiv_fibration_replacement A I f).
exists (path_universe w). 
transitivity (f o w^-1);[apply transport_exp|apply path_forall;by (intros [a [i p]])].
Qed.

Corollary FamequivPow : (A->Type)<~>(Fam A).
exists p2f.
apply (equiv_biinv_equiv _). apply (BiInvPairBiInv _ _ PowisoFam).
Qed.

(** We construct the universal diagram for the object classifier *)
Definition topmap {B} (f:B->A) (b:B): pointedType :=
  (hfiber f (f b) ; (b ; idpath (f b))).

Local Definition help_objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) ->
  (pullback P (@pr1 _ (fun u :Type => u))).
intros [a q]. exists a.
exists (existT (fun u:Type=> u) (P a) q). apply idpath.
Defined.

Local Definition help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
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

Section Subobjectclassifier.
Require Import Misc HProp.
(** We prove that hProp is the subobject classifier *)
(** In fact, the proof works for general mere predicates on [Type], 
not just [IsHProp], truncations and modalities are important examples.
We provide two proofs for comparison. The first using [HProp] as a record,
The second is an unfolded version.*)

Variable A:Type.

(* This should be moved. Strong monos, i.e. -1-truncated maps. *)
Definition is_smono {I} (f:I->A):=forall i, IsHProp (hfiber f i).
Definition SubFam := (sig (fun F:Fam A => is_smono (pr2 F))).

(* Bug: abstract should accept more than one tactic.
Alternatively, we would like to use [Program] here. 
Instead we split the [Definition] and first make a [Local Definition] *)
Local Definition pow2subfam_pf (P:A -> hProp): is_smono (pr2 (p2f A P)). 
intro i. cbn. 
set (e:=@hfiber_fibration A i (fun x => (hproptype (P x)))).
(* rewrite <- e.
Error: The term does not end with an applied homogeneous relation.
There seems to be a [Proper] missing for [IsHProp] and [<~>].
Should we try to add them consistently for all types? *)
rewrite <- (path_universe_uncurried e).
apply isp. 
Qed.

Definition pow2subfam (P:A -> hProp): SubFam:=
  (p2f A P; pow2subfam_pf P).

Local Definition subfam2pow_pf (F:SubFam)(a:A):IsHProp (f2p A F.1 a). 
unfold f2p. by destruct F as [[I f] p]. 
Qed.

Definition subfam2pow (F:SubFam):A->hProp:=
   fun (a:A)=>hp (f2p A F.1 a) (subfam2pow_pf F a).

Theorem PowisosubFam : BiInvPair pow2subfam subfam2pow.
Proof.
split.
 + intro P. assert (f2p A (p2f A (fun x : A => P x)) = P) by by destruct (PowisoFam A) as [p _].
   apply path_forall. intro a. 
   (* Why do we need to be so explicit here? *)
   apply (path_hprop 
    (hp (f2p A (p2f A (fun x : A => hproptype (P x))) a)
     (subfam2pow_pf
        (@exist (Fam A) (fun F : Fam A => @is_smono (proj1_sig F) (proj2_sig F))
           (p2f A (fun x : A => hproptype (P x))) (pow2subfam_pf P)) a))
     _ (ap10 X a)). 
+intros [[B f] q]. apply path_sigma_hprop.
destruct (PowisoFam A) as [_ p ]. apply (p (B;f)).
Qed.

(** Now the general case *)
Variable isP:Type -> Type.
Variable ishprop_isP: forall I, IsHProp (isP I).
Definition IsPfibered {I} (f:I->A):=forall i, isP (hfiber f i).
Definition PFam := (sig (fun F:Fam A => IsPfibered (pr2 F))).
(* We would like to use [Program] here. Instead we first make a [Local Definition] *)
Local Definition pow2Pfam_pf (P:forall a:A, {X :Type & isP X}): 
           IsPfibered (pr2 (p2f A (pr1 o P))). 
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

Theorem PowisosFam : BiInvPair pow2Pfam Pfam2pow.
Proof.
split.
 + intro P. apply path_forall. intro a. 
   assert (f2p A (p2f A (pr1 o P)) a = (pr1 (P a))) by (
    destruct (PowisoFam A) as [p _];
    apply (ap10 (p (pr1 o P)) a)).
  by apply path_sigma_hprop.
+ intros [[B f] q]. apply path_sigma_hprop.
destruct (PowisoFam A) as [_ p ]. apply (p (B;f)).
Qed.

End Subobjectclassifier.

End AssumeUnivalence.
