(* We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
*)

Require Import HoTT Universe.
Set Universe Polymorphism.
Section AssumeUnivalence.
Context `{Univalence}.
Section AssumeFunext.
Context `{fs : Funext}.
Section ToBeMoved.
(* Should be moved *)
Local Open Scope equiv_scope.
Definition pullback {A0 B C} (f:B-> A0) (g:C->A0):= {b:B & {c:C & f b = g c}}.
Definition fibration_replacement {B C} {x:C} (f:C ->B) : {y:B & {c:C & f c = y}} :=
    (f x ; (x ; idpath (f x))).
Definition equiv_fibration_replacement  {B C} (f:C ->B):
  C <~> {y:B & {x:C & f x = y}}.
Admitted.
Notation pr1:=(@projT1 _ _).
Notation pr2:=(@projT2 _ _).
Theorem equiv_total_paths (A : Type) (P : A-> Type) (x y : sigT P) :
  (x = y) <~> { p : pr1 x = pr1 y & transport P p (pr2 x) = pr2 y }.
Admitted.
Definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x <~> { z : sigT P & pr1 z = x }.
Admitted.
End ToBeMoved.

Section FamPow.
(* We consider Families and Powers over a fixed type [A] *)
Variable A:Type.
Notation pr1:=(@projT1 _ _).
Definition Fam A:=sigT (fun I:Type  => I->A).
Definition p2f: (A->Type)-> Fam A:=  fun Q:(A->Type) => ( (sigT Q) ; pr1).
Definition f2p: Fam A -> (A->Type):=
 fun F => let (I, f) := F in (fun a => (hfiber f a)).

Open Scope equiv_scope.

Definition exp {U V:Type}(w:U<~>V):(U->A)<~>(V->A).
exists (fun f:(U->A)=> (fun x => (f (w^-1 x)))).
apply equiv_biinv. split;
 exists (fun f:(V->A)=> (fun x => (f (w x)))); intro f; apply fs; intro u;
apply ap; by apply moveR_E.
Defined.

(* For completeness *)
Definition exp' {U V:Type}(w:U<~>V):(A->U)<~>(A->V).
exists (fun f :A->U => (fun a => (w (f a)))).
apply  equiv_biinv. split;
 exists (fun f:(A->V )=> (fun x => (w^-1 (f x)))); intro f; apply fs; intro u;
by apply moveR_E.
Defined.

Theorem equiv_induction (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_idmap T)) -> (forall U V (w : U <~> V), P U V w).
Proof.
intros H0???.
apply (equiv_rect (equiv_path _ _)).
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
 (* Theorem left (P:A -> Type) : (f2pp2f P) = P *)
 exists f2p. intro P. by_extensionality a.
apply ((path_universe (@hfiber_fibration  _ a P))^).

exists f2p. intros [I f].
(* Theorem right (F:Fam A) : F = (p2ff2p F) *)

set (e:=@equiv_total_paths _ _ (@existT Type (fun I0 : Type => I0 -> A) I f)
({a : A & hfiber f a} ; pr1)). simpl in e.
cut ( {p : I = {a : A & @hfiber I A f a} &
     @transport _ (fun I0 : Type => I0 -> A) _ _ p f = pr1}).
intro X. apply ((e ^-1 X)^).
set (w:=@equiv_fibration_replacement A I f).
exists (path_universe w). path_via (exp w f). apply transport_exp.
 unfold w.
(* It still seems to be hidden in the Funext, Isequiv, apD10 *)
apply fs.  (intros [a [i p]]). simpl.  admit.
(* this used to  follow from inspecting the proof of equiv_fibration_replacement
reflexivity.*)
Qed.

Corollary FamequivPow : (A->Type)<~>(Fam A).
exists p2f.
apply (equiv_biinv_equiv _).  exact PowisoFam.
Qed.

(* We construct the universal diagram for the object classifier *)
Definition pointedType:= { u:Type & u }.
Definition topmap {B} (f:B->A) (b:B): pointedType :=
  (hfiber f (f b) ; (b ; idpath (f b))).
Let help_objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) ->
  (pullback P (@projT1 _ (fun u :Type => u))).
intros [a q]. exists a.
exists (existT (fun u:Type=> u) (P a) q). apply idpath.
Defined.

(* This is not optimal *)
Let bla {B C} (b:B): B=C-> C.
intro. by path_induction.
Defined.

Open Local Scope path_scope.
Let help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
 (pullback P (@projT1 _ (fun u :Type => u))) -> (sigT P).
intros [a [[T t] p]]. simpl in p. exact (a;(bla t (p^))).
Defined.

Lemma objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) <~> (pullback P (@projT1 _ (fun u :Type => u))).
exists (help_objclasspb_is_fibrantreplacement P).
apply equiv_biinv. split; exists (help_objclasspb_is_fibrantreplacement2 P); intros [a p]. apply idpath.
destruct p as [[T t] p].
eapply (@total_path A (fun b : A =>
          sigT (fun c : sigT (fun u : Type => u) => paths (P b) (projT1 c)))
(existT
     (fun b : A =>
      sigT (fun c : sigT (fun u : Type => u) => paths (P b) (projT1 c))) a
     (existT (fun c : sigT (fun u : Type => u) => paths (P a) (projT1 c))
        (existT (fun u : Type => u) (P a) (bla t (p^)))
        (idpath (P a))))
(existT
     (fun b : A =>
      sigT (fun c : sigT (fun u : Type => u) => paths (P b) (projT1 c))) a
     (existT (fun c : sigT (fun u : Type => u) => paths (P a) (projT1 c))
        (existT (fun u : Type => u) T t) p)) (idpath a)).
simpl in p. path_induction. reflexivity.
Qed.

End FamPow.
End AssumeFunext.
End AssumeUnivalence.
