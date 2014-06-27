Require Import Overture hit.minus1Trunc HProp Misc TruncType types.Universe Equivalences Trunc HSet types.Unit.
Set Standard Proposition Elimination Names.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

Section AssumingUA.
(** The univalence axiom for HProp (Voevodsky's uahp) *)
(** We need fs to be able to find hprop_trunc *)
Context `{fs:Funext} `{ua:Univalence}.
Lemma path_biimp : forall P P': sigT IsHProp, (P.1<->P'.1) -> P = P'.
intros ? ? X. apply (equiv_path_sigma_hprop P P'). 
destruct P, P'. destruct X. 
pose (equiv_iff_hprop X X0). simpl. admit.
Defined.

Lemma biimp_path : forall P P': sigT IsHProp, P = P' -> (P.1<->P'.1).
intros ?? p. by destruct p.
Defined.

Lemma path_equiv_biimp :
 forall P P': sigT IsHProp, (P.1<->P'.1) <~> (P = P').
intros.
apply equiv_adjointify with (path_biimp P P') (biimp_path P P').
- intro x. destruct x. eapply allpath_hprop.
- intros x. cut (IsHProp (P .1 <-> P' .1)). intro H. apply allpath_hprop.
  cut (Contr(P .1 <-> P' .1)). intro. apply trunc_succ.
  exists x. intro y. destruct y as [y1 y2]. destruct x as [x1 x2].
f_ap; apply isequiv_apD10; intro x; [apply P'.2| apply P.2].
Defined.

(** The variant of [uahp] for record types. *)
Lemma path_equiv_biimp_rec {P P':hProp}: (P->P') -> (P'->P) -> P = P'.
set (p:=issig_hProp^-1 P).
set (p':=issig_hProp^-1 P').
intros X X0.
assert (p=p') by (by apply path_equiv_biimp).
clear X X0.
path_via (issig_hProp (issig_hProp ^-1 P)); destruct P. reflexivity.
path_via (issig_hProp (issig_hProp ^-1 P')); destruct P';[f_ap|reflexivity].
Defined.

(** We will now prove that for sets epis and surjections are biequivalent.*)
Definition isepi {X Y} `(f:X->Y) := forall Z: hSet,
  forall g h: Y -> Z, g o f = h o f -> g = h.

Definition issurj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).

Lemma issurj_isepi {X Y} (f:X->Y): issurj f -> isepi f.
intros sur ? ? ? ep. apply isequiv_apD10. intro y.
specialize (sur y).
apply (minus1Trunc_rect_nondep (A:=(sigT (fun x : X => f x = y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 path_via (g (f x)). by apply ap.
 path_via (h (f x)). by apply ap.
intros. by apply @set_path2.
Qed.

Require Import TruncType Pushout.
(* Old-style proof using polymorphic Omega. Needs resizing for the isepi proof to live in the
 same universe as X and Y (the Z quantifier is instantiated with an hSet at a level higher) *)
(* Lemma isepi_issurj {X Y} (f:X->Y): isepi f -> issurj f. *)
(* Proof. *)
(*   intros epif y. *)
(*   set (g :=fun _:Y => Unit_hp). *)
(*   set (h:=(fun y:Y => (hp (hexists (fun _ : Unit => {x:X & y = (f x)})) _ ))). *)
(*   assert (X1: g o f = h o f ). *)
(*   - apply isequiv_apD10. intro x. apply path_equiv_biimp_rec;[|done]. *)
(*     intros _ . apply min1. exists tt. by (exists x). *)
(*   - red in epif.  *)
(*     pose (C := pushout g h).  *)

(*     specialize (epif C). *)

(*     specialize (epif {|iss := isset_hProp |} g h). *)
(*     specialize (epif X1). clear X1. *)
(*     set (p:=apD10 epif y). *)
(*     apply (@minus1Trunc_map (sigT (fun _ : Unit => sigT (fun x : X => y = f x)))). *)
(*     + intros [ _ [x eq]]. *)
(*       exists x. *)
(*         by symmetry. *)
(*     + apply (transport hproptype p tt). *)
(* Defined. *)
Require Import Contractible.
Lemma contr_dom_equiv {A B : Type} (f : A -> B) (H : Contr A) : forall x y : A, f x = f y.
Proof.
  intros. pose (contr (A:=A)). rewrite <- (p x). rewrite <- (p y).
  reflexivity.
Qed.
Require Import types.Sigma.

Lemma isepi_hEpi {X Y : hSet} (f : X -> Y) (epif : isepi f) : hEpi f.
Proof.
  red; red in epif.
  intros.
  refine {| center := (g; 1) |}.
  intros [g' Hg']. 
  assert (eq:=epif _ g g' Hg').
  destruct eq. apply path_sigma_uncurried.
  simpl. exists idpath. simpl.
  assert (IsHProp (g o f = g o f)). typeclasses eauto.
  pose (contr_inhabited_hprop (g o f = g o f) 1).
  apply path_contr.
Defined.

Section hEpi_issurj.
  Context {X Y : hSet} (f : X -> Y) (Hisepi : isepi f).
  Definition epif := isepi_hEpi _ Hisepi.
  Definition fam : Cf f -> hProp.
    refine (let fib y := hp (hexists (fun x : X => f x = y)) _ in

    fun c : Cf f => pushout_rectnd hProp
                                   (fun x : Y + Unit =>
                                      match x with
                                        | inl y => fib y
                                        | inr x => Unit_hp
                                      end)
                                   (fun x => _) c).
  (** Prove that the truncated sigma is equivalent to Unit *)
  pose (contr_inhabited_hprop (fib (f x)) (min1 (x; idpath))).
  apply path_hprop. simpl. simpl in i.
  apply path_universe_uncurried.
  apply (equiv_contr_unit).
  Defined.

  Lemma isepi_issurj : issurj f.
  Proof.
    intros y.
    pose (isepi_isContr _ epif).
    
    assert (forall x : Cf f, fam x = fam (t f)).
    intros. apply contr_dom_equiv. apply i.
    specialize (X0 (push (inl y))). simpl in X0.
    pose (ap hproptype X0). simpl in p. 
    rewrite p. exact tt.
  Defined.
End hEpi_issurj.

Lemma isepi_isequiv X Y (f : X -> Y) `{IsEquiv _ _ f}
: isepi f.
Proof.
  intros ? g h H'.
  apply ap10 in H'.
  apply path_forall.
  intro x.
  transitivity (g (f (f^-1 x))).
  - by rewrite eisretr.
  - transitivity (h (f (f^-1 x))).
    * apply H'.
    * by rewrite eisretr.
Qed.
End AssumingUA.
