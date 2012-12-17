Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import Paths Fibrations Contractible Equivalences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.
Open Scope equiv_scope.

Fixpoint has_hlevel (n : nat) : Type -> Type :=
  if n is m.+1 then (fun A => forall x y : A, has_hlevel m (x = y))
  else is_contr.

Definition respV A B (x y : A) (e : A <~> B) : (e x = e y) -> x = y :=
  fun p => (e^-1`_* p)%equiv ^ (equivK e).

Arguments respV {A B x y e} _.

Lemma respK A B (x y : A) (e : A <~> B) :
  cancel (fun p : x = y => e `_* p) respV.
Proof. exact: can_respp. Qed.

Lemma resppJ  A B C (f g : A -> B) (p : f =1 g) (h : B -> C)
      (x y : A) (q : f x = f y) :
  h`_* (q ^ p) = (h`_* q) ^ (fun x => h`_* (p x)).
Proof. by rewrite !resppM -resppV. Qed.

Lemma conjp_eq1 {A B} {x y : A} (f g : A -> B) (p1 p2 : f =1 g) (q : f x = f y) : 
  (forall t, p1 t = p2 t) -> q ^ p1 = q ^ p2.
Proof. by move=> coh; rewrite conjpE !coh. Qed.

Lemma can_respp_coh A B (e : A -> B)(f : B -> A)(efK : cancel e f) (feK : cancel f e) 
  x y (u : e x = e y) :
    (forall t, e`_* (efK t) = feK (e t)) ->  e`_* (f`_* u ^ efK) = u.
Proof. 
by move=> h; rewrite (resppJ efK); rewrite (conjp_eq1 _ h); apply: can_respp.
Qed.

Lemma respVK A B (x y : A) (e : A <~> B) :
  cancel respV (fun p : x = y => e `_* p).
Proof. move=> u /=; exact: (can_respp_coh _ (resp_equivK e)). Qed.

Definition equiv_resp A B (e : A <~> B) (x y : A) : x = y <~> e x = e y :=
  can2_equiv (@respK _ _ x y e) (@respVK _ _ x y e).

Lemma equiv_has_hlevel n U V : U <~> V -> has_hlevel n U -> has_hlevel n V.
Proof.
elim: n U V => /= [U V e U_is_contr | n ihn U V e U_level_n x y].
  exact: equiv_contr_is_contr e.
exact: (ihn _ _ (equiv_sym (equiv_resp (equiv_sym e) x y))).
Qed.
