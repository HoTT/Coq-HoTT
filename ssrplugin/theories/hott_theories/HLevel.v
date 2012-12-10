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

Lemma respK A B (x y : A) (e : A <~> B) :
  cancel (@resp _ _ x y e) (@respV _ _ x y e).
Proof. exact: can_respp. Qed.

Lemma respVK A B (x y : A) (e : A <~> B) :
  cancel (@respV _ _ x y e) (@resp _ _ x y e).
Proof. 
move=> u; rewrite !resppM -resppV !resp_equivK -resppcomp.
by case: _ / u; rewrite mul1p mulVp.
Qed.

Canonical equiv_resp A B (e : A <~> B) (x y : A) :=
  can2_equiv (@respK _ _ x y e) (@respVK _ _ x y e).

Lemma equiv_has_hlevel n U V : U <~> V -> has_hlevel n U -> has_hlevel n V.
Proof.
elim: n U V => /= [U V e U_is_contr | n ihn U V e U_level_n x y].
  exact: equiv_contr_is_contr e.
exact: (ihn _ _ [equiv of (@resp _ _ x y e^-1)^-1]).
Qed.
