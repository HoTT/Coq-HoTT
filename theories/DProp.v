(* -*- mode: coq; mode: visual-line -*-  *)

(** * Decidable propositions *)

Require Import HoTT.Basics HoTT.Types.
Require Import TruncType HProp UnivalenceImpliesFunext.
Require Import hit.Truncations.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Definitions *)

(** A decidable proposition is, morally speaking, an hprop that is decidable.  However, we only require that it be an hprop under the additional assumption of [Funext]; this enables decidable propositions to usually be used without [Funext] hypotheses. *)

Record DProp :=
  { dprop_type : Type ;
    ishprop_dprop : Funext -> IsHProp dprop_type ;
    dec_dprop : Decidable dprop_type
  }.

Coercion dprop_type : DProp >-> Sortclass.
Global Existing Instance ishprop_dprop.
Global Existing Instance dec_dprop.

Definition True : DProp
  := Build_DProp Unit _ (inl tt).

Definition False : DProp
  := Build_DProp Empty _ (inr idmap).

Definition dprop_to_bool (P : DProp) : Bool
  := if dec P then true else false.

Coercion dprop_to_bool : DProp >-> Bool.

(** ** The type of decidable props *)

Definition issig_dprop
  : { X : Type & { _ : Funext -> IsHProp X & Decidable X } } <~> DProp.
Proof.
  issig Build_DProp dprop_type ishprop_dprop dec_dprop.
Defined.

Definition equiv_path_dprop `{Funext} (P Q : DProp)
: (P = Q :> Type) <~> (P = Q :> DProp).
Proof.
  destruct P as [P hP dP]. destruct Q as [Q hQ dQ].
  refine (equiv_compose'
            (equiv_inverse (equiv_ap' (equiv_inverse issig_dprop) _ _))
            _); cbn.
  refine (equiv_compose'
            (equiv_ap' (equiv_inverse
                          (equiv_sigma_assoc _ (fun Xp => Decidable Xp.1)))
                       ((P;hP);dP) ((Q;hQ);dQ)) _).
  refine (equiv_compose' (equiv_path_sigma_hprop _ _) _); cbn.
  { intros [X hX]; exact _. }
  refine (equiv_path_sigma_hprop (P;hP) (Q;hQ)).
Defined.

Definition path_dprop `{Funext} {P Q : DProp}
: (P = Q :> Type) -> (P = Q :> DProp)
  := equiv_path_dprop P Q.

Global Instance ishset_dprop `{Univalence} : IsHSet DProp.
Proof.
  intros P Q.
  refine (trunc_equiv' _ (n := -1) (equiv_path_dprop P Q)).
Defined.

Global Instance isequiv_dprop_to_bool `{Univalence}
: IsEquiv dprop_to_bool.
Proof.
  refine (isequiv_adjointify _ (fun b:Bool => if b then True else False) _ _).
  - intros []; reflexivity.
  - intros P; unfold dprop_to_bool.
    destruct (dec P); symmetry; apply path_dprop, path_universe_uncurried.
    + apply if_hprop_then_equiv_Unit; [ exact _ | assumption ].
    + apply if_not_hprop_then_equiv_Empty; [ exact _ | assumption ].
Defined.

Definition equiv_dprop_to_bool `{Univalence}
: DProp <~> Bool
  := BuildEquiv _ _ dprop_to_bool _.

(** ** Operations *)

(** We define the logical operations on decidable hprops to be the operations on ordinary hprops, with decidability carrying over. *)

Definition dand (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (b1 *  b2) _ _).
  destruct (dec b1) as [x1|y1]; destruct (dec b2) as [x2|y2].
  - exact (inl (x1,x2)).
  - apply inr; intros [_ x2]; exact (y2 x2).
  - apply inr; intros [x1 _]; exact (y1 x1).
  - apply inr; intros [x1 _]; exact (y1 x1).
Defined.

Definition dor (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (hor b1 b2) _ _).
  destruct (dec b1) as [x1|y1].
  - exact (inl (tr (inl x1))).
  - destruct (dec b2) as [x2|y2].
    + exact (inl (tr (inr x2))).
    + apply inr; intros z; strip_truncations.
      destruct z as [x1|x2].
      * exact (y1 x1).
      * exact (y2 x2).
Defined.

Definition dneg (b : DProp) : DProp.
Proof.
  refine (Build_DProp (~b) _ _).
  destruct (dec b) as [x|y].
  - apply inr; intros nx; exact (nx x).
  - exact (inl y).
Defined.

Definition dimpl (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (b1 -> b2) _ _).
  destruct (dec b2) as [x2|y2].
  - exact (inl (fun _ => x2)).
  - destruct (dec b1) as [x1|y1].
    + apply inr; intros f.
      exact (y2 (f x1)).
    + apply inl; intros x1.
      elim (y1 x1).
Defined.

Infix "&&" := dand : dprop_scope.
Infix "||" := dor : dprop_scope.
Infix "->" := dimpl : dprop_scope.
Notation "!! P" := (dneg P) (at level 75, right associativity)
                   : dprop_scope.

Delimit Scope dprop_scope with dprop.
Local Open Scope dprop_scope.

(** ** Computation *)

(** In order to be able to "compute" with [DProp]s like booleans, we define a couple of typeclasses. *)

Class IsTrue (P : DProp) :=
  dprop_istrue : P.

Class IsFalse (P : DProp) :=
  dprop_isfalse : ~ P.

Global Instance true_istrue : IsTrue True := tt.

Global Instance false_isfalse : IsFalse False := idmap.

Global Instance dand_true_true {P Q} `{IsTrue P} `{IsTrue Q}
: IsTrue (P && Q).
Proof.
  exact (dprop_istrue, dprop_istrue).
Defined.

Global Instance dand_false_l {P Q} `{IsFalse P}
: IsFalse (P && Q).
Proof.
  intros [p q].
  exact (dprop_isfalse p).
Defined.

Global Instance dand_false_r {P Q} `{IsFalse Q}
: IsFalse (P && Q).
Proof.
  intros [p q].
  exact (dprop_isfalse q).
Defined.

Global Instance dor_true_l {P Q} `{IsTrue P}
: IsTrue (P || Q).
Proof.
  exact (tr (inl Q dprop_istrue)).
Defined.

Global Instance dor_true_r {P Q} `{IsTrue Q}
: IsTrue (P || Q).
Proof.
  exact (tr (inr P dprop_istrue)).
Defined.

Global Instance dor_false_false {P Q} `{IsFalse P} `{IsFalse Q}
: IsFalse (P || Q).
Proof.
  intros pq. strip_truncations. destruct pq as [p|q].
  - exact (dprop_isfalse p).
  - exact (dprop_isfalse q).
Defined.

Global Instance dneg_true {P} `{IsTrue P}
: IsFalse (!! P).
Proof.
  intros np; exact (np dprop_istrue).
Defined.

Global Instance dneg_false {P} `{IsFalse P}
: IsTrue (!! P).
Proof.
  exact dprop_isfalse.
Defined.

Global Instance dimpl_true_r {P Q} `{IsTrue Q}
: IsTrue (P -> Q).
Proof.
  intros p. exact dprop_istrue.
Defined.

Global Instance dimpl_false_l {P Q} `{IsFalse P}
: IsTrue (P -> Q).
Proof.
  intros p. elim (dprop_isfalse p).
Defined.

Global Instance dimpl_true_false {P Q} `{IsTrue P} `{IsFalse Q}
: IsFalse (P -> Q).
Proof.
  intros f. exact (dprop_isfalse (f dprop_istrue)).
Defined.
