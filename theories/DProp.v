(* -*- mode: coq; mode: visual-line -*-  *)

(** * Decidable propositions *)

Require Import HoTT.Basics HoTT.Types.
Require Import TruncType HProp UnivalenceImpliesFunext.
Require Import HIT.Truncations.

Local Open Scope path_scope.

(** ** Definitions *)

(** A decidable proposition is, morally speaking, an hprop that is decidable.  However, we only require that it be an hprop under the additional assumption of [Funext]; this enables decidable propositions to usually be used without [Funext] hypotheses. *)

Record DProp :=
  { dprop_type : Type ;
    ishprop_dprop : Funext -> IsHProp dprop_type ;
    dec_dprop : Decidable dprop_type
  }.

(** A fancier definition, which would have the property that negation is judgmentally involutive, would be

<<
Record DProp :=
  { dprop_holds : Type ;
    ishprop_holds : Funext -> IsHProp dprop_holds ;
    dprop_denies : Type ;
    ishprop_denies : Funext -> IsHProp dprop_denies ;
    holds_or_denies : dprop_holds + dprop_denies ;
    denies_or_holds : dprop_denies + dprop_holds ;
    not_holds_and_denies : dprop_holds -> dprop_denies -> Empty
  }.
>>

At some point we may want to go that route, but it would be more work.  In particualar, [Instance]s of [Decidable] wouldn't be automatically computed for us, and the characterization of the homotopy type of [DProp] itself would be a lot harder. *)

Coercion dprop_type : DProp >-> Sortclass.
Global Existing Instance ishprop_dprop.
Global Existing Instance dec_dprop.

(** Sometimes, however, we have decidable props that are hprops without funext, and we want to remember that. *)

Record DHProp :=
  { dhprop_hprop : hProp ;
    dec_dhprop : Decidable dhprop_hprop
  }.

Coercion dhprop_hprop : DHProp >-> hProp.
Global Existing Instance dec_dhprop.

Definition dhprop_to_dprop : DHProp -> DProp
  := fun P => Build_DProp P (fun _ => _) _.

Coercion dhprop_to_dprop : DHProp >-> DProp.

(** In particular, [True] and [False] are always hprops. *)

Definition True : DHProp
  := Build_DHProp Unit_hp (inl tt).

Definition False : DHProp
  := Build_DHProp False_hp (inr idmap).

(** Decidable props can be coerced to [Bool]. *)

Definition dprop_to_bool (P : DProp) : Bool
  := if dec P then true else false.

Coercion dprop_to_bool : DProp >-> Bool.

(** And back again, but we don't declare that as a coercion. *)

Definition bool_to_dhprop (b : Bool) : DHProp
  := if b then True else False.

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
  refine (((equiv_ap' issig_dprop^-1 _ _)^-1)
            oE _); cbn.
  refine ((equiv_ap' (equiv_sigma_assoc _ (fun Xp => Decidable Xp.1))^-1
                     ((P;hP);dP) ((Q;hQ);dQ))
            oE _).
  refine (equiv_path_sigma_hprop _ _ oE _); cbn.
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
  refine (isequiv_adjointify dprop_to_bool bool_to_dhprop _ _).
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

(** We define the logical operations on decidable hprops to be the operations on ordinary hprops, with decidability carrying over.  For the operations which preserve hprops without funext, we define separate versions that act on [DHProp]. *)

Definition dand (b1 b2 : DProp) : DProp
  := Build_DProp (b1 * b2) _ _.

Definition dhand (b1 b2 : DHProp) : DHProp
  := Build_DHProp (BuildhProp (b1 * b2)) _.

Definition dor (b1 b2 : DProp) : DProp
  := Build_DProp (hor b1 b2) _ _.

Definition dhor (b1 b2 : DHProp) : DHProp
  := Build_DHProp (BuildhProp (hor b1 b2)) _.

Definition dneg (b : DProp) : DProp
  := Build_DProp (~b) _ _.

Definition dimpl (b1 b2 : DProp) : DProp
  := Build_DProp (b1 -> b2) _ _.

Declare Scope dprop_scope.
Delimit Scope dprop_scope with dprop.
Bind Scope dprop_scope with DProp.
Declare Scope dhprop_scope.
Delimit Scope dhprop_scope with dhprop.
Bind Scope dhprop_scope with DHProp.

Infix "&&" := dand : dprop_scope.
Infix "&&" := dhand : dhprop_scope.
Infix "||" := dor : dprop_scope.
Infix "||" := dhor : dhprop_scope.
Infix "->" := dimpl : dprop_scope.
Notation "!! P" := (dneg P) : dprop_scope.

Local Open Scope dprop_scope.

(** ** Computation *)

(** In order to be able to "compute" with [DProp]s like booleans, we define a couple of typeclasses. *)

Class IsTrue (P : DProp) :=
  dprop_istrue : P.

Class IsFalse (P : DProp) :=
  dprop_isfalse : ~ P.

(** Note that we are not using [Typeclasses Strict Resolution] for [IsTrue] and [IsFalse]; this enables us to write simply [dprop_istrue] as a proof of some true dprop, and Coq will infer from context what the dprop is that we're proving. *)

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

Global Instance dhand_true_true {P Q : DHProp} `{IsTrue P} `{IsTrue Q}
: IsTrue (P && Q)%dhprop.
Proof.
  (** We have to give [P] as an explicit argument here.  This is apparently because with two [IsTrue] instances in the context, when we write simply [dprop_istrue], Coq guesses one of them during typeclass resolution, and isn't willing to backtrack once it realizes that that choice fails to be what's needed to solve the goal.  Coq currently seems to consistently guess [Q] rather than [P], so that we don't have to give the argument [Q] to the second call to [dprop_istrue]; but rather than depend on such behavior, we give both arguments explicitly.  (The problem doesn't arise with [dand_true_true] because in that case, unification, which fires before typeclass search, is able to guess that the argument must be [P].) *)
  exact (@dprop_istrue P _, @dprop_istrue Q _).
Defined.

Global Instance dhand_false_l {P Q : DHProp} `{IsFalse P}
: IsFalse (P && Q)%dhprop.
Proof.
  intros [p q].
  exact (dprop_isfalse p).
Defined.

Global Instance dhand_false_r {P Q : DHProp} `{IsFalse Q}
: IsFalse (P && Q)%dhprop.
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

Global Instance dhor_true_l {P Q : DHProp} `{IsTrue P}
: IsTrue (P || Q)%dhprop.
Proof.
  exact (tr (inl Q dprop_istrue)).
Defined.

Global Instance dhor_true_r {P Q : DHProp} `{IsTrue Q}
: IsTrue (P || Q)%dhprop.
Proof.
  exact (tr (inr P dprop_istrue)).
Defined.

Global Instance dhor_false_false {P Q : DHProp} `{IsFalse P} `{IsFalse Q}
: IsFalse (P || Q)%dhprop.
Proof.
  intros pq. strip_truncations. destruct pq as [p|q].
  (** See comment in the proof of [dhand_true_true]. *)
  - exact (@dprop_isfalse P _ p).
  - exact (@dprop_isfalse Q _ q).
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
