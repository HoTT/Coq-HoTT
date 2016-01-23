(** * Equivalence induction *)
Require Import HoTT.Basics HoTT.Types.

(** We define typeclasses and tactics for doing equivalence induction. *)

Local Open Scope equiv_scope.

Class RespectsEquivalenceL (A : Type@{i}) (P : forall (B : Type@{j}), (A <~> B) -> Type)
  := respects_equivalenceL : { e' : forall B (e : A <~> B), P A (equiv_idmap A) <~> P B e & Funext -> equiv_idmap _ = e' A (equiv_idmap _) }.
Class RespectsEquivalenceR (A : Type@{i}) (P : forall (B : Type@{j}), (B <~> A) -> Type)
  := respects_equivalenceR : { e' : forall B (e : B <~> A), P A (equiv_idmap A) <~> P B e & Funext -> equiv_idmap _ = e' A (equiv_idmap _) }.
(** We use a sigma type rather than a record for two reasons:

    1. In the dependent cases, where one equivalence-respectfulness proof will show up in the body of another goal, it might be the case that using sigma types allows us to reuse the respectfulness lemmas of sigma types, rather than writing new ones for this type.

    2. We expect it to be significantly useful to see the type of the fields than the type of the record, because we expect this type to show up as a goal infrequently.  Sigma types have more informative notations than record type names; the user can run hnf to see what is left to do in the side conditions. *)

Global Arguments RespectsEquivalenceL : clear implicits.
Global Arguments RespectsEquivalenceR : clear implicits.

(** When doing equivalence induction, typeclass inference will either fully solve the respectfulness side-conditions, or not make any progress.  We would like to progress as far as we can on the side-conditions, so that we leave the user with as little to prove as possible.  To do this, we create a "database", implemented using typeclasses, to look up the refinement lemma, keyed on the head of the term we want to respect equivalence. *)
Class respects_equivalence_db {KT VT} (Key : KT) {lem : VT} := make_respects_equivalence_db : Unit.
Definition get_lem' {KT VT} Key {lem} `{@respects_equivalence_db KT VT Key lem} : VT := lem.
Notation get_lem key := ltac:(let res := constr:(get_lem' key) in let res' := (eval unfold get_lem' in res) in exact res') (only parsing).

Section const.
  Context {A : Type} {T : Type}.
  Global Instance const_respects_equivalenceL
  : RespectsEquivalenceL A (fun _ _ => T).
  Proof.
    refine (fun _ _ => equiv_idmap T; fun _ => _).
    exact idpath.
  Defined.
  Global Instance const_respects_equivalenceR
  : RespectsEquivalenceR A (fun _ _ => T).
  Proof.
    refine (fun _ _ => equiv_idmap _; fun _ => _).
    exact idpath.
  Defined.
End const.

Global Instance: forall {T}, @respects_equivalence_db _ _ T (fun A => @const_respects_equivalenceL A T) := fun _ => tt.

Section id.
  Context {A : Type}.
  Global Instance idmap_respects_equivalenceL
  : RespectsEquivalenceL A (fun B _ => B).
  Proof.
    refine (fun B e => e; fun _ => _).
    exact idpath.
  Defined.
  Global Instance idmap_respects_equivalenceR
  : RespectsEquivalenceR A (fun B _ => B).
  Proof.
    refine (fun B e => equiv_inverse e; fun _ => path_equiv _).
    apply path_forall; intro; reflexivity.
  Defined.
End id.

Section unit.
  Context {A : Type}.
  Definition unit_respects_equivalenceL
  : RespectsEquivalenceL A (fun _ _ => Unit)
    := @const_respects_equivalenceL A Unit.
  Definition unit_respects_equivalenceR
  : RespectsEquivalenceR A (fun _ _ => Unit)
    := @const_respects_equivalenceR A Unit.
End unit.

Section prod.
  Global Instance prod_respects_equivalenceL {A} {P Q : forall B, (A <~> B) -> Type}
         `{RespectsEquivalenceL A P, RespectsEquivalenceL A Q}
  : RespectsEquivalenceL A (fun B e => P B e * Q B e).
  Proof.
    refine ((fun B e => equiv_functor_prod' (respects_equivalenceL.1 B e) (respects_equivalenceL.1 B e)); _).
    exact (fun fs =>
             transport
               (fun e' => _ = equiv_functor_prod' e' _) (respects_equivalenceL.2 _)
               (transport
                  (fun e' => _ = equiv_functor_prod' _ e') (respects_equivalenceL.2 _)
                  idpath)).
  Defined.

  Global Instance prod_respects_equivalenceR {A} {P Q : forall B, (B <~> A) -> Type}
         `{RespectsEquivalenceR A P, RespectsEquivalenceR A Q}
  : RespectsEquivalenceR A (fun B e => P B e * Q B e).
  Proof.
    refine ((fun B e => equiv_functor_prod' (respects_equivalenceR.1 B e) (respects_equivalenceR.1 B e)); _).
    exact (fun fs =>
             transport
               (fun e' => _ = equiv_functor_prod' e' _) (respects_equivalenceR.2 _)
               (transport
                  (fun e' => _ = equiv_functor_prod' _ e') (respects_equivalenceR.2 _)
                  idpath)).
  Defined.

  Global Instance: @respects_equivalence_db _ _ (@prod) (@prod_respects_equivalenceL) := tt.
End prod.

(** A tactic to solve the identity-preservation part of equivalence-respectfulness. *)
Local Ltac t_step :=
  idtac;
  match goal with
    | [ |- _ = _ :> (_ <~> _) ] => apply path_equiv
    | _ => reflexivity
    | _ => assumption
    | _ => intro
    | [ |- _ = _ :> (forall _, _) ] => apply path_forall
    | _ => progress unfold functor_forall, functor_sigma
    | _ => progress cbn in *
    | [ |- context[?x.1] ] => let H := fresh in destruct x as [? H]; try destruct H
    | [ H : _ = _ |- _ ] => destruct H
    | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
    | [ H : ?A -> ?B, H' : ?A |- _ ] => generalize dependent (H H'); clear H
    | _ => progress rewrite ?eisretr, ?eissect
  end.
Local Ltac t :=
  repeat t_step.

Section pi.
  Global Instance forall_respects_equivalenceL `{Funext} {A} {P : forall B, (A <~> B) -> Type} {Q : forall B e, P B e -> Type}
         `{HP : RespectsEquivalenceL A P}
         `{HQ : forall a : P A (equiv_idmap A), RespectsEquivalenceL A (fun B e => Q B e (respects_equivalenceL.1 B e a))}
  : RespectsEquivalenceL A (fun B e => forall x : P B e, Q B e x).
  Proof.
    simple refine (fun B e => _; _).
    { refine (equiv_functor_forall'
                (equiv_inverse ((@respects_equivalenceL _ _ HP).1 B e))
                (fun b => _)).
      refine (equiv_compose'
                (equiv_path _ _ (ap (Q B e) (eisretr _ _)))
                (equiv_compose'
                   ((HQ (equiv_inverse ((@respects_equivalenceL _ _ HP).1 B e) b)).1 B e)
                   (equiv_path _ _ (ap (Q A (equiv_idmap _)) _)))).
      refine (ap10 (ap equiv_fun (respects_equivalenceL.2 _)) _). }
    { t. }
  Defined.

  Global Instance forall_respects_equivalenceR `{Funext} {A} {P : forall B, (B <~> A) -> Type} {Q : forall B e, P B e -> Type}
         `{HP : RespectsEquivalenceR A P}
         `{HQ : forall a : P A (equiv_idmap A), RespectsEquivalenceR A (fun B e => Q B e (respects_equivalenceR.1 B e a))}
  : RespectsEquivalenceR A (fun B e => forall x : P B e, Q B e x).
  Proof.
    simple refine (fun B e => _; _).
    { refine (equiv_functor_forall'
                (equiv_inverse ((@respects_equivalenceR _ _ HP).1 B e))
                (fun b => _)).
      refine (equiv_compose'
                (equiv_path _ _ (ap (Q B e) (eisretr _ _)))
                (equiv_compose'
                   ((HQ (equiv_inverse ((@respects_equivalenceR _ _ HP).1 B e) b)).1 B e)
                   (equiv_path _ _ (ap (Q A (equiv_idmap _)) _)))).
      refine (ap10 (ap equiv_fun (respects_equivalenceR.2 _)) _). }
    { t. }
  Defined.
End pi.

Section sigma.
  Global Instance sigma_respects_equivalenceL `{Funext} {A} {P : forall B, (A <~> B) -> Type} {Q : forall B e, P B e -> Type}
         `{HP : RespectsEquivalenceL A P}
         `{HQ : forall a : P A (equiv_idmap A), RespectsEquivalenceL A (fun B e => Q B e (respects_equivalenceL.1 B e a))}
  : RespectsEquivalenceL A (fun B e => sig (Q B e)).
  Proof.
    simple refine ((fun B e => equiv_functor_sigma' (respects_equivalenceL.1 B e) (fun b => _));
            _).
    { refine (equiv_compose'
                ((HQ b).1 B e)
                (equiv_path _ _ (ap (Q A (equiv_idmap _)) _))).
      refine (ap10 (ap equiv_fun (respects_equivalenceL.2 _)) _). }
    { t. }
  Defined.

  Global Instance sigma_respects_equivalenceR `{Funext} {A} {P : forall B, (B <~> A) -> Type} {Q : forall B e, P B e -> Type}
         `{HP : RespectsEquivalenceR A P}
         `{HQ : forall a : P A (equiv_idmap A), RespectsEquivalenceR A (fun B e => Q B e (respects_equivalenceR.1 B e a))}
  : RespectsEquivalenceR A (fun B e => sig (Q B e)).
  Proof.
    simple refine ((fun B e => equiv_functor_sigma' (respects_equivalenceR.1 B e) (fun b => _));
            _).
    { refine (equiv_compose'
                ((HQ b).1 B e)
                (equiv_path _ _ (ap (Q A (equiv_idmap _)) _))).
      refine (ap10 (ap equiv_fun (respects_equivalenceR.2 _)) _). }
    { t. }
  Defined.

  Global Instance: @respects_equivalence_db _ _ (@sigT) (@sigma_respects_equivalenceL) := tt.
End sigma.

Section equiv_transfer.
  Definition respects_equivalenceL_equiv {A A'} {P : forall B, (A <~> B) -> Type} {P' : forall B, A' <~> B -> Type}
             (eA : A <~> A')
             (eP : forall B e, P B (equiv_compose' e eA) <~> P' B e)
             `{HP : RespectsEquivalenceL A P}
  : RespectsEquivalenceL A' P'.
  Proof.
    simple refine ((fun B e => _); _).
    { refine (equiv_compose'
                (eP _ _)
                (equiv_compose'
                   (equiv_compose'
                      (HP.1 _ _)
                      (equiv_inverse (HP.1 _ _)))
                   (equiv_inverse (eP _ _)))). }
    { t. }
  Defined.

  Definition respects_equivalenceR_equiv {A A'} {P : forall B, (B <~> A) -> Type} {P' : forall B, B <~> A' -> Type}
             (eA : A' <~> A)
             (eP : forall B e, P B (equiv_compose' eA e) <~> P' B e)
             `{HP : RespectsEquivalenceR A P}
  : RespectsEquivalenceR A' P'.
  Proof.
    simple refine ((fun B e => _); _).
    { refine (equiv_compose'
                (eP _ _)
                (equiv_compose'
                   (equiv_compose'
                      (HP.1 _ _)
                      (equiv_inverse (HP.1 _ _)))
                   (equiv_inverse (eP _ _)))). }
    { t. }
  Defined.

  Definition respects_equivalenceL_equiv' {A} {P P' : forall B, (A <~> B) -> Type}
             (eP : forall B e, P B e <~> P' B e)
             `{HP : RespectsEquivalenceL A P}
  : RespectsEquivalenceL A P'.
  Proof.
    simple refine ((fun B e => _); _).
    { refine (equiv_compose'
                (eP _ _)
                (equiv_compose'
                   (equiv_compose'
                      (HP.1 _ _)
                      (equiv_inverse (HP.1 _ _)))
                   (equiv_inverse (eP _ _)))). }
    { t. }
  Defined.

  Definition respects_equivalenceR_equiv' {A} {P P' : forall B, (B <~> A) -> Type}
             (eP : forall B e, P B e <~> P' B e)
             `{HP : RespectsEquivalenceR A P}
  : RespectsEquivalenceR A P'.
  Proof.
    simple refine ((fun B e => _); _).
    { refine (equiv_compose'
                (eP _ _)
                (equiv_compose'
                   (equiv_compose'
                      (HP.1 _ _)
                      (equiv_inverse (HP.1 _ _)))
                   (equiv_inverse (eP _ _)))). }
    { t. }
  Defined.
End equiv_transfer.

Section equiv.
  Global Instance equiv_respects_equivalenceL `{Funext} {A} {P Q : forall B, (A <~> B) -> Type}
         `{HP : RespectsEquivalenceL A P}
         `{HP : RespectsEquivalenceL A Q}
  : RespectsEquivalenceL A (fun B e => P B e <~> Q B e).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_functor_equiv _ _);
      apply respects_equivalenceL.1. }
    { t. }
  Defined.

  Global Instance equiv_respects_equivalenceR `{Funext} {A} {P Q : forall B, (B <~> A) -> Type}
         `{HP : RespectsEquivalenceR A P}
         `{HP : RespectsEquivalenceR A Q}
  : RespectsEquivalenceR A (fun B e => P B e <~> Q B e).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_functor_equiv _ _);
      apply respects_equivalenceR.1. }
    { t. }
  Defined.

  Global Instance: @respects_equivalence_db _ _ (@Equiv) (@equiv_respects_equivalenceL) := tt.
End equiv.

Section ap.
  Global Instance equiv_ap_respects_equivalenceL {A} {P Q : forall B, (A <~> B) -> A}
         `{HP : RespectsEquivalenceL A (fun B (e : A <~> B) => P B e = Q B e)}
  : RespectsEquivalenceL A (fun (B : Type) (e : A <~> B) => e (P B e) = e (Q B e)).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_ap' _ _ _ oE _); simpl.
      refine (respects_equivalenceL.1 B e). }
    { t. }
  Defined.

  Global Instance equiv_ap_inv_respects_equivalenceL {A} {P Q : forall B, (A <~> B) -> B}
         `{HP : RespectsEquivalenceL A (fun B (e : A <~> B) => P B e = Q B e)}
  : RespectsEquivalenceL A (fun (B : Type) (e : A <~> B) => e^-1 (P B e) = e^-1 (Q B e)).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_ap' _ _ _ oE _); simpl.
      refine (respects_equivalenceL.1 B e). }
    { t. }
  Defined.

  Global Instance equiv_ap_respects_equivalenceR {A} {P Q : forall B, (B <~> A) -> B}
         `{HP : RespectsEquivalenceR A (fun B (e : B <~> A) => P B e = Q B e)}
  : RespectsEquivalenceR A (fun (B : Type) (e : B <~> A) => e (P B e) = e (Q B e)).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_ap' _ _ _ oE _); simpl.
      refine (respects_equivalenceR.1 B e). }
    { t. }
  Defined.

  Global Instance equiv_ap_inv_respects_equivalenceR {A} {P Q : forall B, (B <~> A) -> A}
         `{HP : RespectsEquivalenceR A (fun B (e : B <~> A) => P B e = Q B e)}
  : RespectsEquivalenceR A (fun (B : Type) (e : B <~> A) => e^-1 (P B e) = e^-1 (Q B e)).
  Proof.
    simple refine (fun B e => _; fun _ => _).
    { refine (equiv_ap' _ _ _ oE _); simpl.
      refine (respects_equivalenceR.1 B e). }
    { t. }
  Defined.
End ap.

(** We now write the tactic that partially solves the respectfulness side-condition.  We include cases for generic typeclass resolution, keys (heads) with zero, one, two, and three arguments, and a few cases that cannot be easily keyed (where the head is one of the arguments, or [forall]), or the head is [paths], for which we have only ad-hoc solutions at the moment. *)
Ltac step_respects_equiv :=
  idtac;
  match goal with
    | _ => progress intros
    | _ => assumption
    | _ => progress unfold respects_equivalenceL
    | _ => progress cbn
    | _ => exact _ (* case for fully solving the side-condition, when possible *)
    | [ |- RespectsEquivalenceL _ (fun _ _ => ?T) ] => rapply (get_lem T)
    | [ |- RespectsEquivalenceL _ (fun _ _ => ?T _) ] => rapply (get_lem T)
    | [ |- RespectsEquivalenceL _ (fun _ _ => ?T _ _) ] => rapply (get_lem T)
    | [ |- RespectsEquivalenceL _ (fun _ _ => ?T _ _ _) ] => rapply (get_lem T)
    | [ |- RespectsEquivalenceL _ (fun B e => equiv_fun e _ = equiv_fun e _) ] => refine equiv_ap_respects_equivalenceL
    | [ |- RespectsEquivalenceL _ (fun B e => equiv_inv e _ = equiv_inv e _) ] => refine equiv_ap_inv_respects_equivalenceL
    | [ |- RespectsEquivalenceL _ (fun B _ => B) ] => refine idmap_respects_equivalenceL
    | [ |- RespectsEquivalenceL _ (fun _ _ => forall _, _) ] => refine forall_respects_equivalenceL
  end.

Ltac equiv_induction p :=
  generalize dependent p;
  let p' := fresh in
  intro p';
    let y := match type of p' with ?x <~> ?y => constr:y end in
    move p' at top;
      generalize dependent y;
      let P := match goal with |- forall y p, @?P y p => constr:P end in
      (* We use [(fun x => x) _] to block automatic typeclass resolution in the hole for the equivalence respectful proof. *)
      refine ((fun g H B e => (@respects_equivalenceL _ P H).1 B e g) _ (_ : (fun x => x) _));
        [ intros | repeat step_respects_equiv ].

Goal forall `{Funext} A B (e : A <~> B), A -> { y : B & forall Q, Contr Q -> ((e^-1 y = e^-1 y) <~> (y = y)) * Q }.
  intros ? ? ? ? a.
  equiv_induction e.
  simpl.
  exists a.
  intros Q q.
  exact (1, center _).
Abort.
