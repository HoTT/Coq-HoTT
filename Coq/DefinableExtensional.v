(** Peter Aczel suggested that we include a meta-theorem which states that
   predicates on functions obey a substitution principle with respect to
   extensional equality, as long as they are built from "standard" constructors.
*)

Require Import Paths Fibrations Contractible Funext Equivalences.

(** Let us first observe the following easy fact. If [P] is a fibration and [x ~~> y]
    then [P x] and [P y] are connected by a path (and so also equivalent). *)

Lemma path_fibers {A} {P : A -> Type} {x y : A} : x ~~> y -> P x ~~> P y.
Proof.
  path_induction.
Defined.

(** Let us call a fibration [P : (A -> B) -> Type] _extensional_ if it takes
   extensionally equal maps to equivalent fibers. *)

Definition extensional {A B} (P : (A -> B) -> Type) :=
  forall f g : A -> B, f ≡ g -> P f ≃> P g.

(** If we assume the Univalence Axiom then [equiv_fibers] implies that every
   fibration on a function space is extensional. But even without UA we can
   show that fibrations built from basic operations are extensional. *)

(* This should go to Paths.v. *)
Definition path_pair {A B} {x y : A * B} : (fst x ~~> fst y) * (snd x ~~> snd y) -> x ~~> y.  
Proof.
  intros [p q].
  destruct x, y.
  simpl in * |- *.
  induction p.
  induction q.
  apply idpath.
Defined.

Lemma ext_prod A B P Q:
  extensional P -> extensional Q -> extensional (fun (h : A -> B) => prod (P h) (Q h)).
Proof.
  intros EP EQ f g E.
  exists (fun p => (EP f g E (fst p), EQ f g E (snd p))).
  intros [u v].
  pose (x := inverse (EP f g E) u).
  pose (y := inverse (EQ f g E) v).
  assert (r : (EP f g E x, EQ f g E y) ~~> (u, v)).
    apply path_pair; split; apply inverse_is_section.
  contract_hfiber (x,y) r.
  destruct z as [a b].
  simpl in * |- *.
  assert (s : (a,b) ~~> (x,y)).
    apply path_pair; simpl; split.
      unfold x; equiv_moveleft.
      apply (map (@fst _ _) q).
      unfold y; equiv_moveleft.
      apply (map (@snd _ _) q).
  apply total_path with (p := s).
  simpl.
Qed.

Lemma ext_sum A B P Q : extensional P -> extensional Q -> extensional (fun (h : A -> B) => P h + Q h)%type.
Proof.
  intros A B P Q EP EQ f g E [u | v].
  left; apply EP with (f := f); auto.
  right; apply EQ with (f := f); auto.
Qed.

Lemma ext_imp A B P Q : extensional P -> extensional Q -> extensional (fun (h : A -> B) => P h -> Q h)%type.
Proof.
  intros A B P Q EP EQ f g E H G.
  apply EQ with (f := f); auto.
  apply H; auto.
  apply EP with (f := g); auto.
  intro x.
  apply opposite.
  apply E.
Qed.
  
Lemma ext_forall A B C (P : (A -> B) -> C -> Type) :
  (forall z : C, extensional (fun h => P h z)) -> extensional (fun h => forall z, P h z).
Proof.
  intros A B C P EC f g E H z.
  apply EC with (f := f); auto.
Qed.

Lemma ext_sig A B C (P : (A -> B) -> C -> Type) :
  (forall z : C, extensional (fun h => P h z)) -> extensional (fun h => sigT (P h)).
Proof.
  intros A B C P EC f g E [w H].
  split with w.
  apply EC with (f := f); auto.
Defined.

Lemma ext_sig_dep A B (C : (A -> B) -> Type) (P : forall h, C h -> Type)  :
  { c : extensional C & (forall f g (E : f ≡ g) u v,  (c f g E u ~~> v) -> P f u -> P g v) } ->
  extensional (fun h => sigT (fun z => P h z)).
Proof.
  intros A B C P [c H].
  intros f g E [u p].
  split with (c f g E u).
  apply H with (f := f) (E := E) (u := u); auto.
Defined.

Ltac auto_ext :=
  match goal with
    | [ |- extensional (fun _ => prod _ _) ] => apply ext_prod; auto_ext
    | [ |- extensional (fun _ => sum _ _) ] => apply ext_sum; auto_ext
    | [ |- extensional (fun _ => (_ -> _))] => apply ext_imp; auto_ext
    | [ |- extensional (fun _ => forall c : _, _) ] => apply ext_forall; auto_ext
    | [ |- extensional (fun _ => sigT _)] => apply ext_sig; auto_ext
    | [ |- forall x : ?A, extensional _ ] => intros; auto_ext
    | _ => auto
  end.

Lemma extensional_hfiber A B (y : B) : extensional (fun h : A -> B => hfiber h y).
Proof.
  intros A B y.
  unfold hfiber.
  auto_ext.
  intros f g E p.
  path_via (f z).
Defined.

(** This goes to the main library. *)
Lemma contractible_retract A B (s : A -> B) (r : B -> A) :
  (r ○ s ≡ idmap A) -> is_contr B -> is_contr A.
Proof.
  intros A B s r E [b p].
  split with (r b).
  intro a.
  path_via (r (s a)).
  apply opposite.
  apply E.
Qed.

Lemma extensional_is_equiv A B : extensional (@is_equiv A B).
Proof.
  intros A B.
  unfold is_equiv.
  auto_ext.
  unfold is_contr.
  apply ext_sig_dep.
  assert (c : extensional (fun h : A -> B => hfiber h z)).
  apply extensional_hfiber.
  split with c.
  intros f g E u v p q y.
  unfold extensional in c.
  Check (c f g E).




