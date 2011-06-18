(** Peter Aczel suggested that we include a meta-theorem which states that
   predicates on functions obey a substitution principle with respect to
   extensional equality, as long as they are built from "standard" constructors.
   *)

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

Require Import Paths Fibrations Contractible Funext Equivalences.

(** Let us first observe the following easy fact. If [P] is a fibration and
   [x ~~> y] then [P x] and [P y] are equivalent. *)

Lemma equiv_fibers {A} (P : A -> Type) (x y : A) : x ~~> y -> P x ≃> P y.
Proof.
  intros A P x y p.
  path_induction.
  apply idequiv.
Qed.

(** Let us call a fibration [P : (A -> B) -> Type] _extensional_ if it takes
   extensionally equal maps to equivalent fibers. *)

Definition extensional {A B} (P : (A -> B) -> Type) :=
  forall f g : A -> B, f ≡ g -> P f ≃> P g.


(** We also include useful constructions of equivalences. *)

(* This should go to Paths.v. *)
Definition path_pair {A B} {a b : A} {c d : B} : a ~~> b -> c ~~> d -> (a,c) ~~> (b,d).
Proof.
  path_induction.
Defined.

Definition path_fst {A B} {a b : A} {c d : B} : (a,c) ~~> (b,d) -> a ~~> b.
Proof.
  intros A B a b c d pq.
  exact (map (@fst A B) pq).
Qed.

Definition path_snd {A B} {a b : A} {c d : B} : (a,c) ~~> (b,d) -> c ~~> d.
Proof.
  intros A B a b c d pq.
  exact (map (@snd A B) pq).
Qed.

(* This should go to Fibrations.v. *)
Lemma path_in_total {A} {P : A -> Type} (u v : total P) :
  { p : pr1 u ~~> pr1 v & transport p (pr2 u) ~~> (pr2 v) } -> u ~~> v.
Proof.
  intros A P [x u] [y v] [p q].
  simpl in * |- *.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Qed.

Lemma equiv_prod {A B} {C D} (f : A ≃> B) (g : C ≃> D) : A * C ≃> B * D.
Proof.
  intros A B C D [f ef] [g eg].
  exists (fun xy => (f (fst xy), g (snd xy))).
  intros [b d].
  destruct (ef b) as [[a p] r].
  destruct (eg d) as [[c q] s].
  contract_hfiber (a,c) (path_pair p q).
  destruct z as (a',c').
  rename q0 into t.
  simpl in t.
  assert (u : (a',c') ~~> (a,c)).
  apply path_pair.
  exact (base_path (r (tpair a' (path_fst t)))).
  exact (base_path (s (tpair c' (path_snd t)))).
  apply path_in_total.
  split with u.
  simpl.
Admitted.

(** If we assume the Univalence Axiom then [equiv_fibers] implies that every
   fibration on a function space is extensional. But even without UA we can
   show that fibrations built from basic operations are extensional. *)

Lemma ext_prod A B P Q:
  extensional P -> extensional Q -> extensional (fun (h : A -> B) => P h * Q h)%type.
Proof.
  intros A B P Q EP EQ f g E.
  unfold equiv.
  split with (fun p => (EP f g E (fst p), EQ f g E (snd p))).
  intros [u v].
  destruct EP as [ep eqP].

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




