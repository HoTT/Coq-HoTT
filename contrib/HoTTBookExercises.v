(** The HoTT Book Exercises formalization. *)

(** This file records formalized solutions to the HoTT Book exercises. *)

(*  See HoTTBook.v for an IMPORTANT NOTE FOR THE HoTT DEVELOPERS.

    PROCEDURE FOR UPDATING THE FILE:

   1. Compile the latest version of the HoTT Book to update the LaTeX
      labels. Do not forget to pull in changes from HoTT/HoTT.

   2. Run `etc/Book.py` using the `--exercises` flag (so your command
      should look like `cat ../book/*.aux | etc/Book.py --exercises contrib/HoTTBookExercises.v`)
      If it complains, fix things.

   3. Add contents to new entries.

   4. Run `etc/Book.py` again to make sure it is happy.

   5. Compile this file with `make contrib` or `make contrib/HoTTBookExercises.vo`.

   6. Do the git thing to submit your changes.

*)

Require Import HoTT Coq.Init.Peano.

Local Open Scope path_scope.

(* END OF PREAMBLE *)
(* ================================================== ex:composition *)
(** Exercise 1.1 *)

Definition Book_1_1 := (fun (A B C : Type) (f : A -> B) (g : B -> C) => g o f).

Theorem Book_1_1_refl : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
                          h o (g o f) = (h o g) o f.
Proof.
  reflexivity.
Defined.

(* ================================================== ex:pr-to-rec *)
(** Exercise 1.2 *)

(** Recursor as equivalence. *)
Definition Book_1_2_prod_lib := @HoTT.Types.Prod.equiv_uncurry.
Section Book_1_2_prod.
  Variable A B : Type.

  (** Recursor with projection functions instead of pattern-matching. *)
  Let prod_rec_proj C (g : A -> B -> C) (p : A * B) : C :=
    g (fst p) (snd p).
  Definition Book_1_2_prod := prod_rec_proj.

  Proposition Book_1_2_prod_fst : fst = prod_rec_proj A (fun a b => a).
  Proof.
    reflexivity.
  Defined.

  Proposition Book_1_2_prod_snd : snd = prod_rec_proj B (fun a b => b).
  Proof.
    reflexivity.
  Defined.
End Book_1_2_prod.

(** Recursor as (dependent) equivalence. *)
Definition Book_1_2_sig_lib := @HoTT.Types.Sigma.equiv_sigT_ind.
Section Book_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.

  (** Non-dependent recursor with projection functions instead of pattern matching. *)
  Let sig_rec_proj C (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C :=
    g (pr1 p) (pr2 p).
  Definition Book_1_2_sig := @sig_rec_proj.

  Proposition Book_1_2_sig_fst : @pr1 A B = sig_rec_proj A (fun a => fun b => a).
  Proof.
    reflexivity.
  Defined.

  (** NB: You cannot implement pr2 with only the recursor, so it is not possible
      to check its definitional equality as the exercise suggests. *)
End Book_1_2_sig.

(* ================================================== ex:pr-to-ind *)
(** Exercise 1.3 *)

(** The propositional uniqueness principles are named with an
    'eta' postfix in the HoTT library. *)

Definition Book_1_3_prod_lib := @HoTT.Types.Prod.prod_ind.
Section Book_1_3_prod.
  Variable A B : Type.

  Let prod_ind_eta (C : A * B -> Type) (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x :=
    transport C (HoTT.Types.Prod.eta_prod x) (g (fst x) (snd x)).
  Definition Book_1_3_prod := prod_ind_eta.

  Proposition Book_1_3_prod_refl : forall C g a b, prod_ind_eta C g (a, b) = g a b.
  Proof.
    reflexivity.
  Defined.
End Book_1_3_prod.

Definition Book_1_3_sig_lib := @Coq.Init.Specif.sigT_ind.
Section Book_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.

  Let sig_ind_eta (C : (exists (a : A), B a) -> Type)
                          (g : forall (a : A) (b : B a), C (a; b))
                          (x : exists (a : A), B a) : C x :=
    transport C (HoTT.Types.Sigma.eta_sigma x) (g (pr1 x) (pr2 x)).
  Definition Book_1_3_sig := sig_ind_eta.

  Proposition Book_1_3_sig_refl : forall C g a b, sig_ind_eta C g (a; b) = g a b.
  Proof.
    reflexivity.
  Defined.
End Book_1_3_sig.

(* ================================================== ex:iterator *)
(** Exercise 1.4 *)



(* ================================================== ex:sum-via-bool *)
(** Exercise 1.5 *)



(* ================================================== ex:prod-via-bool *)
(** Exercise 1.6 *)



(* ================================================== ex:pm-to-ml *)
(** Exercise 1.7 *)



(* ================================================== ex:nat-semiring *)
(** Exercise 1.8 *)



(* ================================================== ex:fin *)
(** Exercise 1.9 *)



(* ================================================== ex:ackermann *)
(** Exercise 1.10 *)

Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
               match m with
                 | O => ack p 1
                 | S q => ack p (ackn q)
               end
           in ackn m
  end.

Definition Book_1_10 := ack.

(* ================================================== ex:neg-ldn *)
(** Exercise 1.11 *)



(* ================================================== ex:tautologies *)
(** Exercise 1.12 *)



(* ================================================== ex:not-not-lem *)
(** Exercise 1.13 *)



(* ================================================== ex:without-K *)
(** Exercise 1.14 *)



(* ================================================== ex:subtFromPathInd *)
(** Exercise 1.15 *)

(* concat_A1p? *)

(* ================================================== ex:add-nat-commutative *)
(** Exercise 1.16 *)



(* ================================================== ex:basics:concat *)
(** Exercise 2.1 *)



(* ================================================== ex:eq-proofs-commute *)
(** Exercise 2.2 *)



(* ================================================== ex:fourth-concat *)
(** Exercise 2.3 *)



(* ================================================== ex:npaths *)
(** Exercise 2.4 *)



(* ================================================== ex:ap-to-apd-equiv-apd-to-ap *)
(** Exercise 2.5 *)



(* ================================================== ex:equiv-concat *)
(** Exercise 2.6 *)



(* ================================================== ex:ap-sigma *)
(** Exercise 2.7 *)



(* ================================================== ex:ap-coprod *)
(** Exercise 2.8 *)



(* ================================================== ex:coprod-ump *)
(** Exercise 2.9 *)



(* ================================================== ex:sigma-assoc *)
(** Exercise 2.10 *)



(* ================================================== ex:pullback *)
(** Exercise 2.11 *)



(* ================================================== ex:pullback-pasting *)
(** Exercise 2.12 *)



(* ================================================== ex:eqvboolbool *)
(** Exercise 2.13 *)

Definition Book_2_13 := @HoTT.Types.Bool.equiv_bool_aut_bool.

(* ================================================== ex:equality-reflection *)
(** Exercise 2.14 *)



(* ================================================== ex:strengthen-transport-is-ap *)
(** Exercise 2.15 *)



(* ================================================== ex:strong-from-weak-funext *)
(** Exercise 2.16 *)



(* ================================================== ex:equiv-functor-types *)
(** Exercise 2.17 *)



(* ================================================== ex:equiv-functor-set *)
(** Exercise 3.1 *)

Definition Book_3_1_solution_1 {A B} (f : A <~> B) (H : IsHSet A)
  := @HoTT.Basics.Trunc.trunc_equiv' A B f 0 H.

(** Alternative solutions: [Book_3_1_solution_2] using UA, and [Book_3_1_solution_3] using two easy lemmas that may be of independent interest *)

Lemma Book_3_1_solution_2 `{Univalence} {A B} : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intro e.
  rewrite (path_universe_uncurried e).
  exact idmap.
Defined.

Lemma retr_f_g_path_in_B {A B} (f : A -> B)  (g : B -> A) (alpha : Sect g f) (x y : B) (p : x = y)
      :  p = (alpha x)^ @ (ap f (ap g p)) @ (alpha y).
Proof.
  destruct p.
  simpl.
  rewrite concat_p1.
  rewrite concat_Vp.
  exact 1.
Defined.

Lemma retr_f_g_isHSet_A_so_B {A B} (f : A -> B)  (g : B -> A)
      : Sect g f -> IsHSet A -> IsHSet B.
Proof.
  intros retr_f_g isHSet_A.
  apply @hset_axiomK. unfold axiomK.
  intros x p.
  assert (ap g p = 1) as g_p_is_1. apply (axiomK_hset isHSet_A).
  assert (1 = (retr_f_g x) ^ @ (ap f (ap g p)) @ (retr_f_g x)) as rhs_is_1.
  rewrite g_p_is_1. simpl. rewrite concat_p1. rewrite concat_Vp. exact 1.
  rewrite (rhs_is_1).
  apply (retr_f_g_path_in_B f g retr_f_g).
Defined.

Lemma Book_3_1_solution_3 {A B} : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intros equivalent_A_B isHSet_A.
  elim equivalent_A_B; intros f isequiv_f.
  elim isequiv_f; intros g retr_f_g sect_f_g coh.
  apply (retr_f_g_isHSet_A_so_B f g); assumption.
Defined.

(* ================================================== ex:isset-coprod *)
(** Exercise 3.2 *)

Definition Book_3_2_solution_1 := @HoTT.Types.Sum.hset_sum.

(** Alternative solution for replaying *)

Lemma Book_3_2_solution_2 (A B : Type) : IsHSet A -> IsHSet B -> IsHSet (A+B).
Proof.
  intros isHSet_A isHSet_B.
  apply @hset_axiomK. unfold axiomK. intros x p. destruct x.
  rewrite (inverse (eisretr_path_sum p)).
  rewrite (axiomK_hset isHSet_A a (path_sum_inv p)).
  simpl; exact idpath.
  rewrite (inverse (eisretr_path_sum p)).
  rewrite (axiomK_hset isHSet_B b (path_sum_inv p)).
  simpl; exact idpath.
Defined.

(* ================================================== ex:isset-sigma *)
(** Exercise 3.3 *)

Definition Book_3_3_solution_1 (A : Type) (B : A -> Type)
   := @HoTT.Types.Sigma.trunc_sigma A B 0.

(** This exercise is hard because 2-paths over Sigma types are not treated in the first three chapters of the book. Consult theories/Types/Sigma.v *)

Lemma Book_3_3_solution_2 (A : Type) (B : A -> Type) :
  IsHSet A -> (forall x:A, IsHSet (B x)) -> IsHSet { x:A | B x}.
Proof.
  intros isHSet_A allBx_HSet.
  apply @hset_axiomK. intros x xx.
  pose (path_path_sigma B x x xx 1) as useful.
  apply (useful (axiomK_hset _ _ _) (set_path2 _ _)).
Defined.

(* ================================================== ex:prop-endocontr *)
(** Exercise 3.4 *)

Lemma Book_3_4_solution_1 `{Funext} (A : Type) : IsHProp A <-> Contr (A -> A).
Proof.
  split.
  intro isHProp_A.
  exists idmap.
  apply path_ishprop. (* automagically, from IsHProp A *)
  intro contr_AA.
  apply hprop_allpath; intros a1 a2.
  exact (ap10 (path_contr (fun x:A => a1) (fun x:A => a2)) a1).
Defined.

(* ================================================== ex:prop-inhabcontr *)
(** Exercise 3.5 *)

Definition Book_3_5_solution_1 := @HoTT.HProp.equiv_hprop_inhabited_contr.

(* ================================================== ex:lem-mereprop *)
(** Exercise 3.6 *)

Lemma Book_3_6_solution_1 `{Funext} (A : Type) : IsHProp A -> IsHProp (A + ~A).
Proof.
  intro isHProp_A.
  apply hprop_allpath. intros x y.
  destruct x as [a1|n1]; destruct y as [a2|n2]; apply path_sum; try apply path_ishprop.
  exact (n2 a1). exact (n1 a2).
Defined.

(* ================================================== ex:disjoint-or *)
(** Exercise 3.7 *)

Lemma Book_3_7_solution_1 (A B: Type) :
  IsHProp A -> IsHProp B -> ~(A*B) -> IsHProp (A+B).
Proof.
  intros isHProp_A isProp_B nab.
  apply hprop_allpath. intros x y.
  destruct x as [a1|b1]; destruct y as [a2|b2]; apply path_sum; try apply path_ishprop.
  exact (nab (a1,b2)). exact (nab (a2,b1)).
Defined.

(* ================================================== ex:brck-qinv *)
(** Exercise 3.8 *)



(* ================================================== ex:lem-impl-prop-equiv-bool *)
(** Exercise 3.9 *)

Definition LEM := forall (A : Type), IsHProp A -> A + ~A.

Definition LEM_hProp_Bool (lem : LEM) (hprop : hProp) : Bool
  := match (lem hprop _) with inl _ => true | inr _ => false end.

Lemma Book_3_9_solution_1 `{Univalence} : LEM -> hProp <~> Bool.
Proof.
  intro lem.
  apply (equiv_adjointify (LEM_hProp_Bool lem) is_true).
  - unfold Sect. intros []; simpl.
    + unfold LEM_hProp_Bool. elim (lem Unit_hp _).
      * exact (fun _ => 1).
      * intro nUnit. elim (nUnit tt).
    + unfold LEM_hProp_Bool. elim (lem False_hp _).
      * intro fals. elim fals.
      * exact (fun _ => 1).
  - unfold Sect. intro hprop.
    unfold LEM_hProp_Bool.
    elim (lem hprop _).
    + intro p.
      apply path_hprop; simpl. (* path_prop is silent *)
      exact ((if_hprop_then_equiv_Unit hprop p)^-1)%equiv.
    + intro np.
      apply path_hprop; simpl. (* path_prop is silent *)
      exact ((if_not_hprop_then_equiv_Empty hprop np)^-1)%equiv.
Defined.

(* ================================================== ex:lem-impred *)
(** Exercise 3.10 *)



(* ================================================== ex:not-brck-A-impl-A *)
(** Exercise 3.11 *)



(* ================================================== ex:lem-impl-simple-ac *)
(** Exercise 3.12 *)



(* ================================================== ex:naive-lem-impl-ac *)
(** Exercise 3.13 *)

Section Book_3_13.
  Definition naive_LEM_impl_DN_elim (A : Type) (LEM : A + ~A)
  : ~~A -> A
    := fun nna => match LEM with
                    | inl a => a
                    | inr na => match nna na with end
                  end.

  Lemma naive_LEM_implies_AC
  : (forall A : Type, A + ~A)
    -> forall X A P,
         (forall x : X, ~~{ a : A x | P x a })
         -> { g : forall x, A x | forall x, P x (g x) }.
  Proof.
    intros LEM X A P H.
    pose (fun x => @naive_LEM_impl_DN_elim _ (LEM _) (H x)) as H'.
    exists (fun x => (H' x).1).
    exact (fun x => (H' x).2).
  Defined.

  Lemma Book_3_13 `{Funext}
  : (forall A : Type, A + ~A)
    -> forall X A P,
         IsHSet X
         -> (forall x : X, IsHSet (A x))
         -> (forall x (a : A x), IsHProp (P x a))
         -> (forall x, merely { a : A x & P x a })
         -> merely { g : forall x, A x & forall x, P x (g x) }.
  Proof.
    intros LEM X A P HX HA HP H0.
    apply tr.
    apply (naive_LEM_implies_AC LEM).
    intro x.
    specialize (H0 x).
    revert H0.
    apply Trunc_rec.
    exact (fun x nx => nx x).
  Defined.
End Book_3_13.

(* ================================================== ex:lem-brck *)
(** Exercise 3.14 *)

Section Book_3_14.
  Context `{Funext}.
  Hypothesis LEM : forall A : Type, IsHProp A -> A + ~A.

  Definition Book_3_14
  : forall A (P : ~~A -> Type),
    (forall a, P (fun na => na a))
    -> (forall x y (z : P x) (w : P y), transport P (path_ishprop x y) z = w)
    -> forall x, P x.
  Proof.
    intros A P base p nna.
    assert (forall x, IsHProp (P x)).
    - intro x.
      apply hprop_allpath.
      intros x' y'.
      etransitivity; [ symmetry; apply (p x x y' x') | ].
      assert (H' : idpath = path_ishprop x x) by apply path_ishprop.
      destruct H'.
      reflexivity.
    - destruct (LEM (P nna) _) as [pnna|npnna]; trivial.
      refine (match _ : Empty with end).
      apply nna.
      intro a.
      apply npnna.
      exact (transport P (path_ishprop _ _) (base a)).
  Defined.

  Lemma Book_3_14_equiv A : merely A <~> ~~A.
  Proof.
    apply equiv_iff_hprop.
    - apply Trunc_rec.
      exact (fun a na => na a).
    - intro nna.
      apply (@Book_3_14 A (fun _ => merely A)).
      * exact tr.
      * intros x y z w.
        apply path_ishprop.
      * exact nna.
  Defined.
End Book_3_14.

(* ================================================== ex:impred-brck *)
(** Exercise 3.15 *)



(* ================================================== ex:lem-impl-dn-commutes *)
(** Exercise 3.16 *)



(* ================================================== ex:prop-trunc-ind *)
(** Exercise 3.17 *)



(* ================================================== ex:lem-ldn *)
(** Exercise 3.18 *)



(* ================================================== ex:decidable-choice *)
(** Exercise 3.19 *)



(* ================================================== ex:omit-contr2 *)
(** Exercise 3.20 *)



(* ================================================== ex:isprop-equiv-equiv-bracket *)
(** Exercise 3.21 *)



(* ================================================== ex:finite-choice *)
(** Exercise 3.22 *)



(* ================================================== ex:decidable-choice-strong *)
(** Exercise 3.23 *)



(* ================================================== ex:two-sided-adjoint-equivalences *)
(** Exercise 4.1 *)



(* ================================================== ex:symmetric-equiv *)
(** Exercise 4.2 *)



(* ================================================== ex:qinv-autohtpy-no-univalence *)
(** Exercise 4.3 *)



(* ================================================== ex:unstable-octahedron *)
(** Exercise 4.4 *)



(* ================================================== ex:2-out-of-6 *)
(** Exercise 4.5 *)

Section Book_4_5.
  Section parts.
    Variables A B C D : Type.
    Variable f : A -> B.
    Variable g : B -> C.
    Variable h : C -> D.
    Context `{IsEquiv _ _ (g o f), IsEquiv _ _ (h o g)}.

    Local Instance Book_4_5_g : IsEquiv g.
    Proof.
      apply isequiv_biinv.
      split.
      - exists ((h o g)^-1 o h);
        repeat intro; simpl;
        try apply (@eissect _ _ (h o g)).
      - exists (f o (g o f)^-1);
        repeat intro; simpl;
        try apply (@eisretr _ _ (g o f)).
    Defined.

    Local Instance Book_4_5_f : IsEquiv f.
    Proof.
      apply (isequiv_homotopic (g^-1 o (g o f))); try exact _.
      intro; apply (eissect g).
    Defined.

    Local Instance Book_4_5_h : IsEquiv h.
    Proof.
      apply (isequiv_homotopic ((h o g) o g^-1)); try exact _.
      intro; apply (ap h); apply (eisretr g).
    Defined.

    Definition Book_4_5_hgf : IsEquiv (h o g o f).
    Proof.
      typeclasses eauto.
    Defined.
  End parts.

  (*Lemma Book_4_5 A B f `{IsEquiv A B f} (a a' : A) : IsEquiv (@ap _ _ f a a').
  Proof.
    pose (@ap _ _ (f^-1) (f a) (f a')) as f'.
    pose (fun p : f^-1 (f a) = _ => p @ (@eissect _ _ f _ a')) as g'.
    pose (fun p : _ = a' => (@eissect _ _ f _ a)^ @ p) as h'.
    pose (g' o f').
    pose (h' o g').
    admit.
  Qed.*)
End Book_4_5.

(* ================================================== ex:qinv-univalence *)
(** Exercise 4.6 *)



(* ================================================== ex:embedding-cancellable *)
(** Exercise 4.7 *)



(* ================================================== ex:cancellable-from-bool *)
(** Exercise 4.8 *)



(* ================================================== ex:ind-lst *)
(** Exercise 5.1 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(** Exercise 5.2 *)

Section Book_5_2.
  (** Here is one example of functions which are propositionally equal but not judgmentally equal.  They satisfy the same reucrrence propositionally. *)
  Let ez : Bool := true.
  Let es : nat -> Bool -> Bool := fun _ => idmap.
  Definition Book_5_2_i : nat -> Bool := nat_ind (fun _ => Bool) ez es.
  Definition Book_5_2_ii : nat -> Bool := fun _ => true.
  Fail Definition Book_5_2_not_defn_eq : Book_5_2_i = Book_5_2_ii := idpath.
  Lemma Book_5_2_i_prop_eq : forall n, Book_5_2_i n = Book_5_2_ii n.
  Proof.
    induction n; simpl; trivial.
  Defined.
End Book_5_2.

Section Book_5_2'.
  (** Here's another example where two functions are not (currently) definitionally equal, but satisfy the same reucrrence judgmentally.  This example is a bit less robust; it fails in CoqMT. *)
  Let ez : nat := 1.
  Let es : nat -> nat -> nat := fun _ => S.
  Definition Book_5_2'_i : nat -> nat := fun n => n + 1.
  Definition Book_5_2'_ii : nat -> nat := fun n => 1 + n.
  Fail Definition Book_5_2'_not_defn_eq : Book_5_2'_i = Book_5_2'_ii := idpath.
  Definition Book_5_2'_i_eq_ez : Book_5_2'_i 0 = ez := idpath.
  Definition Book_5_2'_ii_eq_ez : Book_5_2'_ii 0 = ez := idpath.
  Definition Book_5_2'_i_eq_es n : Book_5_2'_i (S n) = es n (Book_5_2'_i n) := idpath.
  Definition Book_5_2'_ii_eq_es n : Book_5_2'_ii (S n) = es n (Book_5_2'_ii n) := idpath.
End Book_5_2'.

(* ================================================== ex:one-function-two-recurrences *)
(** Exercise 5.3 *)

Section Book_5_3.
  Let ez : Bool := true.
  Let es : nat -> Bool -> Bool := fun _ => idmap.
  Let ez' : Bool := true.
  Let es' : nat -> Bool -> Bool := fun _ _ => true.
  Definition Book_5_3 : nat -> Bool := fun _ => true.
  Definition Book_5_3_satisfies_ez : Book_5_3 0 = ez := idpath.
  Definition Book_5_3_satisfies_ez' : Book_5_3 0 = ez' := idpath.
  Definition Book_5_3_satisfies_es n : Book_5_3 (S n) = es n (Book_5_3 n) := idpath.
  Definition Book_5_3_satisfies_es' n : Book_5_3 (S n) = es' n (Book_5_3 n) := idpath.
  Definition Book_5_3_es_ne_es' : ~(es = es')
    := fun H => false_ne_true (ap10 (ap10 H 0) false).
End Book_5_3.

(* ================================================== ex:bool *)
(** Exercise 5.4 *)

Definition Book_5_4 := @HoTT.Types.Bool.equiv_bool_forall_prod.

(* ================================================== ex:ind-nat-not-equiv *)
(** Exercise 5.5 *)

Section Book_5_5.
  Let ind_nat (P : nat -> Type) := fun x => @nat_ind P (fst x) (snd x).

  Lemma Book_5_5 `{fs : Funext} : ~forall P : nat -> Type,
                                     IsEquiv (@ind_nat P).
  Proof.
    intro H.
    specialize (H (fun _ => Bool)).
    pose proof (eissect (@ind_nat (fun _ => Bool)) (true, (fun _ _ => true))) as H1.
    pose proof (eissect (@ind_nat (fun _ => Bool)) (true, (fun _ => idmap))) as H2.
    cut (ind_nat (fun _ : nat => Bool) (true, fun (_ : nat) (_ : Bool) => true)
         = (ind_nat (fun _ : nat => Bool) (true, fun _ : nat => idmap))).
    - intro H'.
      apply true_ne_false.
      exact (ap10 (apD10 (ap snd (H1^ @ ap _ H' @ H2)) 0) false).
    - apply path_forall.
      intro n; induction n; trivial.
      unfold ind_nat in *; simpl in *.
      rewrite <- IHn.
      destruct n; reflexivity.
  Defined.
End Book_5_5.

(* ================================================== ex:no-dep-uniqueness-failure *)
(** Exercise 5.6 *)



(* ================================================== ex:loop *)
(** Exercise 5.7 *)



(* ================================================== ex:loop2 *)
(** Exercise 5.8 *)



(* ================================================== ex:inductive-lawvere *)
(** Exercise 5.9 *)



(* ================================================== ex:ilunit *)
(** Exercise 5.10 *)



(* ================================================== ex:empty-inductive-type *)
(** Exercise 5.11 *)



(* ================================================== ex:Wprop *)
(** Exercise 5.12 *)



(* ================================================== ex:Wbounds *)
(** Exercise 5.13 *)



(* ================================================== ex:Wdec *)
(** Exercise 5.14 *)



(* ================================================== ex:Wbounds-loose *)
(** Exercise 5.15 *)



(* ================================================== ex:Wimpred *)
(** Exercise 5.16 *)



(* ================================================== ex:no-nullary-constructor *)
(** Exercise 5.17 *)



(* ================================================== ex:torus *)
(** Exercise 6.1 *)



(* ================================================== ex:suspS1 *)
(** Exercise 6.2 *)



(* ================================================== ex:torus-s1-times-s1 *)
(** Exercise 6.3 *)



(* ================================================== ex:nspheres *)
(** Exercise 6.4 *)



(* ================================================== ex:susp-spheres-equiv *)
(** Exercise 6.5 *)



(* ================================================== ex:spheres-make-U-not-2-type *)
(** Exercise 6.6 *)



(* ================================================== ex:monoid-eq-prop *)
(** Exercise 6.7 *)



(* ================================================== ex:free-monoid *)
(** Exercise 6.8 *)



(* ================================================== ex:unnatural-endomorphisms *)
(** Exercise 6.9 *)

Section Book_6_9.
  Hypothesis LEM : forall A, IsHProp A -> A + ~A.

  Definition Book_6_9 {ua : Univalence} : forall X, X -> X.
  Proof.
    intro X.
    pose proof (@LEM (Contr { f : X <~> X & ~(forall x, f x = x) }) _) as contrXEquiv.
    destruct contrXEquiv as [[f H]|H].
    - (** In the case where we have exactly one autoequivalence which is not the identity, use it. *)
      exact (f.1).
    - (** In the other case, just use the identity. *)
      exact idmap.
  Defined.

  Lemma bool_map_equiv_not_idmap (f : { f : Bool <~> Bool & ~(forall x, f x = x) })
  : forall b, ~(f.1 b = b).
  Proof.
    intro b.
    intro H''.
    apply f.2.
    intro b'.
    pose proof (eval_bool_isequiv f.1).
    destruct b', b, (f.1 true), (f.1 false);
      simpl in *;
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
  Qed.

  Lemma Book_6_9_not_id {ua : Univalence} `{fs : Funext} : Book_6_9 Bool = negb.
  Proof.
    apply path_forall; intro b.
    unfold Book_6_9.
    destruct (@LEM (Contr { f : Bool <~> Bool & ~(forall x, f x = x) }) _) as [[f H']|H'].
    - pose proof (bool_map_equiv_not_idmap f b).
      destruct (f.1 b), b;
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : ~(_ = _) |- _ ] => exact (match H idpath with end)
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
    - refine (match H' _ with end).
      eexists (existT (fun f : Bool <~> Bool =>
                         ~(forall x, f x = x))
                      (BuildEquiv _ _ negb _)
                      (fun H => false_ne_true (H true)));
        simpl.
      intro f.
      apply path_sigma_uncurried; simpl.
      refine ((fun H'' =>
                 (equiv_path_equiv _ _ H'';
                  path_ishprop _ _))
                _);
        simpl.
      apply path_forall; intro b'.
      pose proof (bool_map_equiv_not_idmap f b').
      destruct (f.1 b'), b';
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : ~(_ = _) |- _ ] => exact (match H idpath with end)
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
  Qed.
End Book_6_9.

(* ================================================== ex:funext-from-interval *)
(** Exercise 6.10 *)



(* ================================================== ex:susp-lump *)
(** Exercise 6.11 *)



(* ================================================== ex:alt-integers *)
(** Exercise 6.12 *)



(* ================================================== ex:trunc-bool-interval *)
(** Exercise 6.13 *)



(* ================================================== ex:all-types-sets *)
(** Exercise 7.1 *)

Section Book_7_1.
  Lemma Book_7_1_part_i (H : forall A, merely A -> A) A : IsHSet A.
  Proof.
    apply (@HoTT.HSet.isset_hrel_subpaths
             A (fun x y => merely (x = y)));
    try typeclasses eauto.
    - intros ?.
      apply tr.
      reflexivity.
    - intros.
      apply H.
      assumption.
  Defined.

  Lemma Book_7_1_part_ii (H : forall A B (f : A -> B),
                                (forall b, merely (hfiber f b))
                                -> forall b, hfiber f b)
  : forall A, IsHSet A.
  Proof.
    apply Book_7_1_part_i.
    intros A a.
    apply (fun H' => (@H A (merely A) tr H' a).1).
    clear a.
    apply Trunc_ind; try exact _.
    intro x; compute; apply tr.
    exists x; reflexivity.
  Defined.
End Book_7_1.

(* ================================================== ex:s2-colim-unit *)
(** Exercise 7.2 *)



(* ================================================== ex:ntypes-closed-under-wtypes *)
(** Exercise 7.3 *)



(* ================================================== ex:connected-pointed-all-section-retraction *)
(** Exercise 7.4 *)



(* ================================================== ex:ntype-from-nconn-const *)
(** Exercise 7.5 *)



(* ================================================== ex:connectivity-inductively *)
(** Exercise 7.6 *)



(* ================================================== ex:lemnm *)
(** Exercise 7.7 *)



(* ================================================== ex:acnm *)
(** Exercise 7.8 *)



(* ================================================== ex:acnm-surjset *)
(** Exercise 7.9 *)



(* ================================================== ex:acconn *)
(** Exercise 7.10 *)



(* ================================================== ex:n-truncation-not-left-exact *)
(** Exercise 7.11 *)



(* ================================================== ex:double-negation-modality *)
(** Exercise 7.12 *)

Definition Book_7_12 := HoTT.Modalities.Notnot.Notnot.

(* ================================================== ex:prop-modalities *)
(** Exercise 7.13 *)

Definition Book_7_13_part_i := @HoTT.Modalities.Open.Op.
Definition Book_7_13_part_ii := @HoTT.Modalities.Closed.Cl.

(* ================================================== ex:f-local-type *)
(** Exercise 7.14 *)



(* ================================================== ex:trunc-spokes-no-hub *)
(** Exercise 7.15 *)



(* ================================================== ex:s2-colim-unit-2 *)
(** Exercise 7.16 *)



(* ================================================== ex:homotopy-groups-resp-prod *)
(** Exercise 8.1 *)



(* ================================================== ex:decidable-equality-susp *)
(** Exercise 8.2 *)



(* ================================================== ex:contr-infinity-sphere-colim *)
(** Exercise 8.3 *)



(* ================================================== ex:contr-infinity-sphere-susp *)
(** Exercise 8.4 *)



(* ================================================== ex:unique-fiber *)
(** Exercise 8.5 *)



(* ================================================== ex:ap-path-inversion *)
(** Exercise 8.6 *)



(* ================================================== ex:pointed-equivalences *)
(** Exercise 8.7 *)



(* ================================================== ex:HopfJr *)
(** Exercise 8.8 *)



(* ================================================== ex:SuperHopf *)
(** Exercise 8.9 *)



(* ================================================== ex:vksusppt *)
(** Exercise 8.10 *)



(* ================================================== ex:vksuspnopt *)
(** Exercise 8.11 *)



(* ================================================== ex:slice-precategory *)
(** Exercise 9.1 *)



(* ================================================== ex:set-slice-over-equiv-functor-category *)
(** Exercise 9.2 *)



(* ================================================== ex:functor-equiv-right-adjoint *)
(** Exercise 9.3 *)



(* ================================================== ct:pre2cat *)
(** Exercise 9.4 *)



(* ================================================== ct:2cat *)
(** Exercise 9.5 *)



(* ================================================== ct:groupoids *)
(** Exercise 9.6 *)



(* ================================================== ex:2strict-cat *)
(** Exercise 9.7 *)



(* ================================================== ex:pre2dagger-cat *)
(** Exercise 9.8 *)



(* ================================================== ct:ex:hocat *)
(** Exercise 9.9 *)



(* ================================================== ex:dagger-rezk *)
(** Exercise 9.10 *)



(* ================================================== ex:rezk-vankampen *)
(** Exercise 9.11 *)



(* ================================================== ex:stack *)
(** Exercise 9.12 *)



(* ================================================== ex:utype-ct *)
(** Exercise 10.1 *)



(* ================================================== ex:surjections-have-sections-impl-ac *)
(** Exercise 10.2 *)



(* ================================================== ex:well-pointed *)
(** Exercise 10.3 *)



(* ================================================== ex:add-ordinals *)
(** Exercise 10.4 *)



(* ================================================== ex:multiply-ordinals *)
(** Exercise 10.5 *)



(* ================================================== ex:algebraic-ordinals *)
(** Exercise 10.6 *)



(* ================================================== ex:prop-ord *)
(** Exercise 10.7 *)



(* ================================================== ex:ninf-ord *)
(** Exercise 10.8 *)



(* ================================================== ex:well-founded-extensional-simulation *)
(** Exercise 10.9 *)



(* ================================================== ex:choice-function *)
(** Exercise 10.10 *)



(* ================================================== ex:cumhierhit *)
(** Exercise 10.11 *)



(* ================================================== ex:strong-collection *)
(** Exercise 10.12 *)



(* ================================================== ex:choice-cumulative-hierarchy-choice *)
(** Exercise 10.13 *)



(* ================================================== ex:plump-ordinals *)
(** Exercise 10.14 *)



(* ================================================== ex:not-plump *)
(** Exercise 10.15 *)



(* ================================================== ex:plump-successor *)
(** Exercise 10.16 *)



(* ================================================== ex:ZF-algebras *)
(** Exercise 10.17 *)



(* ================================================== ex:alt-dedekind-reals *)
(** Exercise 11.1 *)



(* ================================================== ex:RD-extended-reals *)
(** Exercise 11.2 *)



(* ================================================== ex:RD-lower-cuts *)
(** Exercise 11.3 *)



(* ================================================== ex:RD-interval-arithmetic *)
(** Exercise 11.4 *)



(* ================================================== ex:RD-lt-vs-le *)
(** Exercise 11.5 *)



(* ================================================== ex:reals-non-constant-into-Z *)
(** Exercise 11.6 *)



(* ================================================== ex:traditional-archimedean *)
(** Exercise 11.7 *)



(* ================================================== RC-Lipschitz-on-interval *)
(** Exercise 11.8 *)



(* ================================================== ex:metric-completion *)
(** Exercise 11.9 *)



(* ================================================== ex:reals-apart-neq-MP *)
(** Exercise 11.10 *)



(* ================================================== ex:reals-apart-zero-divisors *)
(** Exercise 11.11 *)



(* ================================================== ex:finite-cover-lebesgue-number *)
(** Exercise 11.12 *)



(* ================================================== ex:mean-value-theorem *)
(** Exercise 11.13 *)



(* ================================================== ex:knuth-surreal-check *)
(** Exercise 11.14 *)



(* ================================================== ex:reals-into-surreals *)
(** Exercise 11.15 *)



(* ================================================== ex:ord-into-surreals *)
(** Exercise 11.16 *)



(* ================================================== ex:hiit-plump *)
(** Exercise 11.17 *)



(* ================================================== ex:pseudo-ordinals *)
(** Exercise 11.18 *)
