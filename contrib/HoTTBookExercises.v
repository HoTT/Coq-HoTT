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

Require Import HoTT HoTT.hit.minus1Trunc.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* END OF PREAMBLE *)
(* ================================================== ex:composition *)
(** Exercise 1.1 *)

Definition Book_1_1 := @compose.

Theorem Book_1_1_refl : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
                          h o (g o f) = (h o g) o f.
Proof.
  reflexivity.
Defined.

(* ================================================== ex:pr-to-rec *)
(** Exercise 1.2 *)

(** Recursor as equivalence. *)
Definition Book_1_2_prod_lib := @HoTT.types.Prod.equiv_uncurry.
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
Definition Book_1_2_sig_lib := @HoTT.types.Sigma.equiv_sigT_rect.
Section Book_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.

  (** Non-dependent recursor with projection functions instead of pattern matching. *)
  Let sig_rec_proj C (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C :=
    g (projT1 p) (projT2 p).
  Definition Book_1_2_sig := @sig_rec_proj.

  Proposition Book_1_2_sig_fst : @projT1 A B = sig_rec_proj A (fun a => fun b => a).
  Proof.
    reflexivity.
  Defined.

  (** NB: You cannot implement projT2 with only the recursor, so it is not possible
      to check its definitional equality as the exercise suggests. *)
End Book_1_2_sig.

(* ================================================== ex:pr-to-ind *)
(** Exercise 1.3 *)

(** The propositional uniqueness principles are named with an
    'eta' postfix in the HoTT library. *)

Definition Book_1_3_prod_lib := @Coq.Init.Datatypes.prod_rect.
Section Book_1_3_prod.
  Variable A B : Type.

  Let prod_ind_eta (C : A * B -> Type) (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x :=
    transport C (HoTT.types.Prod.eta_prod x) (g (fst x) (snd x)).
  Definition Book_1_3_prod := prod_ind_eta.

  Proposition Book_1_3_prod_refl : forall C g a b, prod_ind_eta C g (a, b) = g a b.
  Proof.
    reflexivity.
  Defined.
End Book_1_3_prod.

Definition Book_1_3_sig_lib := @Coq.Init.Specif.sigT_rect.
Section Book_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.

  Let sig_ind_eta (C : (exists (a : A), B a) -> Type)
                          (g : forall (a : A) (b : B a), C (a; b))
                          (x : exists (a : A), B a) : C x :=
    transport C (HoTT.types.Sigma.eta_sigma x) (g (projT1 x) (projT2 x)).
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



(* ================================================== ex:isset-coprod *)
(** Exercise 3.2 *)



(* ================================================== ex:isset-sigma *)
(** Exercise 3.3 *)



(* ================================================== ex:prop-endocontr *)
(** Exercise 3.4 *)



(* ================================================== ex:prop-inhabcontr *)
(** Exercise 3.5 *)



(* ================================================== ex:lem-mereprop *)
(** Exercise 3.6 *)



(* ================================================== ex:disjoint-or *)
(** Exercise 3.7 *)



(* ================================================== ex:brck-qinv *)
(** Exercise 3.8 *)



(* ================================================== ex:lem-impl-prop-equiv-bool *)
(** Exercise 3.9 *)



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
         -> (forall x, minus1Trunc { a : A x & P x a })
         -> minus1Trunc { g : forall x, A x & forall x, P x (g x) }.
  Proof.
    intros LEM X A P HX HA HP H0.
    apply min1.
    apply (naive_LEM_implies_AC LEM).
    intro x.
    specialize (H0 x).
    revert H0.
    apply minus1Trunc_rect_nondep.
    - exact (fun x nx => nx x).
    - apply allpath_hprop.
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
    -> (forall x y (z : P x) (w : P y), transport P (allpath_hprop x y) z = w)
    -> forall x, P x.
  Proof.
    intros A P base p nna.
    assert (forall x, IsHProp (P x)).
    - intro x.
      apply hprop_allpath.
      intros x' y'.
      etransitivity; [ apply symmetry; apply (p x x y' x') | ].
      assert (H' : idpath = allpath_hprop x x) by apply allpath_hprop.
      destruct H'.
      reflexivity.
    - destruct (LEM (P nna) _) as [pnna|npnna]; trivial.
      refine (match _ : Empty with end).
      apply nna.
      intro a.
      apply npnna.
      exact (transport P (allpath_hprop _ _) (base a)).
  Defined.

  Lemma Book_3_14_equiv A : minus1Trunc A <~> ~~A.
  Proof.
    apply equiv_iff_hprop.
    - apply minus1Trunc_rect_nondep.
      * exact (fun a na => na a).
      * apply allpath_hprop.
    - intro nna.
      apply (@Book_3_14 A (fun _ => minus1Trunc A)).
      * exact min1.
      * intros x y z w.
        apply min1_path.
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
      apply equiv_biinv.
      split.
      - exists ((h o g)^-1 o h);
        repeat intro; simpl;
        try apply (@eissect _ _ (h o g)).
      - exists (f o (g o f)^-1);
        repeat intro; simpl;
        try apply (@eisretr _ _ (g o f)).
    Defined.

    (** We use [Proof with try typeclasses eauto] to make typeclass resolution pick up the proofs that [g⁻¹ ∘ (g ∘ f)] and [(h ∘ g) ∘ g⁻¹] are equivalences automatically when we type [...]. *)
    Local Instance Book_4_5_f : IsEquiv f.
    Proof with try typeclasses eauto.
      apply (@isequiv_homotopic _ _ (g^-1 o (g o f)))...
      intro; apply (eissect g).
    Defined.

    Local Instance Book_4_5_h : IsEquiv h.
    Proof with try typeclasses eauto.
      apply (@isequiv_homotopic _ _ ((h o g) o g^-1))...
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



(* ================================================== ex:ind-lst *)
(** Exercise 5.1 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(** Exercise 5.2 *)



(* ================================================== ex:one-function-two-recurrences *)
(** Exercise 5.3 *)



(* ================================================== ex:bool *)
(** Exercise 5.4 *)



(* ================================================== ex:ind-nat-not-equiv *)
(** Exercise 5.5 *)



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



(* ================================================== ex:funext-from-interval *)
(** Exercise 6.10 *)



(* ================================================== ex:susp-lump *)
(** Exercise 6.11 *)



(* ================================================== ex:alt-integers *)
(** Exercise 6.12 *)



(* ================================================== ex:all-types-sets *)
(** Exercise 7.1 *)



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



(* ================================================== ex:prop-modalities *)
(** Exercise 7.13 *)



(* ================================================== ex:f-local-type *)
(** Exercise 7.14 *)



(* ================================================== ex:trunc-spokes-no-hub *)
(** Exercise 7.15 *)



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
