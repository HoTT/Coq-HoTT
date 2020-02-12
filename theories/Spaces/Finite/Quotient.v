Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Colimits.Quotient.
Require Import Spaces.Nat.
Require Import Spaces.Finite.Core.
Require Import Spaces.Finite.Finite.
Require Import Truncations.
Require Import UnivalenceImpliesFunext.
Import TrM.

(** ** Quotients *)

(** The quotient of a finite set by a detachable equivalence relation is finite. *)

Section DecidableQuotients.

  Context
   `{Univalence}
    {X : Type} `{Finite X}
    (R : Relation X) `{is_mere_relation X R}
   `{!Reflexive R} `{!Transitive R} `{!Symmetric R}
    {Rd : forall x y, Decidable (R x y)}.

  Global Instance finite_quotient : Finite (Quotient R).
  Proof.
    assert (e := merely_equiv_fin X).
    strip_truncations.
    pose (R' x y := R (e^-1 x) (e^-1 y)).
    assert (is_mere_relation _ R') by exact _.
    assert (Reflexive R') by (intros ?; unfold R'; apply reflexivity).
    assert (Symmetric R') by (intros ? ?; unfold R'; apply symmetry).
    assert (Transitive R') by (intros ? ? ?; unfold R'; apply transitivity).
    assert (R'd : forall x y, Decidable (R' x y))
      by (intros ? ?; unfold R'; apply Rd).
    srefine (finite_equiv _ (equiv_quotient_functor R' R e^-1 _) _).
    1: by try (intros; split).
    clearbody R'; clear e.
    generalize dependent (fcard X);
      intros n; induction n as [|n IH]; intros R' ? ? ? ? ?.
    { refine (finite_isequiv Empty _^-1 _).
      refine (Quotient_rec R' _ Empty_rec (fun x _ _ => match x with end)). }
    pose (R'' x y := R' (inl x) (inl y)).
    assert (is_mere_relation _ R'') by exact _.
    assert (Reflexive R'') by (intros ?; unfold R''; apply reflexivity).
    assert (Symmetric R'') by (intros ? ?; unfold R''; apply symmetry).
    assert (Transitive R'') by (intros ? ? ?; unfold R''; apply transitivity).
    assert (forall x y, Decidable (R'' x y)) by (intros ? ?; unfold R''; apply R'd).
    assert (inlresp := (fun x y => idmap)
                       : forall x y, R'' x y -> R' (inl x) (inl y)).
    destruct (dec (merely {x:Fin n & R' (inl x) (inr tt)})) as [p|np].
    { strip_truncations.
      destruct p as [x r].
      refine (finite_equiv (Quotient R'') _ _).
      refine (Build_Equiv _ _ (Quotient_functor R'' R' inl inlresp) _).
      apply isequiv_surj_emb.
      - apply BuildIsSurjection.
        refine (Quotient_ind_hprop R' _ _).
        intros [y|[]]; apply tr.
        + exists (class_of R'' y); reflexivity.
        + exists (class_of R'' x); simpl.
          apply qglue, r.
      - apply isembedding_isinj_hset; intros u.
        refine (Quotient_ind_hprop R'' _ _); intros v.
        revert u; refine (Quotient_ind_hprop R'' _ _); intros u.
        simpl; intros q.
        apply qglue; unfold R''.
        exact (related_quotient_paths R' (inl u) (inl v) q). }
    refine (finite_equiv (Quotient R'' + Unit) _ _).
    refine (Build_Equiv _ _ (sum_ind (fun _ => Quotient R')
                                    (Quotient_functor R'' R' inl inlresp)
                                    (fun _ => class_of R' (inr tt))) _).
    apply isequiv_surj_emb.
    - apply BuildIsSurjection.
      refine (Quotient_ind_hprop R' _ _).
      intros [y|[]]; apply tr.
      + exists (inl (class_of R'' y)); reflexivity.
      + exists (inr tt); reflexivity.
    - apply isembedding_isinj_hset; intros u.
      refine (sum_ind _ _ _).
      + refine (Quotient_ind_hprop R'' _ _); intros v.
        revert u; refine (sum_ind _ _ _).
        * refine (Quotient_ind_hprop R'' _ _); intros u.
          simpl; intros q.
          apply ap, qglue; unfold R''.
          exact (related_quotient_paths R' (inl u) (inl v) q).
        * intros []; simpl.
          intros q.
          apply related_quotient_paths in q; try exact _.
          apply symmetry in q.
          elim (np (tr (v ; q))).
      + intros []; simpl.
        destruct u as [u|[]]; simpl.
        * revert u; refine (Quotient_ind_hprop R'' _ _); intros u; simpl.
          intros q.
          apply related_quotient_paths in q; try exact _.
          elim (np (tr (u;q))).
        * intros; reflexivity.
  Defined.

  (** Therefore, the cardinality of [X] is the sum of the cardinalities of its equivalence classes. *)
  Definition fcard_quotient
    : fcard X = finplus (fun z:Quotient R => fcard {x:X & in_class R z x}).
  Proof.
    refine (fcard_domain (class_of R) @ _).
    apply ap, path_arrow; intros z; revert z.
    refine (Quotient_ind_hprop _ _ _); intros x; simpl.
    apply fcard_equiv; unfold hfiber.
    refine (equiv_functor_sigma_id _); intros y; simpl.
    symmetry.
    refine (path_quotient R y x oE _).
    apply equiv_iff_hprop; apply symmetry.
  Defined.

End DecidableQuotients.
