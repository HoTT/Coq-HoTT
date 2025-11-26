From HoTT Require Import Basics Types AbelianGroup AbPullback
  WildCat.Core Limits.Pullback ReflectiveSubuniverse Truncations.Core.

(** * Projective abelian groups *)

(** We define projective abelian groups and show that [P] is projective if and only if every epimorphism [A -> P] merely splits. *)

(** An abelian group [P] is projective if for any map [P -> B] and epimorphism [A -> B], there merely exists a lift [P -> A] making the following triangle commute:

              A
            ^ |
         l /  |
              | e
         /    |
              V
       P ---> B
          f
*)
Class IsAbProjective@{u +} (P : AbGroup@{u}) : Type :=
  isabprojective : forall (A B : AbGroup@{u}), forall (e : A $-> B),
    forall (f : P $-> B), IsSurjection e -> merely (exists l : P $-> A, e $o l == f).

(** An abelian group is projective iff epis into it merely split. *)
Proposition iff_isabprojective_surjections_split (P : AbGroup)
  : IsAbProjective P
    <-> (forall A, forall p : A $-> P, IsSurjection p ->
                           merely (exists s : P $-> A, p $o s == grp_homo_id)).
Proof.
  split.
  - intros H A B.
    apply H.
  - intros H A B e f H1.
    pose proof (s := H (ab_pullback f e) (grp_pullback_pr1 f e)
                       (conn_map_pullback _ f e)).
    strip_truncations.
    destruct s as [s h].
    refine (tr ((grp_pullback_pr2 f e) $o s; _)); intro x.
    refine ((pullback_commsq f e _)^ @ _).
    exact (ap f (h x)).
Defined.
