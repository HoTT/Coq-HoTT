From HoTT Require Import Basics Types AbelianGroup AbPushout
  WildCat.Core Modalities.ReflectiveSubuniverse Truncations.Core.

(** * Injective abelian groups *)

(** We define injective abelian groups and show that [I] is injective if and only if every monomorphism [I -> B] merely splits.  This is dual to [AbProjective]. *)

(** An abelian group [I] is injective if for any map [f : A -> I] and embedding [m : A -> B], there merely exists an extension [g : B -> I] with [g $o m == f]. *)
Class IsAbInjective@{u +} (I : AbGroup@{u}) : Type :=
  isabinjective : forall (A B : AbGroup@{u}), forall (m : A $-> B),
    forall (f : A $-> I), IsEmbedding m -> merely (exists g : B $-> I, g $o m == f).

(** An abelian group is injective iff monos out of it merely split. *)
Proposition iff_isabinjective_embeddings_split `{Univalence} (I : AbGroup)
  : IsAbInjective I
    <-> (forall B, forall m : I $-> B, IsEmbedding m ->
                           merely (exists r : B $-> I, r $o m == grp_homo_id)).
Proof.
  split.
  - intros hinj B m.
    apply hinj.
  - intros hsplit A B m f hm.
    pose proof (s := hsplit (ab_pushout f m) ab_pushout_inl
                       (ab_pushout_embedding_inl f m)).
    strip_truncations.
    destruct s as [r h].
    refine (tr (r $o ab_pushout_inr; _)); intro a.
    refine (ap r (ab_pushout_commsq a)^ @ _).
    exact (h (f a)).
Defined.
