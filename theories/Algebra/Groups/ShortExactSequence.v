From HoTT Require Import Basics Types.
Require Import Truncations.Core.
Require Import WildCat.Core Pointed.Core.
Require Import Groups.Group Groups.Subgroup.
Require Import Universes.HSet.
Require Import Homotopy.ExactSequence Modalities.Identity.

(** * Complexes of groups *)

Definition grp_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C} (cx : IsComplex i f)
  : GroupHomomorphism A (grp_kernel f)
  := grp_kernel_corec _ cx.

Definition grp_iso_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C}
           `{IsEmbedding i} (ex : IsExact (Tr (-1)) i f)
  : GroupIsomorphism A (grp_kernel f)
  := Build_GroupIsomorphism _ _ (grp_cxfib cx_isexact) (isequiv_cxfib ex).

(** [grp_iso_cxfib] definitionally satisfies the homotopy [subgroup_incl (grp_kernel f) o grp_iso_cxfib ex == i].  Therefore, it also satisfies the following variant. *)
Definition grp_iso_cxfib_beta {A B C : Group} {i : A $-> B} {f : B $-> C}
            `{IsEmbedding i} (ex : IsExact (Tr (-1)) i f)
  : i $o grp_iso_inverse (grp_iso_cxfib ex) $== subgroup_incl (grp_kernel f)
  := equiv_cxfib_beta ex.

Definition grp_iscomplex_trivial {X Y : Group} (f : X $-> Y)
  : IsComplex (grp_trivial_rec X) f.
Proof.
  srapply phomotopy_homotopy_hset.
  intro x; cbn.
  exact (grp_homo_unit f).
Defined.

(** If [A -> B -> C] is exact at [B] with [A] contractible, then [B -> C] is an embedding.  Only [B] and [C] need to be groups; [A] can be any pointed type.  Note also that [(-1)]-exactness suffices, which is what one gets from a fiber sequence after truncating. *)
Definition isembedding_isexact {A : pType} {B C : Group} {i : A ->* B} {f : B $-> C}
  `{Contr A} (ex : IsExact (Tr (-1)) i f)
  : IsEmbedding f.
Proof.
  (* Since [A] is contractible and [B] is a set, [i] is an embedding, which upgrades exactness to an equivalence between [A] and the fiber of [f] over the identity. This is needed by [equiv_cxfib]. *)
  assert (IsEmbedding i) by (intro b; rapply istrunc_sigma).
  intro c.
  apply hprop_inhabited_contr; intro b.
  rapply (contr_equiv' A).
  exact ((equiv_grp_hfiber f c b)^-1 oE equiv_cxfib ex).
Defined.

(** A complex 0 -> A -> B of groups is purely exact if and only if the map A -> B is an embedding. (This is also true with [purely] replaced by [Tr (-1)].) *)
Lemma iff_grp_isexact_isembedding {A B : Group} (f : A $-> B)
  : IsExact purely (grp_trivial_rec A) f <-> IsEmbedding f.
Proof.
  split.
  - intro ex.
    exact (isembedding_isexact (isexact_purely_O _ _ (H:=ex))).
  - intro isemb_f.
    exists (grp_iscomplex_trivial f).
    intros y; rapply contr_inhabited_hprop.
    exists tt; apply path_ishprop.
Defined.

(** A complex 0 -> A -> B is purely exact if and only if the kernel of the map A -> B is trivial. *)
Definition equiv_grp_isexact_kernel `{Univalence} {A B : Group} (f : A $-> B)
  : IsExact purely (grp_trivial_rec A) f <~> IsTrivialGroup (grp_kernel f)
  := (equiv_istrivial_kernel_isembedding f)^-1%equiv
       oE equiv_iff_hprop_uncurried (iff_grp_isexact_isembedding f).

(** Two maps which are exact at [B] with respect to the same [f] are both the kernel of [f], so they are isomorphic. *)
Definition grp_iso_isexact_isexact {A B C D : Group}
  {i : A $-> B} {j : C $-> B} {f : B $-> D}
  `{IsEmbedding i} `{IsEmbedding j}
  (exi : IsExact (Tr (-1)) i f) (exj : IsExact (Tr (-1)) j f)
  : GroupIsomorphism A C
  := grp_iso_compose (grp_iso_inverse (grp_iso_cxfib exj)) (grp_iso_cxfib exi).

(** The isomorphism commutes with the embeddings. *)
Definition grp_iso_isexact_isexact_beta {A B C D : Group}
  {i : A $-> B} {j : C $-> B} {f : B $-> D}
  `{IsEmbedding i} `{IsEmbedding j}
  (exi : IsExact (Tr (-1)) i f) (exj : IsExact (Tr (-1)) j f)
  : j $o grp_iso_isexact_isexact exi exj $== i
  := fun a => grp_iso_cxfib_beta exj (grp_iso_cxfib exi a).

(** Any factorization of [i] through [j] is therefore an equivalence, being homotopic to that isomorphism. *)
Definition isequiv_isexact_factor {A B C D : Group}
  {i : A $-> B} {j : C $-> B} (k : A $-> C) {f : B $-> D}
  (p : j $o k $== i) `{IsEmbedding i} `{IsEmbedding j}
  (exi : IsExact (Tr (-1)) i f) (exj : IsExact (Tr (-1)) j f)
  : IsEquiv k.
Proof.
  rapply (isequiv_homotopic (grp_iso_isexact_isexact exi exj)).
  intro a.
  rapply (isinj_embedding j).
  lhs napply (grp_iso_isexact_isexact_beta exi exj).
  exact (p a)^.
Defined.

(** If [A -> B -> C -> D] is exact at [B] and [C], with [A] and [D] contractible, then the middle map is an isomorphism.  Only [B] and [C] need to be groups. *)
Definition grp_iso_isexact {A : pType} {B C : Group} {D : pType}
  {h : A ->* B} {f : B $-> C} {g : C ->* D} `{Contr A} `{Contr D}
  (exl : IsExact (Tr (-1)) h f) (exr : IsExact (Tr (-1)) f g)
  : GroupIsomorphism B C.
Proof.
  snapply (Build_GroupIsomorphism _ _ f).
  napply isequiv_surj_emb.
  - exact (isconnmap_O_isexact_base_contr _ f g).
  - exact (isembedding_isexact exl).
Defined.
