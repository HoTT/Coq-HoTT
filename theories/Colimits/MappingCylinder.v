(* -*- mode: coq; mode: visual-line -*- *)

(** * Mapping Cylinders *)

Require Import HoTT.Basics HoTT.Types Cubical.DPath Cubical.PathSquare.
Require Import HIT.Coeq Colimits.Pushout.
Local Open Scope path_scope.

(** As in topology, the mapping cylinder of a function [f : A -> B] is a way to replace it with an equivalent cofibration (dually to how [hfiber] replaces it with an equivalent fibration).  We can't talk *internally* in type theory about cofibrations, but we can say metatheoretically what they are: functions with the isomorphism extension property.  So while we can't literally say "let [f] be a cofibration" we can do a mostly equivalent thing and say "let [f] be a map and consider its mapping cylinder".  Replacing a map by a cofibration can be useful because it allows us to make more equalities true definitionally. *)

(** ** Definitions *)

(** We define the mapping cylinder as the pushout of [f] and an identity map.  Peter Lumsdaine has given a definition of HIT mapping cylinders that are dependent on the codomain, so that the second factor is not just an equivalence but a trivial fibration.  However, at the moment we don't have a need for that.  *)

Definition Cyl {A B : Type} (f : A -> B) : Type
  := Pushout idmap f.

Section MappingCylinder.
  Context {A B : Type} {f : A -> B}.

  Definition cyl (a : A) : Cyl f
    := pushl a.
  Definition cyr (b : B) : Cyl f
    := pushr b.

  Definition cyglue (a : A)
    : cyl a = cyr (f a)
    := pglue a.

  Section CylInd.
    Context (P : Cyl f -> Type)
            (cyla : forall a, P (cyl a))
            (cylb : forall b, P (cyr b))
            (cylg : forall a, DPath P (cyglue a) (cyla a) (cylb (f a))).

    Definition Cyl_ind_dp : forall c, P c.
    Proof.
      srapply Pushout_ind.
      - apply cyla.
      - apply cylb.
      - intros a; apply dp_path_transport^-1, cylg.
    Defined.

    Definition Cyl_ind_dp_beta_cyglue (a : A)
      : dp_apD Cyl_ind_dp (cyglue a) = cylg a.
    Proof.
      unfold Cyl_ind_dp.
      refine ((dp_path_transport_apD _ _)^ @ _).
      apply moveR_equiv_M.
      rapply Pushout_ind_beta_pglue.
    Defined.

  End CylInd.

  Section CylRec.
    Context {P : Type} (cyla : A -> P) (cylb : B -> P) (cylg : cyla == cylb o f).

    Definition Cyl_rec : Cyl f -> P.
    Proof.
      srapply Pushout_rec.
      - apply cyla.
      - apply cylb.
      - apply cylg.
    Defined.

    Definition Cyl_rec_beta_cyglue (a : A)
      : ap Cyl_rec (cyglue a) = cylg a.
    Proof.
      rapply Pushout_rec_beta_pglue.
    Defined.

  End CylRec.

  Definition pr_cyl : Cyl f <~> B.
  Proof.
    (** Rather than adjointifying, we give all parts of the equivalence explicitly, so we can be sure of retaining the computational behavior of [eissect] and [eisretr].  However, it's easier to prove [eisadj] on the other side, so we reverse the equivalence first. *)
    symmetry.
    srapply Build_Equiv.
    1:apply cyr.
    srapply Build_IsEquiv.
    - srapply Cyl_rec.
      + exact f.
      + exact idmap.
      + reflexivity.
    - srapply Cyl_ind_dp.
      + intros a; cbn.
        symmetry; apply cyglue.
      + intros b; reflexivity.
      + intros a; cbn.
        apply dp_paths_FFlr.
        rewrite Cyl_rec_beta_cyglue.
        apply concat_pV_p.
    - intros b; reflexivity.
    - intros b; reflexivity.
  Defined.

  Definition ap_pr_cyl_cyglue (a : A)
    : ap pr_cyl (cyglue a) = 1
    := Cyl_rec_beta_cyglue _ _ _ a.

  (** The original map [f] factors definitionally through [Cyl f]. *)
  Definition pr_cyl_cyl (a : A) : pr_cyl (cyl a) = f a
    := 1.

End MappingCylinder.

(** Sometimes we have to specify the map explicitly. *)
Definition cyl' {A B} (f : A -> B) : A -> Cyl f := cyl.
Definition pr_cyl' {A B} (f : A -> B) : Cyl f -> B := pr_cyl.

(** ** Functoriality *)

Section FunctorCyl.
  Context {A B A' B': Type} {f : A -> B} {f' : A' -> B'}
          {ga : A -> A'} {gb : B -> B'}
          (g : f' o ga == gb o f).

  Definition functor_cyl : Cyl f -> Cyl f'.
  Proof.
    srapply Cyl_rec.
    - exact (cyl o ga).
    - exact (cyr o gb).
    - intros a.
      refine (_ @ ap cyr (g a)).
      exact (cyglue (ga a)).
  Defined.

  Definition ap_functor_cyl_cyglue (a : A)
    : ap functor_cyl (cyglue a) = cyglue (ga a) @ ap cyr (g a)
    := Cyl_rec_beta_cyglue _ _ _ a.

  (** The benefit of passing to the mapping cylinder is that it makes a square commute definitionally. *)
  Definition functor_cyl_cyl (a : A) : cyl (ga a) = functor_cyl (cyl a)
    := 1.

  (** The other square also commutes, though not definitionally. *)
  Definition pr_functor_cyl (c : Cyl f)
    : pr_cyl (functor_cyl c) = gb (pr_cyl c)
    := ap (pr_cyl o functor_cyl) (eissect pr_cyl c)^.
      
  Definition pr_functor_cyl_cyl (a : A)
    : pr_functor_cyl (cyl a) = g a.
  Proof.
    (** Here we need [eissect pr_cyl (cyl a)] to compute. *)
    refine (ap _ (inv_V _) @ _).
    refine (ap_compose functor_cyl pr_cyl (cyglue a) @ _).
    refine (ap _ (ap_functor_cyl_cyglue a) @ _).
    refine (ap_pp _ _ _ @ _).
    refine (whiskerR (ap_pr_cyl_cyglue (ga a)) _ @ concat_1p _ @ _).
    refine ((ap_compose cyr _ (g a))^ @ _).
    apply ap_idmap.
  Defined.

End FunctorCyl.

(** ** Coequalizers *)

(** A particularly useful application is to replace a map of coequalizers with one where both squares commute definitionally. *)

Section CylCoeq.
  Context {B A f g B' A' f' g'}
          {h : B -> B'} {k : A -> A'}
          (p : k o f == f' o h) (q : k o g == g' o h).

  Definition CylCoeq : Type
    := Coeq (functor_cyl p) (functor_cyl q).

  Definition cyl_cylcoeq : Coeq f g -> CylCoeq
    := functor_coeq cyl cyl (functor_cyl_cyl p) (functor_cyl_cyl q).

  Definition ap_cyl_cylcoeq_cglue (b : B)
    : ap cyl_cylcoeq (cglue b) = cglue (cyl b).
  Proof.
    etransitivity.
    1:rapply functor_coeq_beta_cglue.
    exact (concat_p1 _ @ concat_1p _).
  Defined.

  Definition pr_cylcoeq : CylCoeq <~> Coeq f' g'
    := equiv_functor_coeq pr_cyl pr_cyl (pr_functor_cyl p) (pr_functor_cyl q).

  Definition ap_pr_cylcoeq_cglue (x : Cyl h)
    : PathSquare (ap pr_cylcoeq (cglue x)) (cglue (pr_cyl x))
                 (ap coeq (pr_functor_cyl p x))
                 (ap coeq (pr_functor_cyl q x)).
  Proof.
    apply sq_path.
    apply moveR_pM.
    rewrite <- (ap_V coeq).
    rapply functor_coeq_beta_cglue.
  Defined.

  Definition pr_cyl_cylcoeq
    : functor_coeq h k p q == pr_cylcoeq o cyl_cylcoeq.
  Proof.
    intros c.
    refine (_ @ functor_coeq_compose cyl cyl (functor_cyl_cyl p) (functor_cyl_cyl q)
              pr_cyl pr_cyl (pr_functor_cyl p) (pr_functor_cyl q) c).
    srapply functor_coeq_homotopy.
    1-2:reflexivity.
    all:intros b; cbn.
    all:refine (concat_1p _ @ concat_1p _ @ _ @ (concat_p1 _)^).
    all:apply pr_functor_cyl_cyl.
  Defined.

End CylCoeq.
