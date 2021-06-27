Require Import HoTT.Basics HoTT.Types.
Require Import HSet HFiber Factorization HoTT.Truncations HProp.
Require Import Pointed.Core Pointed.pMap Pointed.pEquiv Pointed.pHomotopy.
Require Import WildCat.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A) : IsPointed (a = a) := 1.

Definition loops (A : pType) : pType
  := Build_pType (point A = point A) _.

Fixpoint iterated_loops (n : nat) (A : pType) : pType
  := match n with
       | O => A
       | S p => loops (iterated_loops p A)
     end.

(* Inner unfolding for iterated loops *)
Lemma unfold_iterated_loops (n : nat) (X : pType)
  : iterated_loops n.+1 X = iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  by refine (ap loops IHn @ _).
Defined.

(** The loop space decreases the truncation level by one.  We don't bother making this an instance because it is automatically found by typeclass search, but we record it here in case anyone is looking for it. *)
Definition istrunc_loops {n} (A : pType) `{IsTrunc n.+1 A}
  : IsTrunc n (loops A) := _.

(** Similarly for connectedness. *)
Definition isconnected_loops `{Univalence} {n} (A : pType)
  `{IsConnected n.+1 A} : IsConnected n (loops A) := _.

Lemma pequiv_loops_punit : loops pUnit <~>* pUnit.
Proof.
  snrapply Build_pEquiv'.
  { srapply (equiv_adjointify (fun _ => tt) (fun _ => idpath)).
    1: by intros [].
    rapply path_contr. }
  reflexivity.
Defined. 

(** ** Functoriality of loop spaces *)

(** Action on 1-cells *)
Global Instance is0functor_loops : Is0Functor loops.
Proof.
  apply Build_Is0Functor.
  intros A B f.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  refine (_ @ concat_Vp (point_eq f)).
  apply whiskerL. apply concat_1p.
Defined.

Global Instance is1functor_loops : Is1Functor loops.
Proof.
  apply Build_Is1Functor.
  (** Action on 2-cells *)
  - intros A B f g p.
    pointed_reduce.
    srapply Build_pHomotopy; cbn.
    { intro q.
      refine (_ @ (concat_p1 _)^ @ (concat_1p _)^).
      apply moveR_Vp.
      apply (concat_Ap (fun x => p x @ 1)). }
    simpl. generalize (p point0). generalize (g point0).
    intros _ []. reflexivity.
  (** Preservation of identity. *)
  - intros A.
    srapply Build_pHomotopy.
    { intro p.
      refine (concat_1p _ @ concat_p1 _ @ ap_idmap _). }
    reflexivity.
  (** Preservation of compositon. *)
  - intros A B c g f.
    srapply Build_pHomotopy.
    { intros p. cbn.
      refine ((inv_pp _ _ @@ 1) @ concat_pp_p _ _ _ @ _).
      apply whiskerL.
      refine (((ap_V _ _)^ @@ 1) @ _ @ concat_p_pp _ _ _ @ ((ap_pp _ _ _)^ @@ 1)).
      apply whiskerL.
      refine (_ @ concat_p_pp _ _ _ @ ((ap_pp _ _ _)^ @@ 1)).
      apply whiskerR.
      apply ap_compose. }
    by pointed_reduce.
Defined.

(** *** Properties of loops functor *)

(** Loops functor distributes over concatenation *)
Lemma fmap_loops_pp {X Y : pType} (f : X ->* Y) (x y : loops X)
  : fmap loops f (x @ y) = fmap loops f x @ fmap loops f y.
Proof.
  pointed_reduce_rewrite.
  apply ap_pp.
Defined.

(** Loops is a pointed functor *)
Global Instance ispointedfunctor_loops : IsPointedFunctor loops.
Proof.
  rapply Build_IsPointedFunctor'.
  apply pequiv_loops_punit.
Defined.

Lemma fmap_loops_pconst {A B : pType} : fmap loops (@pconst A B) ==* pconst.
Proof.
  rapply fmap_zero_morphism.
Defined.

(** *** Iterated loops functor *)

(** Action on 1-cells *)
Global Instance is0functor_iterated_loops n : Is0Functor (iterated_loops n).
Proof.
  induction n.
  1: exact _.
  rapply is0functor_compose.
Defined.

Global Instance is1functor_iterated_loops n : Is1Functor (iterated_loops n).
Proof.
  induction n.
  1: exact _.
  rapply is1functor_compose.
Defined.

Lemma fmap_iterated_loops_pp {X Y : pType} (f : X ->* Y) n
  (x y : iterated_loops n.+1 X)
  : fmap (iterated_loops n.+1) f (x @ y)
    = fmap (iterated_loops n.+1) f x @ fmap (iterated_loops n.+1) f y.
Proof.
  apply fmap_loops_pp.
Defined.

(** The fiber of [fmap loops f] is equivalent to a fiber of [ap f]. *)
Definition hfiber_fmap_loops {A B : pType} (f : A ->* B) (p : loops B)
  : {q : loops A & ap f q = (point_eq f @ p) @ (point_eq f)^}
    <~> hfiber (fmap loops f) p.
Proof.
  apply equiv_functor_sigma_id; intros q.
  refine (equiv_moveR_Vp _ _ _ oE _).
  apply equiv_moveR_pM.
Defined.

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_fmap_loops {n} (A B : pType) (f : A ->* B)
  `{IsTruncMap n.+1 _ _ f} : IsTruncMap n (fmap loops f).
Proof.
  intro p. apply (istrunc_equiv_istrunc _ (hfiber_fmap_loops f p)).
Defined.

(** And likewise the connectedness.  *)
Global Instance isconnected_fmap_loops `{Univalence} {n : trunc_index}
  (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
  : IsConnMap n (fmap loops f).
Proof.
  intros p; eapply isconnected_equiv'.
  - refine (hfiber_fmap_loops f p oE _).
    symmetry; apply hfiber_ap.
  - exact _.
Defined.

Definition isconnected_iterated_fmap_loops `{Univalence}
  (k : nat) (A B : pType) (f : A ->* B)
  : forall n : trunc_index, IsConnMap (trunc_index_inc' n k) f
                       -> IsConnMap n (fmap (iterated_loops k) f).
Proof.
  induction k; intros n C.
  - exact C.
  - apply isconnected_fmap_loops.
    apply IHk.
    exact C.
Defined.

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} n {A B : pType} (f : A ->* B)
  : loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
  <~> image n (fmap loops f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization
    (@IsConnMap n) (@MapIn n) (fmap loops f))).
  { refine (@Build_Factorization (@IsConnMap n) (@MapIn n)
      (loops A) (loops B) (fmap loops f) (loops C)
      (fmap loops g) (fmap loops h) _ _ _).
    intros x; symmetry.
    refine (_ @ fmap_comp loops g h x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate (path_factor (O_factsys n) (fmap loops f) I
    (image n (fmap loops f)))).
Defined.

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  srapply Build_pEquiv.
  1: exact (Build_pMap (loops A) (loops A) inverse 1).
  apply isequiv_path_inverse.
Defined.

(** Loops functor preserves equivalences *)
Definition pequiv_fmap_loops {A B : pType}
  : A $<~> B -> loops A $<~> loops B
  := emap loops.

(** A version of [unfold_iterated_loops] that's an equivalence rather than an equality.  We could get this from the equality, but it's more useful to construct it explicitly since then we can reason about it.  *)
Definition unfold_iterated_loops' (n : nat) (X : pType)
  : iterated_loops n.+1 X <~>* iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  apply pequiv_fmap_loops, IHn.
Defined.

(** For instance, we can prove that it's natural. *)
Definition unfold_iterated_fmap_loops {A B : pType} (n : nat) (f : A ->* B)
  : (unfold_iterated_loops' n B) o* (fmap (iterated_loops n.+1) f)
    ==* (fmap (iterated_loops n) (fmap loops f)) o* (unfold_iterated_loops' n A).
Proof.
  induction n.
  - srefine (Build_pHomotopy _ _).
    + reflexivity.
    + cbn. apply moveL_pV.
      refine (concat_1p _ @ _).
      refine (concat_1p _ @ _).
      refine (_ @ (concat_p1 _)^).
      exact ((ap_idmap _)^).
  - refine ((fmap_comp loops _ _)^* @* _).
    refine (_ @* (fmap_comp loops _ _)).
    rapply (fmap2 loops).
    apply IHn.
Defined.

(** Iterated loops preserves equivalences *)
Definition pequiv_fmap_iterated_loops {A B} n
  : A <~>* B -> iterated_loops n A <~>* iterated_loops n B
  := emap (iterated_loops n).

(* Loops preserves products *)
Lemma loops_prod (X Y : pType) : loops (X * Y) <~>* loops X * loops Y.
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: symmetry; refine (equiv_path_prod (point _) (point (X * Y))).
  reflexivity.
Defined.

(* Iterated loops of products are products of iterated loops *)
Lemma iterated_loops_prod (X Y : pType) {n}
  : iterated_loops n (X * Y) <~>* (iterated_loops n X) * (iterated_loops n Y).
Proof.
  induction n.
  1: reflexivity.
  refine (pequiv_compose _ (loops_prod _ _)).
  by rapply (emap loops).
Defined.

(* A dependent form of loops *)
Definition loopsD {A} : pFam A -> pFam (loops A)
  := fun Pp => (fun q => transport Pp.1 q Pp.2 = Pp.2; 1).

Global Instance istrunc_pfam_loopsD {n} {A} (P : pFam A)
       {H :IsTrunc_pFam n.+1 P}
  : IsTrunc_pFam n (loopsD P).
Proof.
  intros a. pose (H (point A)). exact _.
Defined.

(* psigma and loops 'commute' *)
Lemma loops_psigma_commute (A : pType) (P : pFam A)
  : loops (psigma P) <~>* psigma (loopsD P).
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: exact (equiv_path_sigma _ _ _)^-1%equiv.
  reflexivity.
Defined.

(* product and loops 'commute' *)
Lemma loops_pproduct_commute `{Funext} (A : Type) (F : A -> pType)
  : loops (pproduct F) <~>* pproduct (loops o F).
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: apply equiv_apD10.
  reflexivity.
Defined.

(* product and iterated loops commute *)
Lemma iterated_loops_pproduct_commute `{Funext} (A : Type) (F : A -> pType) (n : nat)
  : iterated_loops n (pproduct F) <~>* pproduct (iterated_loops n o F).
Proof.
  induction n.
  1: reflexivity.
  refine (loops_pproduct_commute _ _ o*E _).
  rapply (emap loops).
  exact IHn.
Defined.

(* Loops neutralise sigmas when truncated *)
Lemma loops_psigma_trunc (n : nat) : forall (Aa : pType)
  (Pp : pFam Aa) (istrunc_Pp : IsTrunc_pFam (trunc_index_inc minus_two n) Pp),
  iterated_loops n (psigma Pp)
  <~>* iterated_loops n Aa.
Proof.
  induction n.
  { intros A P p.
    srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
    1: refine (@equiv_sigma_contr _ _ p).
    reflexivity. }
  intros A P p.
  refine (pequiv_inverse (unfold_iterated_loops' _ _) o*E _ o*E unfold_iterated_loops' _ _).
  refine (IHn _ _ _ o*E _).
  rapply (emap (iterated_loops _)).
  apply loops_psigma_commute.
Defined.

(* We declare this local notation to make it easier to write pointed types *)
Local Notation "( X , x )" := (Build_pType X x).

(** In the following lemmas we have used universe annotations explicitly as without them, coq cannot guess the universe levels correctly. Defining pointed maps as a special case of pForall has the side effect of raising the universe level since pForall requires a bigger universe for the type family. Hopefully in the future, coq's "universe guessing" will be smarter and we can drop the annotations here. *)

(* We can convert between families of loops in a type and loops in Type at that type. *)
Definition loops_type@{i j k} `{Univalence} (A : Type@{i})
  : pEquiv@{j j k} (loops@{j} (Build_pType@{j} Type@{i} A))
          (A <~> A, equiv_idmap).
Proof.
  apply issig_pequiv'.
  exists (equiv_equiv_path A A).
  reflexivity.
Defined.

Lemma local_global_looping `{Univalence} (A : Type@{i}) (n : nat)
  : iterated_loops@{j} n.+2 (Type@{i}, A)
    <~>* pproduct (fun a => iterated_loops@{j} n.+1 (A, a)).
Proof.
  induction n.
  { refine (_ o*E emap loops (loops_type A)).
    apply issig_pequiv'.
    exists (equiv_inverse (equiv_path_arrow 1%equiv 1%equiv)
            oE equiv_inverse (equiv_path_equiv 1%equiv 1%equiv)).
    reflexivity. }
  exact (loops_pproduct_commute _ _ o*E emap loops IHn).
Defined.

(* 7.2.7 *)
Theorem equiv_istrunc_istrunc_loops `{Univalence} n X
  : IsTrunc n.+2 X <~> forall x, IsTrunc n.+1 (loops (X, x)).
Proof.
  srapply equiv_iff_hprop.
  intro tr_loops.
  intros x y p.
  destruct p.
  apply tr_loops.
Defined.

(* This is slightly different to 7.2.9 in that we ommit n = -1, which is
   inhabited hsets are contractible. *)
Theorem equiv_istrunc_contr_iterated_loops `{Univalence} (n : nat)
  : forall A, IsTrunc n A <~> forall a : A,
    Contr (iterated_loops n.+1 (A, a)).
Proof.
  induction n.
  { intro A.
    refine (equiv_composeR' equiv_hset_axiomK _).
    refine (equiv_iff_hprop (fun K a => Build_Contr _ 1 (fun x => (K a x)^)) _).
    intros ? ? ?; apply path_contr. }
  intro A.
  transitivity (forall x, IsTrunc n (loops (A, x))).
  1: destruct n; apply equiv_istrunc_istrunc_loops.
  srapply equiv_functor_forall_id.
  intro a.
  apply (equiv_composeR' (IHn (loops (A, a)))).
  cbn; refine (equiv_iff_hprop _ _).
  1: change ((forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))
      -> Contr (iterated_loops n.+2 (A, a))).
  1: refine (fun X => (ap _ (unfold_iterated_loops n.+1 _))^ # X 1).
  change (Contr (iterated_loops n.+2 (A, a))
    -> (forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))).
  intros X p.
  refine (@contr_equiv' _ _ _ X).
  rewrite !unfold_iterated_loops.
  apply pointed_equiv_equiv.
  rapply (emap (iterated_loops _)).
  symmetry.
  transitivity (p @ p^ = p @ p^, 1).
  { srefine (Build_pEquiv' _ _).
    1: exact (equiv_ap (equiv_concat_r _ _) _ _).
    reflexivity. }
  srapply Build_pEquiv'.
  { apply equiv_concat_lr.
    1: symmetry; apply concat_pV.
    apply concat_pV. }
  cbn; by rewrite concat_p1, concat_Vp.
Qed.

(** [loops_inv] is a natural transformation. *)
Global Instance is1natural_loops_inv : Is1Natural loops loops loops_inv.
Proof.
  intros A B f.
  srapply Build_pHomotopy.
  + intros p. refine (inv_Vp _ _ @ whiskerR _ (point_eq f) @ concat_pp_p _ _ _).
    refine (inv_pp _ _ @ whiskerL (point_eq f)^ (ap_V f p)^).
  + pointed_reduce. reflexivity.
Defined.

(** Loops on the pointed type of dependent pointed maps correspond to
  pointed dependent maps into a family of loops. *)
(* We define this in this direction, because the forward map is pointed by
  reflexivity. *)
Definition equiv_loops_ppforall `{Funext} {A : pType} (B : A -> pType)
  : loops (ppforall x : A, B x) <~>* (ppforall x : A, loops (B x)).
Proof.
  srapply Build_pEquiv'.
  1: symmetry; exact (equiv_path_pforall (point_pforall B) (point_pforall B)).
  reflexivity.
Defined.
