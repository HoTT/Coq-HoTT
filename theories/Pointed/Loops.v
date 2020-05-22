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

(** ** Functoriality of loop spaces *)

Definition loops_functor {A B : pType} (f : A ->* B)
  : (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  refine (_ @ concat_Vp (point_eq f)).
  apply whiskerL. apply concat_1p.
Defined.

Definition iterated_loops_functor {A B : pType} (n : nat)
  : (A ->* B) -> (iterated_loops n A) ->* (iterated_loops n B).
Proof.
  induction n as [|n IHn].
  1: exact idmap.
  refine (loops_functor o _).
  apply IHn.
Defined.

(* Loops functor respects composition *)
Definition loops_functor_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : (loops_functor (pmap_compose g f))
  ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
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

(* Loops functor respects identity *)
Definition loops_functor_idmap (A : pType)
  : loops_functor (@pmap_idmap A) ==* pmap_idmap.
Proof.
  srapply Build_pHomotopy.
  { intro p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _). }
  reflexivity.
Defined.

(* Loops functor distributes over concatenation *)
Lemma loops_functor_pp {X Y : pType} (f : X ->* Y) (x y : loops X)
  : loops_functor f (x @ y) = loops_functor f x @ loops_functor f y.
Proof.
  pointed_reduce_rewrite.
  apply ap_pp.
Defined.

Lemma loops_functor_pconst {A B : pType} : loops_functor (@pconst A B) ==* pconst.
Proof.
  srapply Build_pHomotopy.
  + intro p. refine (concat_1p _ @ concat_p1 _ @ ap_const _ _).
  + reflexivity.
Defined.

(* Loops functor preserves pointed homotopies *)
Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
  : (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  srapply Build_pHomotopy; cbn.
  { intro q.
    refine (_ @ (concat_p1 _)^ @ (concat_1p _)^).
    apply moveR_Vp.
    apply (concat_Ap (fun x => p x @ 1)). }
  simpl. generalize (p point0). generalize (g point0).
  intros _ []. reflexivity.
Defined.

(* Iterated loops functor respects composition *)
Lemma iterated_loops_functor_compose n A B C (f : B ->* C)
  (g : A ->* B) : iterated_loops_functor n (f o* g)
  ==* (iterated_loops_functor n f) o* (iterated_loops_functor n g).
Proof.
  induction n as [|n IHn]; cbn.
  1: reflexivity.
  refine (_ @* (loops_functor_compose _ _)).
  apply loops_2functor, IHn.
Defined.

Lemma iterated_loops_functor_idmap (A : pType) n
  : iterated_loops_functor n (@pmap_idmap A) ==* pmap_idmap.
Proof.
  induction n; cbn.
  1: reflexivity.
  etransitivity.
  2: apply loops_functor_idmap.
  apply loops_2functor, IHn.
Defined.

Lemma iterated_loops_functor_pp {X Y : pType} (f : X ->* Y) n
  (x y : iterated_loops n.+1 X) : iterated_loops_functor n.+1 f (x @ y)
    = iterated_loops_functor n.+1 f x @ iterated_loops_functor n.+1 f y.
Proof.
  induction n.
  1: apply loops_functor_pp.
  change (iterated_loops_functor n.+2 f)
    with (loops_functor (iterated_loops_functor n.+1 f)).
  apply loops_functor_pp.
Defined.

(* Iterated loops functor respects homotopies *)
Definition iterated_loops_2functor n {A B : pType}
           {f g : A ->* B} (p : f ==* g)
  : (iterated_loops_functor n f) ==* (iterated_loops_functor n g).
Proof.
  induction n as [|n IHn]; [ assumption | apply loops_2functor, IHn ].
Defined.

(** The fiber of [loops_functor f] is equivalent to a fiber of [ap f]. *)
Definition hfiber_loops_functor {A B : pType} (f : A ->* B) (p : loops B)
  : {q : loops A & ap f q = (point_eq f @ p) @ (point_eq f)^}
    <~> hfiber (loops_functor f) p.
Proof.
  apply equiv_functor_sigma_id; intros q.
  refine (equiv_moveR_Vp _ _ _ oE _).
  apply equiv_moveR_pM.
Defined.

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_loops_functor {n} (A B : pType) (f : A ->* B)
  `{IsTruncMap n.+1 _ _ f} : IsTruncMap n (loops_functor f).
Proof.
  intro p. apply (trunc_equiv' _ (hfiber_loops_functor f p)).
Defined.

(** And likewise the connectedness.  *)
Global Instance isconnected_loops_functor `{Univalence} {n : trunc_index}
  (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
  : IsConnMap n (loops_functor f).
Proof.
  intros p; eapply isconnected_equiv'.
  - refine (hfiber_loops_functor f p oE _).
    symmetry; apply hfiber_ap.
  - exact _.
Defined.

Definition isconnected_iterated_loops_functor `{Univalence}
  (k : nat) (A B : pType) (f : A ->* B)
  : forall n : trunc_index, IsConnMap (trunc_index_inc' n k) f
                       -> IsConnMap n (iterated_loops_functor k f).
Proof.
  induction k; intros n C.
  - exact C.
  - apply isconnected_loops_functor.
    apply IHk.
    exact C.
Defined.

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} n {A B : pType} (f : A ->* B)
  : loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
  <~> image n (loops_functor f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization
    (@IsConnMap n) (@MapIn n) (loops_functor f))).
  { refine (@Build_Factorization (@IsConnMap n) (@MapIn n)
      (loops A) (loops B) (loops_functor f) (loops C)
      (loops_functor g) (loops_functor h) _ _ _).
    intros x; symmetry.
    refine (_ @ loops_functor_compose h g x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate (path_factor (O_factsys n) (loops_functor f) I
    (image n (loops_functor f)))).
Defined.

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  srapply Build_pEquiv.
  1: exact (Build_pMap (loops A) (loops A) inverse 1).
  apply isequiv_path_inverse.
Defined.

(** Loops functor preserves equivalences *)
Definition pequiv_loops_functor {A B : pType}
  : A <~>* B -> loops A <~>* loops B.
Proof.
  intro f.
  srapply pequiv_adjointify.
  1: apply loops_functor, f.
  1: apply loops_functor, (pequiv_inverse f).
  1,2: refine ((loops_functor_compose _ _)^* @* _ @* loops_functor_idmap _).
  1,2: apply loops_2functor.
  1: apply peisretr.
  apply peissect.
Defined.

(** A version of [unfold_iterated_loops] that's an equivalence rather than an equality.  We could get this from the equality, but it's more useful to construct it explicitly since then we can reason about it.  *)
Definition unfold_iterated_loops' (n : nat) (X : pType)
  : iterated_loops n.+1 X <~>* iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  apply pequiv_loops_functor, IHn.
Defined.

(** For instance, we can prove that it's natural. *)
Definition unfold_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : (unfold_iterated_loops' n B) o* (iterated_loops_functor n.+1 f)
    ==* (iterated_loops_functor n (loops_functor f)) o* (unfold_iterated_loops' n A).
Proof.
  induction n.
  - srefine (Build_pHomotopy _ _).
    + reflexivity.
    + cbn. apply moveL_pV.
      refine (concat_1p _ @ _).
      refine (concat_1p _ @ _).
      refine (_ @ (concat_p1 _)^).
      exact ((ap_idmap _)^).
  - refine ((loops_functor_compose _ _)^* @* _).
    refine (_ @* (loops_functor_compose _ _)).
    apply loops_2functor.
    apply IHn.
Defined.

(** Iterated loops preserves equivalences *)
Lemma pequiv_iterated_loops_functor {A B} n : A <~>* B
  -> iterated_loops n A <~>* iterated_loops n B.
Proof.
  intros f.
  induction n.
  1: apply f.
  by apply pequiv_loops_functor.
Defined.

(** Since that was a separate induction, its underlying function is only homotopic to [iterated_loops_functor n], not definitionally equal. *)

Definition pequiv_iterated_loops_functor_is_iterated_loops_functor {A B} n (f : A <~>* B)
  : pequiv_iterated_loops_functor n f ==* iterated_loops_functor n f.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - apply loops_2functor, IHn.
Defined.

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
  by apply pequiv_loops_functor.
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
  apply pequiv_loops_functor, IHn.
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
  apply pequiv_iterated_loops_functor.
  apply loops_psigma_commute.
Defined.

(* We declare this local notation to make it easier to write pointed types *)
Local Notation "( X , x )" := (Build_pType X x).

(** In the following lemmas we have used universe annotations explicitly as without them, coq cannot guess the universe levels correctly. Defining pointed maps as a special case of pForall has the side effect of raising the universe level since pForall requires a bigger universe for the type family. Hopefully in the future, coq's "universe guessing" will be smarter and we can drop the annotations here. *)

(* We can convert between families of loops in a type and loops in Type at that type. *)
Definition loops_type@{i j k} `{Univalence} (A : Type@{i})
  : pEquiv@{j j k} (loops@{j} (Type@{i}, A)) (A <~> A, equiv_idmap).
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
  { refine (_ o*E pequiv_loops_functor (loops_type A)).
    apply issig_pequiv'.
    exists (equiv_inverse (equiv_path_arrow 1%equiv 1%equiv)
            oE equiv_inverse (equiv_path_equiv 1%equiv 1%equiv)).
    reflexivity. }
  exact (loops_pproduct_commute _ _ o*E pequiv_loops_functor IHn).
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
  apply pequiv_iterated_loops_functor.
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

(** [loops] and [iterated_loops] are 1-functors *)
Global Instance is0functor_loops
  : Is0Functor loops.
Proof.
  apply Build_Is0Functor. intros. exact (loops_functor f).
Defined.

Global Instance is1functor_loops : Is1Functor loops.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (loops_2functor h).
  + intros. apply loops_functor_idmap.
  + intros. apply loops_functor_compose.
Defined.

Global Instance is0functor_iterated_loops (n : nat)
  : Is0Functor (iterated_loops n).
Proof.
  apply Build_Is0Functor. intros. exact (iterated_loops_functor n f).
Defined.

Global Instance is1functor_iterated_loops (n : nat)
  : Is1Functor (iterated_loops n).
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (iterated_loops_2functor n h).
  + intros. apply iterated_loops_functor_idmap.
  + intros. apply iterated_loops_functor_compose.
Defined.

(** [loops_inv] is a natural transformation. *)
Global Instance is1natural_loops_inv : Is1Natural loops loops loops_inv.
Proof.
  apply Build_Is1Natural. intros A B f.
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
