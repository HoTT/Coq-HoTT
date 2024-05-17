(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.
Require Import HSet.
Require Import Spaces.Pos Spaces.BinInt.
Require Import Colimits.Coeq.
Require Import Truncations.Core Truncations.Connectedness.

(** * Theorems about the [Circle]. *)

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(* ** Definition of the [Circle]. *)

(** We define the circle as the coequalizer of two copies of the identity map of [Unit].  This is easily equivalent to the naive definition

<<
Private Inductive Circle : Type0 :=
| base : Circle
| loop : base = base.
>>

but it allows us to apply the flattening lemma directly rather than having to pass across that equivalence.  *)

(** The circle is defined to be the coequalizer of two copies of the identity map on [Unit]. *)
Definition Circle := @Coeq Unit Unit idmap idmap.

(** It has a basepoint. *)
Definition base : Circle := coeq tt.

(** And a non-trivial path. *)
Definition loop : base = base := cglue tt.

(** Here is a notation for the circle that can be imported. *)
Module CircleNotation.
  Notation S1 := Circle (only parsing).
End CircleNotation.

(** Circle induction *)
Definition Circle_ind (P : Circle -> Type)
  (b : P base) (l : loop # b = b)
  : forall (x : Circle), P x.
Proof.
  refine (Coeq_ind P (fun u => transport P (ap coeq (path_unit tt u)) b) _).
  intros []; exact l.
Defined.

(** Computation rule for circle induction. *)
Definition Circle_ind_beta_loop (P : Circle -> Type)
  (b : P base) (l : loop # b = b)
  : apD (Circle_ind P b l) loop = l
  := Coeq_ind_beta_cglue P _ _ tt.

(** We mark [Circle], [base] and [loop] to never be simplified by [simpl] or [cbn] in order to hide how we defined it from the user. *) 
Arguments Circle : simpl never.
Arguments base : simpl never.
Arguments loop : simpl never.
Arguments Circle_ind_beta_loop : simpl never.

(** The recursion princple or non-dependent eliminator. *)
Definition Circle_rec (P : Type) (b : P) (l : b = b)
  : Circle -> P
  := Circle_ind (fun _ => P) b (transport_const _ _ @ l).

(** Computation rule for non-dependent eliminator. *)
Definition Circle_rec_beta_loop (P : Type) (b : P) (l : b = b)
  : ap (Circle_rec P b l) loop = l.
Proof.
  unfold Circle_rec.
  refine (cancelL (transport_const loop b) _ _ _).
  refine ((apD_const (Circle_ind (fun _ => P) b _) loop)^ @ _).
  refine (Circle_ind_beta_loop (fun _ => P) _ _).
Defined.

(** The [Circle] is pointed by [base]. *)
Global Instance ispointed_Circle : IsPointed Circle := base.

Definition pCircle : pType := [Circle, base].

(** ** The loop space of the [Circle] is the Integers [Int]

  This is the encode-decode style proof a la Licata-Shulman. *)

Section EncodeDecode.
  (** We assume univalence throughout this section. *)
  Context `{Univalence}.

  (** First we define the type of codes, this is a type family over the circle. This can be thought of as the covering space by the homotopical real numbers. It is defined by mapping loop to the path given by univalence applied to the automorphism of the integers. We will show that the section of this family at [base] is equivalent to the loop space of the circle. Giving us an equivalence [base = base <~> Int]. *)
  Definition Circle_code : Circle -> Type
    := Circle_rec Type BinInt (path_universe binint_succ).

  (** Transporting along [loop] gives us the successor automorphism on [Int]. *)
  Definition transport_Circle_code_loop (z : BinInt)
    : transport Circle_code loop z = binint_succ z.
  Proof.
    refine (transport_compose idmap Circle_code loop z @ _).
    unfold Circle_code; rewrite Circle_rec_beta_loop.
    apply transport_path_universe.
  Defined.

  (** Transporting along [loop^] gives us the predecessor on [Int]. *)
  Definition transport_Circle_code_loopV (z : BinInt)
    : transport Circle_code loop^ z = binint_pred z.
  Proof.
    refine (transport_compose idmap Circle_code loop^ z @ _).
    rewrite ap_V.
    unfold Circle_code; rewrite Circle_rec_beta_loop.
    rewrite <- (path_universe_V binint_succ).
    apply transport_path_universe.
  Defined.

  (** To turn a path in [Circle] based at [base] into a code we transport along it. We call this encoding. *)
  Definition Circle_encode (x:Circle) : (base = x) -> Circle_code x
    := fun p => p # zero.

  (** TODO: explain this proof in more detail. *)
  (** Turning a code into a path based at [base]. We call this decoding. *)
  Definition Circle_decode (x : Circle) : Circle_code x -> (base = x).
  Proof.
    revert x; refine (Circle_ind (fun x => Circle_code x -> base = x) (loopexp loop) _).
    apply path_forall; intros z; simpl in z.
    refine (transport_arrow _ _ _ @ _).
    refine (transport_paths_r loop _ @ _).
    rewrite transport_Circle_code_loopV.
    destruct z as [n| |n].
    2: apply concat_Vp.
    { rewrite <- binint_neg_pos_succ.
      unfold loopexp, loopexp_pos.
      rewrite pos_peano_ind_beta_pos_succ.
      apply concat_pV_p. }
    induction n as [|n nH] using pos_peano_ind.
    1: apply concat_1p.
    rewrite <- pos_add_1_r.
    change (pos (n + 1)%pos)
      with (binint_succ (pos n)).
    rewrite binint_pred_succ.
    cbn; rewrite pos_add_1_r.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    reflexivity.
  Defined.

  (** The non-trivial part of the proof that decode and encode are equivalences is showing that decoding followed by encoding is the identity on the fibers over [base]. *)
  Definition Circle_encode_loopexp (z:BinInt)
    : Circle_encode base (loopexp loop z) = z.
  Proof.
    destruct z as [n | | n]; unfold Circle_encode.
    - induction n using pos_peano_ind; simpl in *.
      + refine (moveR_transport_V _ loop _ _ _).
        by symmetry; apply transport_Circle_code_loop.
      + unfold loopexp_pos.
        rewrite pos_peano_ind_beta_pos_succ.
        rewrite transport_pp.
        refine (moveR_transport_V _ loop _ _ _).
        refine (_ @ (transport_Circle_code_loop _)^).
        refine (IHn @ _^).
        rewrite binint_neg_pos_succ.
        by rewrite binint_succ_pred.
    - reflexivity.
    - induction n using pos_peano_ind; simpl in *.
      + by apply transport_Circle_code_loop.
      + unfold loopexp_pos.
        rewrite pos_peano_ind_beta_pos_succ.
        rewrite transport_pp.
        refine (moveR_transport_p _ loop _ _ _).
        refine (_ @ (transport_Circle_code_loopV _)^).
        refine (IHn @ _^).
        rewrite <- pos_add_1_r.
        change (binint_pred (binint_succ (pos n)) = pos n).
        apply binint_pred_succ.
  Defined.

  (** Now we put it together. *)
  Definition Circle_encode_isequiv (x:Circle) : IsEquiv (Circle_encode x).
  Proof.
   refine (isequiv_adjointify (Circle_encode x) (Circle_decode x) _ _).
    (* Here we induct on [x:Circle].  We just did the case when [x] is [base]. *)
    - refine (Circle_ind (fun x => (Circle_encode x) o (Circle_decode x) == idmap)
        Circle_encode_loopexp _ _).
      (* What remains is easy since [Int] is known to be a set. *)
      by apply path_forall; intros z; apply hset_path2.
    (* The other side is trivial by path induction. *)
    - intros []; reflexivity.
  Defined.

  (** Finally giving us an equivalence between the loop space of the [Circle] and [Int]. *)
  Definition equiv_loopCircle_int : (base = base) <~> BinInt
    := Build_Equiv _ _ (Circle_encode base) (Circle_encode_isequiv base).

End EncodeDecode.

(** ** Connectedness and truncatedness of the [Circle] *)

(** The circle is 0-connected. *)
Global Instance isconnected_Circle `{Univalence} : IsConnected 0 Circle.
Proof.
  apply is0connected_merely_allpath.
  1: exact (tr base).
  srefine (Circle_ind _ _ _).
  - simple refine (Circle_ind _ _ _).
    + exact (tr 1).
    + apply path_ishprop.
  - apply path_ishprop.
Defined.

(** It follows that the circle is a 1-type. *)
Global Instance istrunc_Circle `{Univalence} : IsTrunc 1 Circle.
Proof.
  apply istrunc_S.
  intros x y.
  assert (p := merely_path_is0connected Circle base x).
  assert (q := merely_path_is0connected Circle base y).
  strip_truncations.
  destruct p, q.
  refine (istrunc_equiv_istrunc (n := 0) BinInt equiv_loopCircle_int^-1).
Defined.

(** ** Iteration of equivalences *)

(** If [P : Circle -> Type] is defined by a type [X] and an autoequivalence [f], then the image of [n : Int] regarded as in [base = base] is [iter_int f n]. *)
Definition Circle_action_is_iter `{Univalence} X (f : X <~> X) (n : BinInt) (x : X)
: transport (Circle_rec Type X (path_universe f)) (equiv_loopCircle_int^-1 n) x
  = binint_iter f n x.
Proof.
  refine (_ @ loopexp_path_universe _ _ _).
  refine (transport_compose idmap _ _ _ @ _).
  refine (ap (fun p => transport idmap p x) _).
  unfold equiv_loopCircle_int; cbn.
  unfold Circle_decode; simpl.
  rewrite ap_loopexp.
  refine (ap (fun p => loopexp p n) _).
  apply Circle_rec_beta_loop.
Defined.

(** The universal property of the circle (Lemma 6.2.9 in the Book).  We could deduce this from [isequiv_Coeq_rec], but it's nice to see a direct proof too. *)
Definition Circle_rec_uncurried (P : Type)
  : {b : P & b = b} -> (Circle -> P)
  := fun x => Circle_rec P (pr1 x) (pr2 x).

Global Instance isequiv_Circle_rec_uncurried `{Funext} (P : Type) : IsEquiv (Circle_rec_uncurried P).
Proof.
  srapply isequiv_adjointify.
  - exact (fun g => (g base ; ap g loop)).
  - intros g.
    apply path_arrow.
    srapply Circle_ind.
    + reflexivity.
    + unfold Circle_rec_uncurried; cbn.
      apply transport_paths_FlFr'.
      apply equiv_p1_1q.
      apply Circle_rec_beta_loop.
  - intros [b p]; apply ap.
    apply Circle_rec_beta_loop.
Defined.

Definition equiv_Circle_rec `{Funext} (P : Type)
  : {b : P & b = b} <~> (Circle -> P)
  := Build_Equiv _ _ _ (isequiv_Circle_rec_uncurried P).

(** A pointed version of the universal property of the circle. *)
Definition pmap_from_circle_loops `{Funext} (X : pType)
  : (pCircle ->** X) <~>* loops X.
Proof.
  snrapply Build_pEquiv'.
  - refine (_ oE (issig_pmap _ _)^-1%equiv).
    equiv_via { xp : { x : X & x = x } & xp.1 = pt }.
    2: make_equiv_contr_basedpaths.
    exact ((equiv_functor_sigma_pb (equiv_Circle_rec X)^-1%equiv)).
  - simpl.  apply ap_const.
Defined.
