(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the circle [S1]. *)

Require Import HoTT.Basics.
Require Import Types.Paths Types.Forall Types.Arrow Types.Universe Types.Empty Types.Unit.
Require Import HSet UnivalenceImpliesFunext.
Require Import Spaces.Int.
Require Import hit.Coeq.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(* ** Definition of the circle. *)

(** We define the circle as the coequalizer of two copies of the identity map of [Unit].  This is easily equivalent to the naive definition

<<<
Private Inductive S1 : Type1 :=
| base : S1
| loop : base = base.
>>>

but it allows us to apply the flattening lemma directly rather than having to pass across that equivalence.  *)

Definition S1 := @Coeq Unit Unit idmap idmap.
Definition base : S1 := coeq tt.
Definition loop : base = base := cp tt.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : loop # b = b)
  : forall (x:S1), P x.
Proof.
  refine (Coeq_ind P (fun u => transport P (ap coeq (path_unit tt u)) b) _).
  intros []; exact l.
Defined.

Definition S1_ind_beta_loop
           (P : S1 -> Type) (b : P base) (l : loop # b = b)
: apD (S1_ind P b l) loop = l
  := Coeq_ind_beta_cp P _ _ tt.

(** But we want to allow the user to forget that we've defined the circle in that way. *)
Arguments S1 : simpl never.
Arguments base : simpl never.
Arguments loop : simpl never.
Arguments S1_ind : simpl never.
Arguments S1_ind_beta_loop : simpl never.

(* ** The non-dependent eliminator *)

Definition S1_rec (P : Type) (b : P) (l : b = b)
  : S1 -> P
  := S1_ind (fun _ => P) b (transport_const _ _ @ l).

Definition S1_rec_beta_loop (P : Type) (b : P) (l : b = b)
  : ap (S1_rec P b l) loop = l.
Proof.
  unfold S1_rec.
  refine (cancelL (transport_const loop b) _ _ _).
  refine ((apD_const (S1_ind (fun _ => P) b _) loop)^ @ _).
  refine (S1_ind_beta_loop (fun _ => P) _ _).
Defined.

(* ** The loop space of the circle is the Integers. *)

(** We use encode-decode. *)

Section AssumeUnivalence.
Context `{Univalence}.

Definition S1_code : S1 -> Type
  := S1_rec Type Int (path_universe succ_int).

(* Transporting in the codes fibration is the successor autoequivalence. *)

Definition transport_S1_code_loop (z : Int)
  : transport S1_code loop z = succ_int z.
Proof.
  refine (transport_compose idmap S1_code loop z @ _).
  unfold S1_code; rewrite S1_rec_beta_loop.
  apply transport_path_universe.
Defined.

Definition transport_S1_code_loopV (z : Int)
  : transport S1_code loop^ z = pred_int z.
Proof.
  refine (transport_compose idmap S1_code loop^ z @ _).
  rewrite ap_V.
  unfold S1_code; rewrite S1_rec_beta_loop.
  rewrite <- (path_universe_V succ_int).
  apply transport_path_universe.
Defined.

(* Encode by transporting *)

Definition S1_encode (x:S1) : (base = x) -> S1_code x
  := fun p => p # zero.

(* Decode by iterating loop. *)

Definition S1_decode (x:S1) : S1_code x -> (base = x).
Proof.
  revert x; refine (S1_ind (fun x => S1_code x -> base = x) (loopexp loop) _).
  apply path_forall; intros z; simpl in z.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_r loop _ @ _).
  rewrite transport_S1_code_loopV.
  destruct z as [[|n] | | [|n]]; simpl.
  by apply concat_pV_p.
  by apply concat_pV_p.
  by apply concat_Vp.
  by apply concat_1p.
  reflexivity.
Defined.

(* The nontrivial part of the proof that decode and encode are equivalences is showing that decoding followed by encoding is the identity on the fibers over [base]. *)

Definition S1_encode_loopexp (z:Int)
  : S1_encode base (loopexp loop z) = z.
Proof.
  destruct z as [n | | n]; unfold S1_encode.
  induction n; simpl in *.
  refine (moveR_transport_V _ loop _ _ _).
  by symmetry; apply transport_S1_code_loop.
  rewrite transport_pp.
  refine (moveR_transport_V _ loop _ _ _).
  refine (_ @ (transport_S1_code_loop _)^).
  assumption.
  reflexivity.
  induction n; simpl in *.
  by apply transport_S1_code_loop.
  rewrite transport_pp.
  refine (moveR_transport_p _ loop _ _ _).
  refine (_ @ (transport_S1_code_loopV _)^).
  assumption.
Defined.

(* Now we put it together. *)

Definition S1_encode_isequiv (x:S1) : IsEquiv (S1_encode x).
Proof.
  refine (isequiv_adjointify (S1_encode x) (S1_decode x) _ _).
  (* Here we induct on [x:S1].  We just did the case when [x] is [base]. *)
  refine (S1_ind (fun x => Sect (S1_decode x) (S1_encode x))
    S1_encode_loopexp _ _).
  (* What remains is easy since [Int] is known to be a set. *)
  by apply path_forall; intros z; apply set_path2.
  (* The other side is trivial by path induction. *)
  intros []; reflexivity.
Defined.

Definition equiv_loopS1_int : (base = base) <~> Int
  := BuildEquiv _ _ (S1_encode base) (S1_encode_isequiv base).

End AssumeUnivalence.
