(* -*- mode: coq; mode: visual-line -*- *)

(** * The Integers. *)

Require Import HoTT.Basics HoTT.Types.Universe.
Require Import HSet.

Local Open Scope path_scope.

(* ** Positive Numbers *)

Inductive Pos : Type0 :=
| one : Pos
| succ_pos : Pos -> Pos.

Definition one_neq_succ_pos (z : Pos) : ~ (one = succ_pos z)
  := fun p => transport (fun s => match s with one => Unit | succ_pos t => Empty end) p tt.

Definition succ_pos_injective {z w : Pos} (p : succ_pos z = succ_pos w) : z = w
  := transport (fun s => z = (match s with one => w | succ_pos a => a end)) p (idpath z).

(** ** Definition of the Integers *)

Inductive Int : Type0 :=
| neg : Pos -> Int
| zero : Int
| pos : Pos -> Int.

Global Instance ispointed_Int : IsPointed Int := zero.

Definition neg_injective {z w : Pos} (p : neg z = neg w) : z = w
  := transport (fun s => z = (match s with neg a => a | zero => w | pos a => w end)) p (idpath z).

Definition pos_injective {z w : Pos} (p : pos z = pos w) : z = w
  := transport (fun s => z = (match s with neg a => w | zero => w | pos a => a end)) p (idpath z).

Definition neg_neq_zero {z : Pos} : ~ (neg z = zero)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (idpath z).

Definition pos_neq_zero {z : Pos} : ~ (pos z = zero)
  := fun p => transport (fun s => match s with pos a => z = a | zero => Empty | neg _ => Empty end) p (idpath z).

Definition neg_neq_pos {z w : Pos} : ~ (neg z = pos w)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (idpath z).

(* ** Decidable paths and truncation. *)

Global Instance decpaths_int : DecidablePaths Int.
Proof.
  intros [n | | n] [m | | m].
  - revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
    + exact (inl 1).
    + exact (inr (fun p => one_neq_succ_pos _ (neg_injective p))).
    + exact (inr (fun p => one_neq_succ_pos _ (symmetry _ _ (neg_injective p)))).
    + destruct (IHn m) as [p | np].
      * exact (inl (ap neg (ap succ_pos (neg_injective p)))).
      * exact (inr (fun p => np (ap neg (succ_pos_injective (neg_injective p))))).
  - exact (inr neg_neq_zero).
  - exact (inr neg_neq_pos).
  - exact (inr (neg_neq_zero o symmetry _ _)).
  - exact (inl 1).
  - exact (inr (pos_neq_zero o symmetry _ _)).
  - exact (inr (neg_neq_pos o symmetry _ _)).
  - exact (inr pos_neq_zero).
  - revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
    + exact (inl 1).
    + exact (inr (fun p => one_neq_succ_pos _ (pos_injective p))).
    + exact (inr (fun p => one_neq_succ_pos _ (symmetry _ _ (pos_injective p)))).
    + destruct (IHn m) as [p | np].
      * exact (inl (ap pos (ap succ_pos (pos_injective p)))).
      * exact (inr (fun p => np (ap pos (succ_pos_injective (pos_injective p))))).
Defined.

Global Instance hset_int : IsHSet Int | 0.
Proof.
  exact _.
Defined.

(* ** The successor autoequivalence. *)

Definition succ_int (z : Int) : Int
  := match z with
       | neg (succ_pos n) => neg n
       | neg one => zero
       | zero => pos one
       | pos n => pos (succ_pos n)
     end.

Definition pred_int (z : Int) : Int
  := match z with
       | neg n => neg (succ_pos n)
       | zero => neg one
       | pos one => zero
       | pos (succ_pos n) => pos n
     end.

Global Instance isequiv_succ_int : IsEquiv succ_int | 0.
Proof.
  refine (isequiv_adjointify succ_int pred_int _ _).
  - intros [[|n] | | [|n]]; reflexivity.
  - intros [[|n] | | [|n]]; reflexivity.
Defined.

(** ** Iteration of equivalences *)

(** *** Iteration by positive numbers *)

Section IterPos.
  Context {A} (f : A -> A).

  Fixpoint iter_pos (n : Pos) : A -> A
    := match n with
         | one => f
         (** Should this be (iter_pos f n (f a))? *)
         | succ_pos n => f o iter_pos n
       end.

  Definition iter_pos_succ_l (n : Pos) (a : A)
  : iter_pos (succ_pos n) a = f (iter_pos n a)
    := 1.

  Fixpoint iter_pos_succ_r (n : Pos) (a : A)
  : iter_pos (succ_pos n) a = iter_pos n (f a)
    := match n with
         | one => 1
         | succ_pos n => ap f (iter_pos_succ_r n a)
       end.

End IterPos.

(** *** Iteration by arbitrary integers *)

Section Iteration.

  (** Iteration by arbitrary integers requires the endofunction to be an equivalence, so that we can define a negative iteration by using its inverse. *)
  Context {A} (f : A -> A) `{IsEquiv _ _ f}.

  Definition iter_int (n : Int) : A -> A
  := match n with
       | neg n => iter_pos (f^-1) n
       | zero => idmap
       | pos n => iter_pos f n
     end.

  Definition iter_int_succ_l (n : Int) (a : A)
  : iter_int (succ_int n) a = f (iter_int n a).
  Proof.
    destruct n as [[|n]| |n]; cbn.
    - symmetry; apply eisretr.  (** -1 *)
    - symmetry; apply eisretr.  (** -n *)
    - reflexivity.              (** 0 *)
    - reflexivity.              (** n *)
  Defined.

  Definition iter_int_succ_r (n : Int) (a : A)
  : iter_int (succ_int n) a = iter_int n (f a).
  Proof.
    destruct n as [[|n]| |n]; cbn.
    - symmetry; apply eissect.  (** -1 *)
    - refine (_ @ iter_pos_succ_l f^-1 n (f a)).
      refine (_ @ (iter_pos_succ_r f^-1 n (f a))^).
      apply ap.
      symmetry; apply eissect.  (** -n *)
    - reflexivity.              (** 0 *)
    - etransitivity.  (** n *)
      + symmetry; apply iter_pos_succ_l.
      + apply iter_pos_succ_r.
  Defined.

  Definition iter_int_pred_l (n : Int) (a : A)
  : iter_int (pred_int n) a = f^-1 (iter_int n a).
  Proof.
    destruct n as [n| |[|n]]; cbn.
    - reflexivity.              (** -n *)
    - reflexivity.              (** 0 *)
    - symmetry; apply eissect.  (** 1 *)
    - symmetry; apply eissect.  (** n *)
  Defined.

  Definition iter_int_pred_r (n : Int) (a : A)
  : iter_int (pred_int n) a = iter_int n (f^-1 a).
  Proof.
    destruct n as [n| |[|n]]; cbn.
    - etransitivity.  (** -n *)
      + symmetry; apply iter_pos_succ_l.
      + apply iter_pos_succ_r.
    - reflexivity.              (** 0 *)
    - symmetry; apply eisretr.  (** 1 *)
    - refine (_ @ iter_pos_succ_l f n (f^-1 a)).
      refine (_ @ (iter_pos_succ_r f n (f^-1 a))^).
      apply ap.
      symmetry; apply eisretr.  (** n *)
  Defined.

End Iteration.

(** ** Exponentiation of loops *)

Fixpoint loopexp_pos {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x)
  := match n with
       | one => p
       | succ_pos n => loopexp_pos p n @ p
     end.

Definition loopexp {A : Type} {x : A} (p : x = x) (z : Int) : (x = x)
  := match z with
       | neg n => loopexp_pos p^ n
       | zero => 1
       | pos n => loopexp_pos p n
     end.

Definition ap_loopexp {A B} (f : A -> B) {x : A} (p : x = x) (z : Int)
: ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  destruct z as [n| |n]; try reflexivity.
  - induction n as [|n IH]; simpl.
    * apply ap_V.
    * rewrite ap_pp, IH.
      apply whiskerL, ap_V.
  - induction n as [|n IH]; try reflexivity; simpl.
    rewrite ap_pp, IH; reflexivity.
Qed.

(** Under univalence, exponentiation of loops corresponds to iteration of autoequivalences. *)

Definition equiv_path_loopexp `{Univalence}
           {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = iter_int (equiv_path A A p) z a.
Proof.
  destruct z as [n| |n]; try reflexivity.
  all:induction n as [|n IH]; try reflexivity; cbn in *.
  all:refine (transport_pp _ _ _ _ @ _); apply ap, IH.
Defined.

Definition loopexp_path_universe `{Univalence}
           {A : Type} (f : A <~> A) (z : Int) (a : A)
: transport idmap (loopexp (path_universe f) z) a
  = iter_int f z a.
Proof.
  revert f. equiv_intro (equiv_path A A) p.
  refine (_ @ equiv_path_loopexp p z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.
