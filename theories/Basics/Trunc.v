(** * Truncatedness *)

Require Import
  Basics.Overture
  Basics.Contractible
  Basics.Equivalences
  Basics.Tactics
  Basics.Nat
  Basics.Iff.

Local Set Universe Minimization ToSet.

Local Open Scope trunc_scope.
Local Open Scope path_scope.
Generalizable Variables A B m n f.

(** ** Notation for truncation-levels *)
Open Scope trunc_scope.

(** Increase a truncation index by a natural number. *)
Fixpoint trunc_index_inc@{} (k : trunc_index) (n : nat)
  : trunc_index
  := match n with
      | O => k
      | S m => (trunc_index_inc k m).+1
    end.

(** This is a variation that inserts the successor operations in the other order.  This is sometimes convenient. *)
Fixpoint trunc_index_inc'@{} (k : trunc_index) (n : nat)
  : trunc_index
  := match n with
      | O => k
      | S m => (trunc_index_inc' k.+1 m)
    end.

Definition trunc_index_inc'_succ@{} (n : nat) (k : trunc_index)
  : trunc_index_inc' k.+1 n = (trunc_index_inc' k n).+1.
Proof.
  revert k; simple_induction n n IHn; intro k.
  - reflexivity.
  - exact (IHn k.+1).
Defined.

Definition trunc_index_inc_agree@{} (k : trunc_index) (n : nat)
  : trunc_index_inc k n = trunc_index_inc' k n.
Proof.
  simple_induction n n IHn.
  - reflexivity.
  - simpl.
    refine (ap _ IHn @ _).
    symmetry; apply trunc_index_inc'_succ.
Defined.

Definition nat_to_trunc_index@{} (n : nat) : trunc_index
  := (trunc_index_inc minus_two n).+2.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Definition trunc_index_inc'_0n@{} (n : nat)
  : trunc_index_inc' 0%nat n = n.
Proof.
  simple_induction n n IHn.
  1: reflexivity.
  refine (trunc_index_inc'_succ _ _ @ _).
  exact (ap _ IHn).
Defined.

Definition int_to_trunc_index@{} (v : Decimal.int) : option trunc_index
  := match v with
     | Decimal.Pos d => Some (nat_to_trunc_index (Nat.of_uint d))
     | Decimal.Neg d => match Nat.of_uint d with
                        | 2%nat => Some minus_two
                        | 1%nat => Some (minus_two.+1)
                        | 0%nat => Some (minus_two.+2)
                        | _ => None
                        end
     end.

Definition num_int_to_trunc_index@{} (v : Numeral.int) : option trunc_index :=
  match v with
  | Numeral.IntDec v => int_to_trunc_index v
  | Numeral.IntHex _ => None
  end.

Fixpoint trunc_index_to_little_uint@{} n acc :=
  match n with
  | minus_two => acc
  | minus_two.+1 => acc
  | minus_two.+2 => acc
  | trunc_S n => trunc_index_to_little_uint n (Decimal.Little.succ acc)
  end.

Definition trunc_index_to_int@{} n :=
  match n with
  | minus_two => Decimal.Neg (Nat.to_uint 2)
  | minus_two.+1 => Decimal.Neg (Nat.to_uint 1)
  | n => Decimal.Pos (Decimal.rev (trunc_index_to_little_uint n Decimal.zero))
  end.

Definition trunc_index_to_num_int@{} n :=
  Numeral.IntDec (trunc_index_to_int n).

(** This allows us to use notation like (-2) and 42 for a [trunc_index]. *)
Number Notation trunc_index num_int_to_trunc_index trunc_index_to_num_int
  : trunc_scope.

(** Sends a [trunc_index] [n] to the natural number [n+2]. *)
Fixpoint trunc_index_to_nat (n : trunc_index) : nat
  := match n with
    | minus_two => 0%nat
    | n'.+1 => (trunc_index_to_nat n').+1
    end.

(** ** Arithmetic on truncation-levels. *)
Fixpoint trunc_index_add@{} (m n : trunc_index) : trunc_index
  := match m with
       | -2 => n
       | m'.+1 => (trunc_index_add m' n).+1
     end.

Notation "m +2+ n" := (trunc_index_add m n) : trunc_scope.

Definition trunc_index_add_minus_two@{} m
  : m +2+ -2 = m.
Proof.
  simple_induction m m IHm.
  1: reflexivity.
  cbn; apply ap.
  assumption.
Defined.

Definition trunc_index_add_succ@{} m n
  : m +2+ n.+1 = (m +2+ n).+1.
Proof.
  simple_induction m m IHm.
  1: reflexivity.
  cbn; apply ap; assumption.
Defined.

Definition trunc_index_add_comm@{} m n
  : m +2+ n = n +2+ m.
Proof.
  simple_induction n n IHn.
  - apply trunc_index_add_minus_two.
  - exact (trunc_index_add_succ _ _ @ ap trunc_S IHn).
Defined.

Fixpoint trunc_index_leq@{} (m n : trunc_index) : Type0
  := match m, n with
       | -2, _ => Unit
       | m'.+1, -2 => Empty
       | m'.+1, n'.+1 => trunc_index_leq m' n'
     end.

Existing Class trunc_index_leq.

Notation "m <= n" := (trunc_index_leq m n) : trunc_scope.

Instance trunc_index_leq_minus_two_n@{} n : -2 <= n := tt.

Instance trunc_index_leq_succ@{} n : n <= n.+1.
Proof.
  by induction n as [|n IHn] using trunc_index_ind.
Defined.

Definition trunc_index_pred@{} : trunc_index -> trunc_index.
Proof.
  intros [|m].
  1: exact (-2).
  exact m.
Defined.

Notation "n '.-1'" := (trunc_index_pred n) : trunc_scope.
Notation "n '.-2'" := (n.-1.-1) : trunc_scope.

Definition trunc_index_succ_pred@{} (n : nat)
  : (n.-1).+1 = n
  := idpath.

Definition trunc_index_succ_pred'@{} (n : trunc_index)
  : -1 <= n -> (n.-1).+1 = n.
Proof.
  destruct n.
  1: contradiction.
  reflexivity.
Defined.

Definition trunc_index_add_pred@{} (m : trunc_index) (n : nat)
  : m +2+ n.-1 = (m +2+ n).-1.
Proof.
  destruct m.
  1: reflexivity.
  (* The RHS is definitionally [m +2+ n], which is definitionally [m +2+ n.-1.+1], so this finishes it off: *)
  symmetry; napply trunc_index_add_succ.
Defined.

Definition trunc_index_add_pred'@{} (m n : trunc_index)
  : -1 <= n -> m +2+ n.-1 = (m +2+ n).-1.
Proof.
  destruct m.
  1: reflexivity.
  destruct n.
  1: contradiction.
  intros _.
  (* The RHS is definitionally [m +2+ n], which is definitionally [m +2+ n.-1.+1], so this finishes it off: *)
  symmetry; napply trunc_index_add_succ.
Defined.

Definition trunc_index_leq_minus_two@{} {n}
  : n <= -2 -> n = -2.
Proof.
  destruct n.
  1: reflexivity.
  contradiction.
Defined.

Definition trunc_index_leq_succ'@{} n m
  : n <= m -> n <= m.+1.
Proof.
  revert m.
  induction n as [|n IHn] using trunc_index_ind.
  1: exact _.
  intros m p; cbn.
  induction m as [|m IHm] using trunc_index_ind.
  1: destruct p.
  apply IHn, p.
Defined.

Instance trunc_index_leq_refl@{}
  : Reflexive trunc_index_leq.
Proof.
  intro n.
  by induction n as [|n IHn] using trunc_index_ind.
Defined.

Instance trunc_index_leq_transitive@{}
  : Transitive trunc_index_leq.
Proof.
  intros a b c p q.
  revert b a c p q.
  induction b as [|b IHb] using trunc_index_ind.
  { intros a c p.
    by destruct (trunc_index_leq_minus_two p). }
  induction a as [|a IHa] using trunc_index_ind;
  induction c as [|c IHc] using trunc_index_ind.
  all: intros.
  1,2: exact tt.
  1: contradiction.
  cbn in p, q; cbn.
  by apply IHb.
Defined.

Definition trunc_index_leq_add@{} n m
  : n <= m +2+ n.
Proof.
  simple_induction m m IHm.
  - reflexivity.
  - rapply trunc_index_leq_transitive.
Defined.

Definition trunc_index_leq_add'@{} n m
  : n <= n +2+ m.
Proof.
  rewrite trunc_index_add_comm.
  apply trunc_index_leq_add.
Defined.

Fixpoint trunc_index_min@{} (n m : trunc_index)
  : trunc_index.
Proof.
  destruct n.
  1: exact (-2).
  destruct m.
  1: exact (-2).
  exact (trunc_index_min n m).+1.
Defined.

Definition trunc_index_min_minus_two@{} n
  : trunc_index_min n (-2) = -2.
Proof.
  by destruct n.
Defined.

Definition trunc_index_min_swap@{} n m
  : trunc_index_min n m = trunc_index_min m n.
Proof.
  revert m.
  simple_induction n n IHn; intro m.
  { symmetry.
    apply trunc_index_min_minus_two. }
  simple_induction m m IHm.
  1: reflexivity.
  cbn; apply ap, IHn.
Defined.

Definition trunc_index_min_path@{} n m
  : (trunc_index_min n m = n) + (trunc_index_min n m = m).
Proof.
  revert m; simple_induction n n IHn; intro m.
  1: by apply inl.
  simple_induction m m IHm.
  1: by apply inr.
  destruct (IHn m).
  1: apply inl.
  2: apply inr.
  1,2: cbn; by apply ap.
Defined.

Definition trunc_index_min_leq_left@{} (n m : trunc_index)
  : trunc_index_min n m <= n.
Proof.
  revert n m.
  refine (trunc_index_ind _ _ _); [ | intros n IHn ].
  all: refine (trunc_index_ind _ _ _); [ | intros m IHm ].
  all: try exact tt.
  exact (IHn m).
Defined.

Definition trunc_index_min_leq_right@{} (n m : trunc_index)
  : trunc_index_min n m <= m.
Proof.
  revert n m.
  refine (trunc_index_ind _ _ _); [ | intros n IHn ].
  all: refine (trunc_index_ind _ _ _); [ | intros m IHm ].
  all: try exact tt.
  exact (IHn m).
Defined.

(** ** Truncatedness proper. *)

(** A contractible space is (-2)-truncated, by definition. This function is the identity, so there is never any need to actually use it, but it exists to be found in searches. *)
Definition contr_istrunc_minus_two `{H : IsTrunc (-2) A} : Contr A
  := H.

(** Truncation levels are cumulative. *)
Instance istrunc_paths' {n : trunc_index} {A : Type} `{IsTrunc n A}
  : forall x y : A, IsTrunc n (x = y) | 1000.
Proof.
  generalize dependent A.
  simple_induction n n IH; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply istrunc_S.  rapply IH.
Defined.

Instance istrunc_succ {n : trunc_index} {A : Type} `{IsTrunc n A}
  : IsTrunc n.+1 A | 1000.
Proof.
  apply istrunc_S.
  exact istrunc_paths'.
Defined.

(** This could be an [Instance] (with very high priority, so it doesn't get applied trivially).  However, we haven't given typeclass search any hints allowing it to solve goals like [m <= n], so it would only ever be used trivially.  *)
Definition istrunc_leq {m n} (Hmn : m <= n) `{IsTrunc m A}
  : IsTrunc n A.
Proof.
  generalize dependent A; generalize dependent m.
  simple_induction n n' IH;
    intros [ | m'] Hmn A ? .
  - (* -2, -2 *) assumption.
  - (* S m', -2 *) destruct Hmn.
  - (* -2, S n' *) apply @istrunc_succ, (IH (-2)); auto.
  - (* S m', S n' *)
    apply istrunc_S.
    intros x y; apply (IH m'); auto with typeclass_instances.
Defined.

(** In particular, a contractible type, hprop, or hset is truncated at all higher levels.  We don't allow these to be used as idmaps, since there would be no point to it. *)

Definition istrunc_contr {n} {A} `{Contr A} : IsTrunc n.+1 A
  := (@istrunc_leq (-2) n.+1 tt _ _).

Definition istrunc_hprop {n} {A} `{IsHProp A} : IsTrunc n.+2 A
  := (@istrunc_leq (-1) n.+2 tt _ _).

Definition istrunc_hset {n} {A} `{IsHSet A}
  : IsTrunc n.+3 A
  := (@istrunc_leq 0 n.+3 tt _ _).

(** Consider the preceding definitions as instances for typeclass search, but only if the requisite hypothesis is already a known assumption; otherwise they result in long or interminable searches. *)
#[export] Hint Immediate istrunc_contr : typeclass_instances.
#[export] Hint Immediate istrunc_hprop : typeclass_instances.
#[export] Hint Immediate istrunc_hset : typeclass_instances.

(** Equivalence preserves truncation (this is, of course, trivial with univalence).  This is not an [Instance] because it causes infinite loops. *)
Definition istrunc_isequiv_istrunc A {B} (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  simple_induction n n IH; simpl; intros A ? B f ?.
  - exact (contr_equiv _ f).
  - apply istrunc_S.
    intros x y.
    exact (IH _ _ _ (ap (f^-1))^-1 _).
Defined.

Definition istrunc_equiv_istrunc A {B} (f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B
  := istrunc_isequiv_istrunc A f.

(** ** Truncated morphisms *)

Class IsTruncMap (n : trunc_index) {X Y : Type} (f : X -> Y)
  := istruncmap_fiber :: forall y:Y, IsTrunc n (hfiber f y).

Notation IsEmbedding := (IsTruncMap (-1)).

(** ** Universes of truncated types *)

(** It is convenient for some purposes to consider the universe of all n-truncated types (within a given universe of types).  In particular, this allows us to state the important fact that each such universe is itself (n+1)-truncated. *)

Record TruncType (n : trunc_index) := {
  trunctype_type : Type ;
  trunctype_istrunc :: IsTrunc n trunctype_type
}.

Arguments Build_TruncType _ _ {_}.
Arguments trunctype_type {_} _.
Arguments trunctype_istrunc [_] _.

Coercion trunctype_type : TruncType >-> Sortclass.

Notation "n -Type" := (TruncType n) : type_scope.
Notation HProp := (-1)-Type.
Notation HSet := 0-Type.

Notation Build_HProp := (Build_TruncType (-1)).
Notation Build_HSet := (Build_TruncType 0).

(** This is (as of October 2014) the only [Canonical Structure] in the library.  It would be nice to do without it, in the interests of minimizing the number of fancy Coq features that the reader needs to know about. *)
Canonical Structure default_TruncType := fun n T P => (@Build_TruncType n T P).

(** Version of [smalltype] for n-Types. *)
Definition smallntype@{i j} (n : trunc_index) (P : TruncType@{j} n) {smallP : IsSmall@{i j} P}
  : TruncType@{i} n.
Proof.
  napply (Build_TruncType n (smalltype P)).
  apply (@istrunc_equiv_istrunc _ _ (equiv_smalltype P)^-1 n _).
Defined.

Notation smallhprop := (smallntype (-1)).

(** ** Facts about hprops *)

(** An inhabited proposition is contractible.  This is not an [Instance] because it causes infinite loops. *)
Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  apply (Build_Contr _ x).
  intro y.
  rapply center.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Instance hprop_inhabited_contr (A : Type)
  : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H; apply istrunc_S; intros x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** Any two points in an hprop are connected by a path. *)
Theorem path_ishprop `{H : IsHProp A}
  : forall x y : A, x = y.
Proof.
  intros x y.
  rapply center.
Defined.

(** Conversely, this property characterizes hprops. *)
Theorem hprop_allpath (A : Type)
  : (forall (x y : A), x = y) -> IsHProp A.
Proof.
  intros H; apply istrunc_S; intros x y.
  napply contr_paths_contr.
  exact (Build_Contr _ x (H x)).
Defined.

(** Two propositions are equivalent as soon as there are maps in both directions. *)
Definition isequiv_iff_hprop `{IsHProp A} `{IsHProp B}
  (f : A -> B) (g : B -> A)
  : IsEquiv f.
Proof.
  apply (isequiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop_uncurried `{IsHProp A} `{IsHProp B}
  : (A <-> B) -> (A <~> B).
Proof.
  intro fg.
  apply (equiv_adjointify (fst fg) (snd fg));
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B)
  := fun f g => equiv_iff_hprop_uncurried (f, g).

Corollary iff_contr_hprop (A : Type) `{IsHProp A}
  : Contr A <-> A.
Proof.
  split.
  - apply center.
  - rapply contr_inhabited_hprop.
Defined.

(** ** Truncatedness: any dependent product of n-types is an n-type *)

Definition contr_forall `{Funext} `{P : A -> Type} `{forall a, Contr (P a)}
  : Contr (forall a, P a).
Proof.
  apply (Build_Contr _ (fun a => center (P a))).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

Instance istrunc_forall `{Funext} `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a) | 100.
Proof.
  generalize dependent P.
  simple_induction n n IH; simpl; intros P ?.
  (* case [n = -2], i.e. contractibility *)
  - exact contr_forall.
  (* case n = n'.+1 *)
  - apply istrunc_S.
    intros f g; exact (istrunc_isequiv_istrunc@{u1 u1} _ (apD10@{_ _ u1} ^-1)).
Defined.

(** Truncatedness is an hprop. *)
Instance ishprop_istrunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A) | 0.
Proof.
  revert A; simple_induction n n IH; cbn; intro A.
  - napply (istrunc_equiv_istrunc _ (equiv_istrunc_unfold (-2) A)^-1%equiv).
    apply hprop_allpath.
    intros [a1 c1] [a2 c2].
    destruct (c1 a2).
    apply (ap (exist _ a1)).
    funext x.
    pose (Build_Contr _ a1 c1); apply path2_contr.
  - exact (istrunc_equiv_istrunc _ (equiv_istrunc_unfold n.+1 A)^-1%equiv).
    (* This case follows from [istrunc_forall]. *)
Defined.

(** By [trunc_hprop], it follows that [IsTrunc n A] is also [m]-truncated for any [m >= -1]. *)

(** Similarly, a map being truncated is also a proposition. *)
Instance ishprop_istruncmap `{Funext} (n : trunc_index) {X Y : Type} (f : X -> Y)
: IsHProp (IsTruncMap n f).
Proof.
  apply hprop_allpath; intros s t.
  apply path_forall; intros x.
  apply path_ishprop.
Defined.

(** If a type [A] is [n]-truncated, then [IsTrunc n A] is contractible. *)
Instance contr_istrunc `{Funext} (n : trunc_index) (A : Type) `{istruncA : IsTrunc n A}
  : Contr (IsTrunc n A) | 100
  := contr_inhabited_hprop _ _.

Corollary equiv_contr_hprop (A : Type) `{Funext} `{IsHProp A}
  : Contr A <~> A.
Proof.
  exact (equiv_iff_hprop_uncurried (iff_contr_hprop A)).
Defined.

(** If a type [A] implies that it is [n.+1]-truncated, then it is [n.+1]-truncated. **)
Definition istrunc_inhabited_istrunc {n : trunc_index}
  {A : Type} (H : A -> IsTrunc n.+1 A)
  : IsTrunc n.+1 A
  := istrunc_S _ (fun a b => H a a b).

(** If you are looking for a theorem about truncation, you may want to read the note "Finding Theorems" in "STYLE.md". *)
