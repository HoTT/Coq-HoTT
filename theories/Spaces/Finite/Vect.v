Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.DProp
  HoTT.Spaces.Finite.Fin
  HoTT.Spaces.Finite.FinInduction
  HoTT.Spaces.Nat.

(** Finite-dimensional vector. Note that the induction principle
    [vect_ind] uses funext and does not compute. *)

Definition Vect (n : nat) (A : Type) : Type := Fin n -> A.

(** The empty vector. *)

Definition vnil {A : Type} : Vect 0 A := Empty_rec.

Definition path_vnil `{Funext} {A : Type} (v : Vect 0 A) : vnil = v.
Proof.
  apply path_contr.
Defined.

(** Add an element in the end of a vector, [vcons'] and [vcons]. *)

Definition vcons' {A : Type} (n : nat) (a : A) (v : Vect (pred n) A)
  : Vect n A
  := fun i =>  fin_rec (fun n => Vect (pred n) A -> A)
                       (fun _ _ => a) (fun n' i _ v => v i) i v.

Definition vcons {A : Type} {n : nat} : A -> Vect n A -> Vect n.+1 A
  := vcons' n.+1.

(** Take the first element is a non-empty vector, [vhead'] and [vhead]. *)

Definition vhead' {A} (n : nat) : n > 0 -> Vect n A -> A
  := match n with
     | 0 => fun N _ => Empty_rec N
     | n'.+1 => fun _ v => v fin_zero
     end.

Definition vhead {A} {n : nat} : Vect n.+1 A -> A := vhead' n.+1 tt.

Definition compute_vhead' {A} n (N : n > 0) (a : A) (v : Vect (pred n) A)
  : vhead' n N (vcons' n a v) = a.
Proof.
  destruct n; [elim N|].
  exact (apD10 (compute_fin_rec_fin_zero _ _ _ _) v).
Defined.

Definition compute_vhead {A} {n} (a : A) (v : Vect n A)
  : vhead (vcons a v) = a.
Proof.
  apply compute_vhead'.
Defined.

(** If the vector is non-empty, then remove the first element. *)

Definition vtail' {A} (n : nat) : Vect n A -> Vect (pred n) A
  := match n with
     | 0 => fun _ => Empty_rec
     | n'.+1 => fun v i => v (fsucc i)
     end.

(** Remove the first element from a non-empty vector. *)

Definition vtail {A} {n : nat} : Vect n.+1 A -> Vect n A := vtail' n.+1.

Definition compute_vtail' {A} n (a : A) (v : Vect (pred n) A)
  : vtail' n (vcons' n a v) == v.
Proof.
  intro i.
  destruct n; [elim i|].
  exact (apD10 (compute_fin_rec_fsucc _ _ _ _) v).
Defined.

Definition compute_vtail `{Funext} {A} {n} (a : A) (v : Vect n A)
  : vtail (vcons a v) = v.
Proof.
  funext i.
  apply compute_vtail'.
Defined.

(** A non-empty vector is the [vcons] of its head and tail,
    [path_expand_vcons'] and [path_expand_vcons]. *)

Lemma path_expand_vcons' {A : Type} (n : nat)
  (i : Fin n) (N : n > 0) (v : Vect n A)
  : vcons' n (vhead' n N v) (vtail' n v) i = v i.
Proof.
  induction i using fin_ind.
  - apply compute_vhead.
  - apply (compute_vtail' n.+1 (vhead v) (vtail v)).
Defined.

Lemma path_expand_vcons `{Funext} {A} {n} (v : Vect n.+1 A)
  : vcons (vhead v) (vtail v) = v.
Proof.
  funext i.
  apply path_expand_vcons'.
Defined.

(** The following [path_vcons'] and [path_vcons] gives a way to construct
    a path between [vcons] vectors. They cooperate nicely with
    [path_expand_vcons'] and [path_expand_vcons]. *)

Definition path_vcons' {A} n {a1 a2 : A} {v1 v2 : Vect (pred n) A}
  (p : a1 = a2) (q : forall i, v1 i = v2 i) (i : Fin n)
  : vcons' n a1 v1 i = vcons' n a2 v2 i.
Proof.
  induction i using fin_ind.
  - exact (compute_vhead _ _ @ p @ (compute_vhead _ _)^).
  - refine (_ @ (compute_vtail' n.+1 a2 v2 i)^).
    exact (compute_vtail' n.+1 a1 v1 i @ q i).
Defined.

Definition compute_path_vcons' {A} (n : nat)
    (a : A) (v : Vect (pred n) A) (i : Fin n)
    : path_vcons' n (idpath a) (fun j => idpath (v j)) i = idpath.
Proof.
  induction i using fin_ind; unfold path_vcons'.
  - rewrite compute_fin_ind_fin_zero.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
  - rewrite compute_fin_ind_fsucc.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
Qed.

Definition path_vcons `{Funext} {A} {n} {a1 a2 : A} (p : a1 = a2)
  {v1 v2 : Vect n A} (q : v1 = v2)
  : vcons a1 v1 = vcons a2 v2.
Proof.
  funext i. apply path_vcons'.
  - assumption.
  - intro j. exact (apD10 q j).
Defined.

Lemma compute_path_vcons `{Funext} {A} {n} (a : A) (v : Vect n A)
  : path_vcons (idpath a) (idpath v) = idpath.
Proof.
  refine (ap (path_forall _ _) _ @ eta_path_forall _ _ _).
  funext i. exact (compute_path_vcons' n.+1 a v i).
Defined.

(** The lemmas [path_expand_vcons_vcons'] and [path_expand_vcons_vcons]
    identify [path_expand_vcons'] with [path_vcons'] and
    [path_expand_vcons] with [path_vcons]. *)

Lemma path_expand_vcons_vcons' {A : Type} (n : nat)
  (N : n > 0) (a : A) (v : Vect (pred n) A) (i : Fin n)
  : path_expand_vcons' n i N (vcons' n a v) =
    path_vcons' n (compute_vhead' n N a v) (compute_vtail' n a v) i.
Proof.
  induction i using fin_ind; unfold path_vcons', path_expand_vcons'.
  - do 2 rewrite compute_fin_ind_fin_zero.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
  - do 2 rewrite compute_fin_ind_fsucc.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
Qed.

Lemma path_expand_vcons_vcons `{Funext}
  {A : Type} {n : nat} (a : A) (v : Vect n A)
  : path_expand_vcons (vcons a v) =
    path_vcons (compute_vhead a v) (compute_vtail a v).
Proof.
  refine (ap (path_forall _ _) _).
  funext i.
  pose (p := eisretr apD10 (compute_vtail' n.+1 a v)).
  refine (_ @ (ap (fun f => _ f i) p)^).
  exact (path_expand_vcons_vcons' n.+1 tt a v i).
Defined.

(** The induction principle for finite dimensional vectors, [vect_ind].
    Note that it uses funext and does not compute. *)

Lemma vect_ind `{Funext} {A : Type} (P : forall n, Vect n A -> Type)
  (z : P 0 vnil) (s : forall n a (v : Vect n A), P n v -> P n.+1 (vcons a v))
  {n : nat} (v : Vect n A)
  : P n v.
Proof.
  induction n.
  - exact (transport (P 0) (path_vnil v) z).
  - refine (transport (P n.+1) (path_expand_vcons v) _).
    apply s. apply IHn.
Defined.

Lemma compute_vect_ind_vnil `{Funext} {A : Type}
  (P : forall n, Vect n A -> Type) (z : P 0 vnil)
  (s : forall (n : nat) (a : A) (v : Vect n A), P n v -> P n.+1 (vcons a v))
  : vect_ind P z s vnil = z.
Proof.
  exact (ap (fun x => _ x z) (hset_path2 1 (path_vnil vnil)))^.
Defined.

Lemma compute_vect_ind_vcons `{Funext} {A : Type}
  (P : forall n, Vect n A -> Type) (z : P 0 vnil)
  (s : forall (n : nat) (a : A) (v : Vect n A), P n v -> P n.+1 (vcons a v))
  {n : nat} (a : A) (v : Vect n A)
  : vect_ind P z s (vcons a v) = s n a v (vect_ind P z s v).
Proof.
  simpl.
  induction (path_expand_vcons_vcons a v)^.
  set (p1 := compute_vhead a v).
  set (p2 := compute_vtail a v).
  induction p1, p2.
  exact (ap (fun p => transport _ p _) (compute_path_vcons _ _)).
Defined.

