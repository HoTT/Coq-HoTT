Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.implementations.list
  HoTT.Basics.Overture
  HoTT.Spaces.Nat.

(* Disable automatic generation of elimination schemes to avoid
   generation of induction/recursion principles to [Prop]/[Set]. *)

Local Unset Elimination Schemes.

Declare Scope ne_list_scope.

Delimit Scope ne_list_scope with ne_list.

Open Scope ne_list_scope.

(** Nonempty list implementation [ne_list.ne_list]. *)

Module ne_list.

(** A nonempty list. Below there is an implicit coercion
    [ne_list >-> list]. *)

Inductive ne_list (T:Type) : Type
  := one: T → ne_list T | cons: T → ne_list T → ne_list T.

Arguments one {T}.
Arguments cons {T}.

Scheme ne_list_ind := Induction for ne_list Sort Type.
Arguments ne_list_ind [T].

Scheme ne_list_rec := Minimality for ne_list Sort Type.
Arguments ne_list_rec [T].

Definition ne_list_rect := ne_list_ind.
Arguments ne_list_rect [T].

Section with_type.
  Context {T: Type}.

  Fixpoint app (a b: ne_list T): ne_list T :=
    match a with
    | one x => cons x b
    | cons x y => cons x (app y b)
    end.

  Fixpoint foldr {R} (u: T → R) (f: T → R → R) (a: ne_list T): R :=
    match a with
    | one x => u x
    | cons x y => f x (foldr u f y)
    end.

  Fixpoint foldr1 (f: T → T → T) (a: ne_list T): T :=
    match a with
    | one x => x
    | cons x y => f x (foldr1 f y)
    end.

  Definition head (l: ne_list T): T
    := match l with one x => x | cons x _ => x end.

  Fixpoint to_list (l: ne_list T): list T :=
    match l with
    | one x => x :: nil
    | cons x xs => x :: to_list xs
    end.

  Fixpoint from_list (x: T) (xs: list T): ne_list T :=
    match xs with
    | nil => one x
    | Datatypes.cons h t => cons x (from_list h t)
    end.

  Definition tail (l: ne_list T): list T
    := match l with one _ => nil | cons _ x => to_list x end.

  Lemma decomp_eq (l: ne_list T): l = from_list (head l) (tail l).
  Proof with auto.
    induction l...
    destruct l...
    cbn in *.
    rewrite IHl...
  Qed. 

  Definition last: ne_list T → T := foldr1 (fun x y => y).

  Fixpoint replicate_Sn (x: T) (n: nat): ne_list T :=
    match n with
    | 0 => one x
    | S n' => cons x (replicate_Sn x n')
    end.

  Fixpoint take (n: nat) (l: ne_list T): ne_list T :=
    match l, n with
    | cons x xs, S n' => take n' xs
    | _, _ => one (head l)
    end.

  Fixpoint front (l: ne_list T) : list T :=
    match l with
    | one _ => nil
    | cons x xs => x :: front xs
    end.

  Lemma two_level_rect (P: ne_list T → Type)
    (Pone: ∀ x, P (one x))
    (Ptwo: ∀ x y, P (cons x (one y)))
    (Pmore: ∀ x y z, P z → (∀ y', P (cons y' z)) → P (cons x (cons y z)))
    : ∀ l, P l.
  Proof with auto.
   cut (∀ l, P l * ∀ x, P (cons x l)).
   - intros. apply X.
   - destruct l...
     revert t.
     induction l...
     intros.
     split.
     + apply IHl.
     + intro. apply Pmore; intros; apply IHl.
  Qed.

  Lemma tl_length (l: ne_list T)
    : S (length (tl (to_list l))) = length (to_list l).
  Proof. destruct l; reflexivity. Qed.
End with_type.

Fixpoint tails {T} (l: ne_list T): ne_list (ne_list T) :=
  match l with
  | one x => one (one x)
  | cons x y => cons l (tails y)
  end.

Lemma tails_are_shorter {T} (y x: ne_list T):
  InList x (to_list (tails y)) →
  le (length (to_list x)) (length (to_list y)).
Proof with auto.
 induction y using ne_list_ind; cbn.
 - intros [[] | C].
   + constructor.
   + elim C.
 - intros [[] | C]...
Qed.

Fixpoint map {A B} (f: A → B) (l: ne_list A): ne_list B :=
  match l with
  | one x => one (f x)
  | cons h t => cons (f h) (map f t)
  end.

Lemma list_map {A B} (f: A → B) (l: ne_list A)
  : to_list (map f l) = list.map f (to_list l).
Proof.
  induction l.
  - reflexivity.
  - cbn. rewrite <- IHl. reflexivity.
Qed.

Fixpoint inits {A} (l: ne_list A): ne_list (ne_list A) :=
  match l with
  | one x => one (one x)
  | cons h t => cons (one h) (map (cons h) (inits t))
  end.

Fixpoint zip {A B: Type} (l: ne_list A) (m: ne_list B)
  : ne_list (A * B) :=
  match l with
  | one a => one (a, head m)
  | cons a l =>
      match m with
      | one b => one (a, b)
      | cons b m => cons (a, b) (zip l m)
      end
  end.

  Module notations.

    Global Notation ne_list := ne_list.

    Global Notation "[: x :]" := (one x) : ne_list_scope.

    Global Notation "[: x ; .. ; y ; z :]"
        := (cons x .. (cons y (one z)) ..) : ne_list_scope.

    Global Infix ":::" := cons (at level 60, right associativity) : ne_list_scope.

  End notations.

End ne_list.

Global Coercion ne_list.to_list : ne_list.ne_list >-> list.
