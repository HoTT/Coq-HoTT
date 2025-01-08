(** The HoTT Book Exercises formalization. *)

(** This file records formalized solutions to the HoTT Book exercises. *)

(*  See HoTTBook.v for an IMPORTANT NOTE FOR THE HoTT DEVELOPERS.

    PROCEDURE FOR UPDATING THE FILE:

   1. Compile the latest version of the HoTT Book to update the LaTeX
      labels. Do not forget to pull in changes from HoTT/HoTT.

   2. Run `etc/Book.py` using the `--exercises` flag (so your command
      should look like `cat ../book/*.aux | etc/Book.py --exercises contrib/HoTTBookExercises.v`)
      If it complains, fix things.

   3. Add contents to new entries.

   4. Run `etc/Book.py` again to make sure it is happy.

   5. Compile this file with `make contrib` or `make contrib/HoTTBookExercises.vo`.

   6. Do the git thing to submit your changes.

*)

From HoTT Require Import Basics Types HProp HSet Projective
     TruncType Truncations Modalities.Notnot Modalities.Open Modalities.Closed
     BoundedSearch Equiv.BiInv Spaces.Nat Spaces.Torus.TorusEquivCircles
     Classes.implementations.peano_naturals Metatheory.Core Metatheory.FunextVarieties.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope path_scope.

(* END OF PREAMBLE *)
(* ================================================== ex:composition *)
(** Exercise 1.1 *)

Definition Book_1_1 := (fun (A B C : Type) (f : A -> B) (g : B -> C) => g o f).

Theorem Book_1_1_refl : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
                          h o (g o f) = (h o g) o f.
Proof.
  reflexivity.
Defined.

(* ================================================== ex:pr-to-rec *)
(** Exercise 1.2 *)

(** Recursor as equivalence. *)
Definition Book_1_2_prod_lib := @HoTT.Types.Prod.equiv_uncurry.
Section Book_1_2_prod.
  Variable A B : Type.

  (** Recursor with projection functions instead of pattern-matching. *)
  Let prod_rec_proj C (g : A -> B -> C) (p : A * B) : C
    := g (fst p) (snd p).
  Definition Book_1_2_prod := prod_rec_proj.

  Proposition Book_1_2_prod_fst : fst = prod_rec_proj A (fun a b => a).
  Proof.
    reflexivity.
  Defined.

  Proposition Book_1_2_prod_snd : snd = prod_rec_proj B (fun a b => b).
  Proof.
    reflexivity.
  Defined.
End Book_1_2_prod.

(** Recursor as (dependent) equivalence. *)
Definition Book_1_2_sig_lib := @HoTT.Types.Sigma.equiv_sig_ind.
Section Book_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.

  (** Non-dependent recursor with projection functions instead of pattern matching. *)
  Let sig_rec_proj C (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C
    := g (pr1 p) (pr2 p).
  Definition Book_1_2_sig := @sig_rec_proj.

  Proposition Book_1_2_sig_fst : @pr1 A B = sig_rec_proj A (fun a => fun b => a).
  Proof.
    reflexivity.
  Defined.

  (** NB: You cannot implement pr2 with only the recursor, so it is not possible
      to check its definitional equality as the exercise suggests. *)
End Book_1_2_sig.

(* ================================================== ex:pr-to-ind *)
(** Exercise 1.3 *)

(** The propositional uniqueness principles are named with an
    'eta' postfix in the HoTT library. *)

Definition Book_1_3_prod_lib := @HoTT.Types.Prod.prod_ind.
Section Book_1_3_prod.
  Variable A B : Type.

  Let prod_ind_eta (C : A * B -> Type) (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x
    := transport C (HoTT.Types.Prod.eta_prod x) (g (fst x) (snd x)).
  Definition Book_1_3_prod := prod_ind_eta.

  Proposition Book_1_3_prod_refl : forall C g a b, prod_ind_eta C g (a, b) = g a b.
  Proof.
    reflexivity.
  Defined.
End Book_1_3_prod.

Definition Book_1_3_sig_lib := @HoTT.Basics.Overture.sig_ind.
Section Book_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.

  Let sig_ind_eta (C : (exists (a : A), B a) -> Type)
                          (g : forall (a : A) (b : B a), C (a; b))
                          (x : exists (a : A), B a) : C x
    := transport C (HoTT.Types.Sigma.eta_sigma x) (g (pr1 x) (pr2 x)).
  Definition Book_1_3_sig := sig_ind_eta.

  Proposition Book_1_3_sig_refl : forall C g a b, sig_ind_eta C g (a; b) = g a b.
  Proof.
    reflexivity.
  Defined.
End Book_1_3_sig.

(* ================================================== ex:iterator *)
(** Exercise 1.4 *)

Section Book_1_4.
  Fixpoint Book_1_4_iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C
    := match n with
      | O => c0
      | S m => cs (Book_1_4_iter C c0 cs m)
      end.

  Definition Book_1_4_rec' (C : Type) (c0 : C) (cs : nat -> C -> C) : nat -> nat * C
    := Book_1_4_iter (nat * C) (O, c0) (fun x => (S (fst x), cs (fst x) (snd x))).
  
  Definition Book_1_4_rec (C : Type) (c0 : C) (cs : nat -> C -> C) (n : nat) : C
    := snd (Book_1_4_rec' C c0 cs n).

  Lemma Book_1_4_aux : forall C c0 cs n, fst (Book_1_4_rec' C c0 cs n) = n.
  Proof.
    intros C c0 cs n. induction n as [| m IH].
    - simpl. reflexivity.
    - cbn. exact (ap S IH).
  Qed.

  Proposition Book_1_4_eq
    : forall C c0 cs n, Book_1_4_rec C c0 cs n = nat_rect (fun _ => C) c0 cs n.
  Proof. 
    intros C c0 cs n. induction n as [| m IH].
    - simpl. reflexivity.
    - change (cs (fst (Book_1_4_rec' C c0 cs m)) (Book_1_4_rec C c0 cs m)
              = cs m (nat_rect (fun _ => C) c0 cs m)).
      lhs rapply (ap (fun x => cs x _) (Book_1_4_aux _ _ _ _)).
      exact (ap (cs m) IH).
  Qed.
End Book_1_4.

(* ================================================== ex:sum-via-bool *)
(** Exercise 1.5 *)

Section Book_1_5.
  Definition Book_1_5_sum (A B : Type) := { x : Bool & if x then A else B }.

  Notation "'inl' a" := (true; a) (at level 0).
  Notation "'inr' b" := (false; b) (at level 0).

  Definition Book_1_5_ind (A B : Type) (C : Book_1_5_sum A B -> Type) (f : forall a, C (inl a))
   (g : forall b, C (inr b)) : forall x : Book_1_5_sum A B, C x := fun x => match x with
   | inl a => f a
   | inr b => g b
   end.

  Theorem inl_red {A B : Type} {C : Book_1_5_sum A B -> Type} f g { a : A }
  : Book_1_5_ind A B C f g (inl a) = f a.
  Proof. reflexivity. Defined.

  Theorem inr_red {A B : Type} {C : Book_1_5_sum A B -> Type} f g { b : B }
  : Book_1_5_ind A B C f g (inr b) = g b.
  Proof. reflexivity. Defined.
End Book_1_5.

(* ================================================== ex:prod-via-bool *)
(** Exercise 1.6 *)

Section Book_1_6.
  Context `{Funext}.

  Definition Book_1_6_prod (A B : Type) := forall x : Bool, (if x then A else B).

  Definition Book_1_6_mk_pair {A B : Type} (a : A) (b : B) : Book_1_6_prod A B
    := fun x => match x with
              | true => a
              | false => b
              end.

  Notation "( a , b )" := (Book_1_6_mk_pair a b) (at level 0).
  Notation "'pr1' p" := (p true) (at level 0).
  Notation "'pr2' p" := (p false) (at level 0).

  Definition Book_1_6_eq {A B : Type} (p : Book_1_6_prod A B) : (pr1 p, pr2 p) == p
    := fun x => match x with
              | true => 1
              | false => 1
              end.

  Theorem Book_1_6_id {A B : Type} (a : A) (b : B) : Book_1_6_eq (a, b) = (fun x => 1).
  Proof.
    apply path_forall. intros x. destruct x; reflexivity.
  Qed.

  Definition Book_1_6_eta {A B : Type} (p : Book_1_6_prod A B) : (pr1 p, pr2 p) = p
    := path_forall (pr1 p, pr2 p) p (Book_1_6_eq p).

  Definition Book_1_6_ind {A B : Type} (C : Book_1_6_prod A B -> Type) (f : forall a b, C (a, b))
    (p : Book_1_6_prod A B) : C p
    := transport C (Book_1_6_eta p) (f (pr1 p) (pr2 p)).

  Theorem Book_1_6_red {A B : Type} (C : Book_1_6_prod A B -> Type) f a b
    : Book_1_6_ind C f (a, b) = f a b.
  Proof.
    unfold Book_1_6_ind, Book_1_6_eta. simpl.
    rewrite Book_1_6_id, path_forall_1.
    reflexivity.
  Qed.
End Book_1_6.

(* ================================================== ex:pm-to-ml *)
(** Exercise 1.7 *)

Section Book_1_7.
  Definition Book_1_7_id {A : Type}
    : forall {x y : A} (p : x = y), (x; 1) = (y; p) :> { a : A & x = a }
    := paths_ind' (fun (x y : A) (p : x = y) => (x; 1) = (y; p)) (fun x => 1).

  Definition Book_1_7_transport {A : Type} (P : A -> Type)
    : forall {x y : A} (p : x = y), P x -> P y
    := paths_ind' (fun (x y : A) (p : x = y) => P x -> P y) (fun x => idmap).

  Definition Book_1_7_ind' {A : Type} (a : A) (C : forall x, (a = x) -> Type)
    (c : C a 1) (x : A) (p : a = x)
    : C x p
    := Book_1_7_transport (fun r => C (pr1 r) (pr2 r)) (Book_1_7_id p) c.

  Definition Book_1_7_eq {A : Type} (a : A) (C : forall x, (a = x) -> Type) (c : C a 1)
    : Book_1_7_ind' a C c a 1 = c
    := 1.
End Book_1_7.

(* ================================================== ex:nat-semiring *)
(** Exercise 1.8 *)

Section Book_1_8.
  Fixpoint Book_1_8_rec_nat (C : Type) c0 cs (n : nat) : C
    := match n with
      | O => c0
      | S m => cs m (Book_1_8_rec_nat C c0 cs m)
      end.

  Definition Book_1_8_add : nat -> nat -> nat
    := Book_1_8_rec_nat (nat -> nat) (fun m => m) (fun n g m => (S (g m))).

  Definition Book_1_8_mult : nat -> nat -> nat
    := Book_1_8_rec_nat (nat -> nat) (fun m => 0) (fun n g m => Book_1_8_add m (g m)).

  (* [Book_1_8_rec_nat] gives back a function with the wrong argument order, so we flip the order of the arguments [p] and [q]. *)
  Definition Book_1_8_exp : nat -> nat -> nat
    := fun p q =>
        (Book_1_8_rec_nat (nat -> nat) (fun m => (S 0)) (fun n g m => Book_1_8_mult m (g m))) q p.

  Example add_example: Book_1_8_add 32 17 = 49 := 1.
  Example mult_example: Book_1_8_mult 20 5 = 100 := 1.
  Example exp_example: Book_1_8_exp 2 10 = 1024 := 1.

  Definition Book_1_8_semiring := HoTT.Classes.implementations.peano_naturals.nat_semiring.
End Book_1_8.

(* ================================================== ex:fin *)
(** Exercise 1.9 *)

Section Book_1_9.
  Fixpoint Book_1_9_Fin (n : nat) : Type
    := match n with
      | O => Empty
      | S m => (Book_1_9_Fin m) + Unit
      end.

  Definition Book_1_9_fmax (n : nat) : Book_1_9_Fin (S n) := inr tt.
End Book_1_9.

(* ================================================== ex:ackermann *)
(** Exercise 1.10 *)

Fixpoint ack (n m : nat) : nat 
  := match n with
    | O => S m
    | S p => let fix ackn (m : nat)
              := match m with
                | O => ack p 1
                | S q => ack p (ackn q)
                end
            in ackn m
    end.

Definition Book_1_10 := ack.

(* ================================================== ex:neg-ldn *)
(** Exercise 1.11 *)

Section Book_1_11.
  Theorem dblneg : forall A, (~~~A) -> ~A.
  Proof.
    intros A f a; apply f.
    intros g; apply g.
    exact a.
  Defined.
End Book_1_11.

(* ================================================== ex:tautologies *)
(** Exercise 1.12 *)

Section Book_1_12.
  Theorem Book_1_12_part1 : forall A B, A -> (B -> A).
  Proof.
    intros ? ? a ?.
    exact a.
  Defined.

  Theorem Book_1_12_part2 : forall A, A -> ~~A.
  Proof.
    intros A a f.
    exact (f a).
  Defined.

  Theorem Book_1_12_part3 : forall A B, ((~A) + (~B)) -> ~(A * B).
  Proof.
    intros A B [na | nb] [a b].
    - exact (na a).
    - exact (nb b).
  Qed.
End Book_1_12.

(* ================================================== ex:not-not-lem *)
(** Exercise 1.13 *)

Section Book_1_13.
  Lemma Book_1_13_aux: forall A B, ~(A + B) -> ~A * ~B.
  Proof.
    intros A B nAorB; split.
    - intro a; exact (nAorB (inl a)).
    - intro b; exact (nAorB (inr b)).
  Qed.

  Theorem Book_1_13 : forall P, ~~(P + ~P).
  Proof.
    intros P f. apply Book_1_13_aux in f. destruct f as [np nnp].
    exact (nnp np).
  Qed.

  Theorem Book_1_13_direct : forall P, ~~(P + ~P).
  Proof.
    intros P f.
    apply f. apply inr. intro p. apply f.
    exact (inl p).
  Qed.
End Book_1_13.

(* ================================================== ex:without-K *)
(** Exercise 1.14 *)

(** There is no adequate type family C : Pi_{x, y, p} U  such that C(x, x, p) is p = refl x definitionally. *)

(* ================================================== ex:subtFromPathInd *)
(** Exercise 1.15 *)

Definition Book_1_15_paths_rec {A : Type} {C : A -> Type} {x y : A} (p : x = y) : C x -> C y 
  := match p with 1 => idmap end.
(** This is exactly the definition of [transport] from Basics.Overture. *)

(* ================================================== ex:add-nat-commutative *)
(** Exercise 1.16 *)

Definition Book_1_16 := HoTT.Spaces.Nat.Core.nat_add_comm.

(* ================================================== ex:basics:concat *)
(** Exercise 2.1 *)

(* Book_2_1_concatenation1 is equivalent to the proof given in the text *)
Definition Book_2_1_concatenation1 :
    forall {A : Type} {x y z : A}, x = y -> y = z -> x = z.
Proof.
  intros A x y z x_eq_y y_eq_z.
  induction x_eq_y.
  induction y_eq_z.
  reflexivity.
Defined.

Definition Book_2_1_concatenation2 :
    forall {A : Type} {x y z : A}, x = y -> y = z -> x = z.
Proof.
  intros A x y z x_eq_y y_eq_z.
  induction x_eq_y.
  exact y_eq_z.
Defined.

Definition Book_2_1_concatenation3 :
    forall {A : Type} {x y z : A}, x = y -> y = z -> x = z.
Proof.
  intros A x y z x_eq_y y_eq_z.
  induction y_eq_z.
  exact x_eq_y.
Defined.

Local Notation "p *1 q" := (Book_2_1_concatenation1 p q) (at level 10).
Local Notation "p *2 q" := (Book_2_1_concatenation2 p q) (at level 10).
Local Notation "p *3 q" := (Book_2_1_concatenation3 p q) (at level 10).

Section Book_2_1_Proofs_Are_Equal.
  Context {A : Type} {x y z : A}.
  Variable (p : x = y) (q : y = z).
  Definition Book_2_1_concatenation1_eq_Book_2_1_concatenation2 : p *1 q = p *2 q.
  Proof.
    induction p, q.
    reflexivity.
  Defined.

  Definition Book_2_1_concatenation2_eq_Book_2_1_concatenation3 : p *2 q =  p *3 q.
  Proof.
    induction p, q.
    reflexivity.
  Defined.

  Definition Book_2_1_concatenation1_eq_Book_2_1_concatenation3 : p *1 q = p *3 q.
  Proof.
    induction p, q.
    reflexivity.
  Defined.
End Book_2_1_Proofs_Are_Equal.

(* ================================================== ex:eq-proofs-commute *)
(** Exercise 2.2 *)

Definition Book_2_2 :
  forall {A : Type} {x y z : A} (p : x = y) (q : y = z),
    (Book_2_1_concatenation1_eq_Book_2_1_concatenation2 p q) *1
    (Book_2_1_concatenation2_eq_Book_2_1_concatenation3 p q) =
    (Book_2_1_concatenation1_eq_Book_2_1_concatenation3 p q).
Proof.
  induction p, q.
  reflexivity.
Defined.

(* ================================================== ex:fourth-concat *)
(** Exercise 2.3 *)

(* Since we have x_eq_y : x = y we can transport y_eq_z : y = z along
   x_eq_y⁻¹ : y = x in the type family λw.(w = z) to obtain a term
   of type x = z. *)
Definition Book_2_1_concatenation4
    {A : Type} {x y z : A} : x = y -> y = z -> x = z :=
  fun x_eq_y y_eq_z => transport (fun w => w = z) (inverse x_eq_y) y_eq_z.

Local Notation "p *4 q" := (Book_2_1_concatenation4 p q) (at level 10).
Definition Book_2_1_concatenation1_eq_Book_2_1_concatenation4 :
    forall {A : Type} {x y z : A} (p : x = y) (q : y = z), (p *1 q = p *4 q).
Proof.
  induction p, q.
  reflexivity.
Defined.

(* ================================================== ex:npaths *)
(** Exercise 2.4 *)

Definition Book_2_4_npath : nat -> Type -> Type
  := nat_ind (fun (n : nat) => Type -> Type)
             (* 0-dimensional paths are elements *)
             (fun A => A)
             (* (n+1)-dimensional paths are paths between n-dimimensional paths *)
             (fun n f A => (exists a1 a2 : (f A), a1 = a2)).

(* This is the intuition behind definition of nboundary:
   As we've defined them, every (n+1)-path is a path between two n-paths. *)
Lemma npath_as_sig : forall {n : nat} {A : Type},
    (Book_2_4_npath (S n) A) = (exists (p1 p2 : Book_2_4_npath n A), p1 = p2).
Proof.
  reflexivity.
Defined.

(* It can be helpful to take a look at what this definition does.
   Try uncommenting the following lines: *)
(*
Context {A : Type}.
Eval compute in (Book_2_4_npath 0 A). (* = A : Type *)
Eval compute in (Book_2_4_npath 1 A). (* = {a1 : A & {a2 : A & a1 = a2}} : Type *)
Eval compute in (Book_2_4_npath 2 A). (* and so on... *)
*)

(* Given an (n+1)-path, we simply project to a pair of n-paths. *)
Definition Book_2_4_nboundary
  : forall {n : nat} {A : Type}, Book_2_4_npath (S n) A ->
                          (Book_2_4_npath n A * Book_2_4_npath n A)
  := fun {n} {A} p => (pr1 p, pr1 (pr2 p)).

(* ================================================== ex:ap-to-apd-equiv-apd-to-ap *)
(** Exercise 2.5 *)

(* Note that "@" is notation for concatentation and ^ is for inversion *)

Definition Book_eq_2_3_6 {A B : Type} {x y : A} (p : x = y) (f : A -> B)
  : (f x = f y) -> (transport (fun _ => B) p (f x) = f y) :=
  fun fx_eq_fy =>
    (HoTT.Basics.PathGroupoids.transport_const p (f x)) @ fx_eq_fy.

Definition Book_eq_2_3_7 {A B : Type} {x y : A} (p : x = y) (f : A -> B)
  : (transport (fun _ => B) p (f x) = f y) -> f x = f y :=
  fun fx_eq_fy =>
    (HoTT.Basics.PathGroupoids.transport_const p (f x))^ @ fx_eq_fy.

(* By induction on p, it suffices to assume that x ≡ y and p ≡ refl, so
   the above equations concatenate identity paths, which are units under
   concatenation.

   [isequiv_adjointify] is one way to prove two functions form an equivalence,
   specifically one proves that they are (category-theoretic) sections of one
   another, that is, each is a right inverse for the other. *)
Definition Equivalence_Book_eq_2_3_6_and_Book_eq_2_3_6
           {A B : Type} {x y : A} (p : x = y) (f : A -> B)
    : IsEquiv (Book_eq_2_3_6 p f).
Proof.
  apply (isequiv_adjointify (Book_eq_2_3_6 p f) (Book_eq_2_3_7 p f));
    unfold Book_eq_2_3_6, Book_eq_2_3_7, transport_const;
    induction p;
    intros y;
    do 2 (rewrite concat_1p);
    reflexivity.
Defined.

(* ================================================== ex:equiv-concat *)
(** Exercise 2.6 *)

(* This exercise is solved in the library as
   HoTT.Types.Paths.isequiv_concat_l
 *)

Definition concat_left {A : Type} {x y : A} (z : A) (p : x = y)
    : (y = z) -> (x = z) :=
  fun q => p @ q.

Definition concat_right {A : Type} {x y : A} (z : A) (p : x = y)
    : (x = z) -> (y = z) :=
  fun q => (inverse p) @ q.

(* Again, by induction on p, it suffices to assume that x ≡ y and p ≡ refl, so
   the above equations concatenate identity paths, which are units under
   concatenation. *)
Definition Book_2_6 {A : Type} {x y z : A} (p : x = y)
  : IsEquiv (concat_left z p).
Proof.
  apply (isequiv_adjointify (concat_left z p) (concat_right z p));
    induction p;
    unfold concat_right, concat_left;
    intros y;
    do 2 (rewrite concat_1p);
    reflexivity.
Defined.

(* ================================================== ex:ap-sigma *)
(** Exercise 2.7 *)

(* Already solved as ap_functor_sigma; there is a copy here for completeness *)

Section Book_2_7.
  Definition Book_2_7 {A B : Type} {P : A -> Type} {Q : B -> Type}
            (f : A -> B) (g : forall a, P a -> Q (f a))
            (u v : sig P) (p : u.1 = v.1) (q : p # u.2 = v.2)
  : ap (functor_sigma f g) (path_sigma P u v p q)
    = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
                (ap f p)
                ((transport_compose Q f p (g u.1 u.2))^
                  @ (@ap_transport _ P (fun x => Q (f x)) _ _ p g u.2)^
                  @ ap (g v.1) q).
  Proof.
    destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
    destruct p; simpl in q.
    destruct q.
    reflexivity.
  Defined.
End Book_2_7.

(* ================================================== ex:ap-coprod *)
(** Exercise 2.8 *)

Definition Book_2_8 := @HoTT.Types.Sum.ap_functor_sum.

(* ================================================== ex:coprod-ump *)
(** Exercise 2.9 *)

(* This exercise is solved in the library as
   HoTT.Types.Sum.equiv_sum_ind
 *)
(* To extract a function on either summand, compose with the injections *)
Definition coprod_ump1 {A B X} : (A + B -> X) -> (A -> X) * (B -> X) :=
  fun f => (f o inl, f o inr).

(* To create a function on the direct sum from functions on the summands, work
   by cases *)
Definition coprod_ump2 {A B X} : (A -> X) * (B -> X) -> (A + B -> X) :=
  prod_ind (fun _ => A + B -> X) (fun f g => sum_ind (fun _ => X) f g).

Definition Book_2_9 {A B X} `{Funext} : (A -> X) * (B -> X) <~> (A + B -> X).
  apply (equiv_adjointify coprod_ump2 coprod_ump1).
Proof.
  - intros f.
    apply path_forall.
    intros [a | b]; reflexivity.
  - intros [f g].
    reflexivity.
Defined.

(* ================================================== ex:sigma-assoc *)
(** Exercise 2.10 *)

(* This exercise is solved in the library as
   HoTT.Types.Sigma.equiv_sigma_assoc
 *)

Section TwoTen.
  Context `{A : Type} {B : A -> Type} {C : (exists a : A, B a) -> Type}.

  Local Definition f210 : (exists a : A, (exists b : B a, (C (a; b)))) ->
                          (exists (p : exists a : A, B a), (C p)) :=
    fun pairpair =>
      match pairpair with (a; pp) =>
        match pp with (b; c) => ((a; b); c) end
      end.

  Local Definition g210 : (exists (p : exists a : A, B a), (C p)) ->
                          (exists a : A, (exists b : B a, (C (a; b)))).
  Proof.
    intros pairpair.
    induction pairpair as [pair c].
    induction pair as [a b].
    exact (a; (b; c)).
  Defined.

  Definition Book_2_10 : (exists a : A, (exists b : B a, (C (a; b)))) <~>
                         (exists (p : exists a : A, B a), (C p)).
  Proof.
    apply (equiv_adjointify f210 g210); compute; reflexivity.
  Defined.
End TwoTen.

(* ================================================== ex:pullback *)
(** Exercise 2.11 *)

(** The definition of commutative squares in HoTT.Limits.Pullback is slightly different, using a homotopy between the composites instead of a path. *)

Definition Book_2_11 `{H : Funext} {X A B C} (f : A -> C) (g : B -> C)
  : (X -> HoTT.Limits.Pullback.Pullback f g)
    <~> HoTT.Limits.Pullback.Pullback (fun h : X -> A => f o h) (fun k : X -> B => g o k)
  := HoTT.Limits.Pullback.equiv_ispullback_commsq f g
    oE (HoTT.Limits.Pullback.equiv_pullback_corec f g)^-1.

(* ================================================== ex:pullback-pasting *)
(** Exercise 2.12 *)

Definition Book_2_12_i := @HoTT.Limits.Pullback.ispullback_pasting_left.

Definition Book_2_12_ii := @HoTT.Limits.Pullback.ispullback_pasting_outer.

(* ================================================== ex:eqvboolbool *)
(** Exercise 2.13 *)

Definition Book_2_13 := @HoTT.Types.Bool.equiv_bool_aut_bool.

(* ================================================== ex:equality-reflection *)
(** Exercise 2.14 *)

(** For any q : x = y, q and refl_x has the same type x = x, so we can form the type Pi_{x,y} Pi_q (q = refl_x). *)
(** A path induction produces an element r, with (r x x p) : p = refl_x, which is also definitional by assumption *)

(* ================================================== ex:strengthen-transport-is-ap *)
(** Exercise 2.15 *)

Definition Book_2_15 {A} (B : A -> Type) {x y : A} (p : x = y)
  : transport B p = HoTT.Types.Universe.equiv_path _ _ (ap B p)
  := match p with 1 => 1 end.

(* ================================================== ex:strong-from-weak-funext *)
(** Exercise 2.16 *)



(* ================================================== ex:equiv-functor-types *)
(** Exercise 2.17 *)



(* ================================================== ex:dep-htpy-natural *)
(** Exercise 2.18 *)



(* ================================================== ex:equiv-functor-set *)
(** Exercise 3.1 *)

Definition Book_3_1_solution_1 {A B} (f : A <~> B) (H : IsHSet A)
  := @HoTT.Basics.Trunc.istrunc_equiv_istrunc A B f 0 H.

(** Alternative solutions: [Book_3_1_solution_2] using UA, and [Book_3_1_solution_3] using two easy lemmas that may be of independent interest *)

Lemma Book_3_1_solution_2 `{Univalence} {A B} : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intro e.
  rewrite (path_universe_uncurried e).
  exact idmap.
Defined.

Lemma retr_f_g_path_in_B {A B} (f : A -> B)  (g : B -> A)
  (alpha : f o g == idmap) (x y : B) (p : x = y)
  :  p = (alpha x)^ @ (ap f (ap g p)) @ (alpha y).
Proof.
  destruct p.
  simpl.
  rewrite concat_p1.
  rewrite concat_Vp.
  exact 1.
Defined.

Lemma retr_f_g_isHSet_A_so_B {A B} (f : A -> B)  (g : B -> A)
      : f o g == idmap -> IsHSet A -> IsHSet B.
Proof.
  intros retr_f_g isHSet_A.
  srapply hset_axiomK. unfold axiomK.
  intros x p.
  assert (ap g p = 1) as g_p_is_1.
  - apply (axiomK_hset isHSet_A).
  - assert (1 = (retr_f_g x) ^ @ (ap f (ap g p)) @ (retr_f_g x)) as rhs_is_1.
    + rewrite g_p_is_1. simpl. rewrite concat_p1. rewrite concat_Vp. exact 1.
    + rewrite (rhs_is_1).
      apply (retr_f_g_path_in_B f g retr_f_g).
Defined.

Lemma Book_3_1_solution_3 {A B} : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intros equivalent_A_B isHSet_A.
  elim equivalent_A_B; intros f isequiv_f.
  elim isequiv_f; intros g retr_f_g sect_f_g coh.
  apply (retr_f_g_isHSet_A_so_B f g); assumption.
Defined.

(* ================================================== ex:isset-coprod *)
(** Exercise 3.2 *)

Definition Book_3_2_solution_1 := @HoTT.Types.Sum.ishset_sum.

(** Alternative solution for replaying *)

Lemma Book_3_2_solution_2 (A B : Type) : IsHSet A -> IsHSet B -> IsHSet (A+B).
Proof.
  intros isHSet_A isHSet_B.
  srapply hset_axiomK. unfold axiomK. intros x p. destruct x.
  - rewrite (inverse (eisretr_path_sum p)).
    rewrite (axiomK_hset isHSet_A a (path_sum_inv p)).
    simpl; exact idpath.
  - rewrite (inverse (eisretr_path_sum p)).
    rewrite (axiomK_hset isHSet_B b (path_sum_inv p)).
    simpl; exact idpath.
Defined.

(* ================================================== ex:isset-sigma *)
(** Exercise 3.3 *)

Definition Book_3_3_solution_1 (A : Type) (B : A -> Type)
   := @HoTT.Types.Sigma.istrunc_sigma A B 0.

(** This exercise is hard because 2-paths over Sigma types are not treated in the first three chapters of the book. Consult theories/Types/Sigma.v *)

Lemma Book_3_3_solution_2 (A : Type) (B : A -> Type) :
  IsHSet A -> (forall x:A, IsHSet (B x)) -> IsHSet { x:A | B x}.
Proof.
  intros isHSet_A allBx_HSet.
  srapply hset_axiomK. intros x xx.
  pose (path_path_sigma B x x xx 1) as useful.
  apply (useful (axiomK_hset _ _ _) (hset_path2 _ _)).
Defined.

(* ================================================== ex:prop-endocontr *)
(** Exercise 3.4 *)

Lemma Book_3_4_solution_1 `{Funext} (A : Type) : IsHProp A <-> Contr (A -> A).
Proof.
  split.
  - intro isHProp_A.
    apply (Build_Contr _ idmap).
    apply path_ishprop. (* automagically, from IsHProp A *)
  - intro contr_AA.
    apply hprop_allpath; intros a1 a2.
    exact (ap10 (path_contr (fun x:A => a1) (fun x:A => a2)) a1).
Defined.

(* ================================================== ex:prop-inhabcontr *)
(** Exercise 3.5 *)

Definition Book_3_5_solution_1 := @HoTT.Universes.HProp.equiv_hprop_inhabited_contr.

(* ================================================== ex:lem-mereprop *)
(** Exercise 3.6 *)

Lemma Book_3_6_solution_1 `{Funext} (A : Type) : IsHProp A -> IsHProp (A + ~A).
Proof.
  intro isHProp_A.
  apply hprop_allpath. intros x y.
  destruct x as [a1|n1]; destruct y as [a2|n2]; apply path_sum; try apply path_ishprop.
  - exact (n2 a1).
  - exact (n1 a2).
Defined.

(* ================================================== ex:disjoint-or *)
(** Exercise 3.7 *)

Lemma Book_3_7_solution_1 (A B: Type) :
  IsHProp A -> IsHProp B -> ~(A*B) -> IsHProp (A+B).
Proof.
  intros isHProp_A isProp_B nab.
  apply hprop_allpath. intros x y.
  destruct x as [a1|b1]; destruct y as [a2|b2]; apply path_sum; try apply path_ishprop.
  - exact (nab (a1,b2)).
  - exact (nab (a2,b1)).
Defined.

(* ================================================== ex:brck-qinv *)
(** Exercise 3.8 *)



(* ================================================== ex:lem-impl-prop-equiv-bool *)
(** Exercise 3.9 *)

Definition LEM := forall (A : Type), IsHProp A -> A + ~A.

Definition LEM_hProp_Bool (lem : LEM) (hprop : HProp) : Bool
  := match (lem hprop _) with inl _ => true | inr _ => false end.

Lemma Book_3_9_solution_1 `{Univalence} : LEM -> HProp <~> Bool.
Proof.
  intro lem.
  apply (equiv_adjointify (LEM_hProp_Bool lem) is_true).
  - intros []; simpl.
    + unfold LEM_hProp_Bool. elim (lem Unit_hp _).
      * exact (fun _ => 1).
      * intro nUnit. elim (nUnit tt).
    + unfold LEM_hProp_Bool. elim (lem False_hp _).
      * intro fals. elim fals.
      * exact (fun _ => 1).
  - intro hprop.
    unfold LEM_hProp_Bool.
    elim (lem hprop _).
    + intro p.
      apply path_hprop; simpl. (* path_prop is silent *)
      exact ((if_hprop_then_equiv_Unit hprop p)^-1)%equiv.
    + intro np.
      apply path_hprop; simpl. (* path_prop is silent *)
      exact ((if_not_hprop_then_equiv_Empty hprop np)^-1)%equiv.
Defined.

(* ================================================== ex:lem-impred *)
(** Exercise 3.10 *)



(* ================================================== ex:not-brck-A-impl-A *)
(** Exercise 3.11 *)

(** This theorem extracts the main idea leading to the contradiction constructed
    in the proof of Theorem 3.2.2, that univalence implies that all functions are
    natural with respect to equivalences.

    The terms are complicated, but it pretty much follows the proof in the book,
    step by step.
 *)
Lemma univalence_func_natural_equiv `{Univalence}
  : forall (C : Type -> Type) (all_contr : forall A, Contr (C A -> C A))
      (g : forall A, C A -> A) {A : Type}  (e : A <~> A),
    e o (g A) = (g A).
Proof.
  intros C all_contr g A e.
  apply path_forall.

  intros x.
  pose (p := path_universe_uncurried e).

  (* The propositional computation rule for univalence of section 2.10 *)
  refine (concat (happly (transport_idmap_path_universe_uncurried e)^ (g A x)) _).

  (** To obtain the situation of 2.9.4, we rewrite x using

<<
        x = transport (fun A : Type => C A) p^ x
>>

      This equality holds because [(C A) -> (C A)] is contractible, so

<<
        transport (fun A : Type => C A) p^ = idmap
>>

      In both Theorem 3.2.2 and the following result, the hypothesis
      [Contr ((C A) -> (C A))] will follow from the contractibility of [(C A)].
   *)
  refine (concat (ap _ (ap _ (happly (@path_contr _ (all_contr A)
                                                  idmap (transport _ p^)) x))) _).

  (* Equation 2.9.4 is called transport_arrow in the library. *)
  refine (concat (@transport_arrow _ (fun A => C A) idmap _ _ p (g A) x)^ _).

  exact (happly (apD g p) x).
Defined.

(** For this proof, we closely follow the proof of Theorem 3.2.2
    from the text, replacing ¬¬A → A by ∥A∥ → A. *)
Lemma Book_3_11 `{Univalence} : ~ (forall A, Trunc (-1) A -> A).
Proof.
  (* The proof is by contradiction. We'll assume we have such a
     function, and obtain an element of 0. *)
  intros g.

  assert (end_contr : forall A, Contr (Trunc (-1) A -> Trunc (-1) A)).
  {
    intros A.
    apply Book_3_4_solution_1.
    apply istrunc_truncation.
  }

  (** There are no fixpoints of the fix-point free autoequivalence of 2 (called
      negb). We will derive a contradiction by showing there must be such a fixpoint
      by naturality of g.

      We parametrize over b to emphasize that this proof depends only on the fact
      that Bool is inhabited, not on any specific value (we use "true" below).
   *)
  pose
    (contr b :=
        (not_fixed_negb (g Bool b))
        (happly (univalence_func_natural_equiv _ end_contr g equiv_negb) b)).

  contradiction (contr (tr true)).
Defined.

(* ================================================== ex:lem-impl-simple-ac *)
(** Exercise 3.12 *)



(* ================================================== ex:naive-lem-impl-ac *)
(** Exercise 3.13 *)

Section Book_3_13.
  Definition naive_LEM_impl_DN_elim (A : Type) (LEM : A + ~A)
  : ~~A -> A
    := fun nna => match LEM with
                    | inl a => a
                    | inr na => match nna na with end
                  end.

  Lemma naive_LEM_implies_AC
  : (forall A : Type, A + ~A)
    -> forall X A P,
         (forall x : X, ~~{ a : A x | P x a })
         -> { g : forall x, A x | forall x, P x (g x) }.
  Proof.
    intros LEM X A P H.
    pose (fun x => @naive_LEM_impl_DN_elim _ (LEM _) (H x)) as H'.
    exists (fun x => (H' x).1).
    exact (fun x => (H' x).2).
  Defined.

  Lemma Book_3_13 `{Funext}
  : (forall A : Type, A + ~A)
    -> forall X A P,
         IsHSet X
         -> (forall x : X, IsHSet (A x))
         -> (forall x (a : A x), IsHProp (P x a))
         -> (forall x, merely { a : A x & P x a })
         -> merely { g : forall x, A x & forall x, P x (g x) }.
  Proof.
    intros LEM X A P HX HA HP H0.
    apply tr.
    apply (naive_LEM_implies_AC LEM).
    intro x.
    specialize (H0 x).
    revert H0.
    apply Trunc_rec.
    exact (fun x nx => nx x).
  Defined.
End Book_3_13.

(* ================================================== ex:lem-brck *)
(** Exercise 3.14 *)

Section Book_3_14.
  Context `{Funext}.
  Hypothesis LEM : forall A : Type, IsHProp A -> A + ~A.

  Definition Book_3_14
  : forall A (P : ~~A -> Type),
    (forall a, P (fun na => na a))
    -> (forall x y (z : P x) (w : P y), transport P (path_ishprop x y) z = w)
    -> forall x, P x.
  Proof.
    intros A P base p nna.
    assert (forall x, IsHProp (P x)).
    - intro x.
      apply hprop_allpath.
      intros x' y'.
      etransitivity; [ symmetry; apply (p x x y' x') | ].
     (* Without this it somehow proves [H'] using the wrong universe for hprop_Empty and fails when we do [Defined].
        See Coq #4862. *)
      set (path := path_ishprop x x).
      assert (H' : idpath = path) by apply path_ishprop.
      destruct H'.
      reflexivity.
    - destruct (LEM (P nna) _) as [pnna|npnna]; trivial.
      refine (match _ : Empty with end).
      apply nna.
      intro a.
      apply npnna.
      exact (transport P (path_ishprop _ _) (base a)).
  Defined.

  Lemma Book_3_14_equiv A : merely A <~> ~~A.
  Proof.
    apply equiv_iff_hprop.
    - apply Trunc_rec.
      exact (fun a na => na a).
    - intro nna.
      apply (@Book_3_14 A (fun _ => merely A)).
      * exact tr.
      * intros x y z w.
        apply path_ishprop.
      * exact nna.
  Defined.
End Book_3_14.

(* ================================================== ex:impred-brck *)
(** Exercise 3.15 *)



(* ================================================== ex:lem-impl-dn-commutes *)
(** Exercise 3.16 *)



(* ================================================== ex:prop-trunc-ind *)
(** Exercise 3.17 *)



(* ================================================== ex:lem-ldn *)
(** Exercise 3.18 *)



(* ================================================== ex:decidable-choice *)
(** Exercise 3.19 *)

Definition Book_3_19 := @HoTT.BoundedSearch.minimal_n.

(* ================================================== ex:omit-contr2 *)
(** Exercise 3.20 *)



(* ================================================== ex:isprop-equiv-equiv-bracket *)
(** Exercise 3.21 *)



(* ================================================== ex:finite-choice *)
(** Exercise 3.22 *)



(* ================================================== ex:decidable-choice-strong *)
(** Exercise 3.23 *)



(* ================================================== ex:n-set *)
(** Exercise 3.24 *)



(* ================================================== ex:two-sided-adjoint-equivalences *)
(** Exercise 4.1 *)



(* ================================================== ex:symmetric-equiv *)
(** Exercise 4.2 *)



(* ================================================== ex:qinv-autohtpy-no-univalence *)
(** Exercise 4.3 *)



(* ================================================== ex:unstable-octahedron *)
(** Exercise 4.4 *)



(* ================================================== ex:2-out-of-6 *)
(** Exercise 4.5 *)

Section Book_4_5.
  Section parts.
    Variables A B C D : Type.
    Variable f : A -> B.
    Variable g : B -> C.
    Variable h : C -> D.
    Context `{IsEquiv _ _ (g o f), IsEquiv _ _ (h o g)}.

    Local Instance Book_4_5_g : IsEquiv g.
    Proof.
      apply isequiv_biinv.
      split.
      - exists ((h o g)^-1 o h).
        exact (eissect (h o g)).
      - exists (f o (g o f)^-1).
        exact (eisretr (g o f)).
    Defined.

    Local Instance Book_4_5_f : IsEquiv f.
    Proof.
      apply (isequiv_homotopic (g^-1 o (g o f))); try exact _.
      intro; apply (eissect g).
    Defined.

    Local Instance Book_4_5_h : IsEquiv h.
    Proof.
      apply (isequiv_homotopic ((h o g) o g^-1)); try exact _.
      intro; apply (ap h); apply (eisretr g).
    Defined.

    Definition Book_4_5_hgf : IsEquiv (h o g o f).
    Proof.
      typeclasses eauto.
    Defined.
  End parts.

  (*Lemma Book_4_5 A B f `{IsEquiv A B f} (a a' : A) : IsEquiv (@ap _ _ f a a').
  Proof.
    pose (@ap _ _ (f^-1) (f a) (f a')) as f'.
    pose (fun p : f^-1 (f a) = _ => p @ (@eissect _ _ f _ a')) as g'.
    pose (fun p : _ = a' => (@eissect _ _ f _ a)^ @ p) as h'.
    pose (g' o f').
    pose (h' o g').
    admit.
  Qed.*)
End Book_4_5.

(* ================================================== ex:qinv-univalence *)
(** Exercise 4.6 *)

Section Book_4_6_i.

  Definition is_qinv {A B : Type} (f : A -> B)
    := { g : B -> A & (f o g == idmap) * (g o f == idmap) }.
  Definition qinv (A B : Type)
    := { f : A -> B & is_qinv f }.
  Definition qinv_id A : qinv A A
    := (fun x => x; (fun x => x ; (fun x => 1, fun x => 1))).
  Definition qinv_path A B : (A = B) -> qinv A B
    := fun p => match p with 1 => qinv_id _ end.
  Definition QInv_Univalence_type := forall (A B : Type@{i}),
      is_qinv (qinv_path A B).
  Definition isequiv_qinv {A B} {f : A -> B}
    : is_qinv f -> IsEquiv f.
  Proof.
    intros [g [s r]].
    exact (isequiv_adjointify f g s r).
  Defined.
  Definition equiv_qinv_path (qua: QInv_Univalence_type) (A B : Type)
    : (A = B) <~> qinv A B
    := Build_Equiv _ _ (qinv_path A B) (isequiv_qinv (qua A B)).

  Definition qinv_isequiv {A B} (f : A -> B) `{IsEquiv _ _ f}
    : qinv A B
    := (f ; (f^-1 ; (eisretr f , eissect f))).

  Context `{qua : QInv_Univalence_type}.

  Theorem qinv_univalence_isequiv_postcompose {A B : Type} {w : A -> B}
          `{H0 : IsEquiv A B w} C : IsEquiv (fun (g:C->A) => w o g).
  Proof.
    unfold QInv_Univalence_type in *.
    pose (w' := qinv_isequiv w).
    refine (isequiv_adjointify
              (fun (g:C->A) => w o g)
              (fun (g:C->B) => w^-1 o g)
              _
              _);
    intros g;
    first [ change ((fun x => w'.1 ( w'.2.1 (g x))) = g)
          | change ((fun x => w'.2.1 ( w'.1 (g x))) = g) ];
    clearbody w'; clear H0 w;
    rewrite <- (@eisretr _ _ (@qinv_path A B) (isequiv_qinv (qua A B)) w');
    generalize ((@equiv_inv _ _ (qinv_path A B) (isequiv_qinv (qua A B))) w');
    intro p; clear w'; destruct p; reflexivity.
  Defined.

  (** Now the rest is basically copied from UnivalenceImpliesFunext, with name changes so as to use the current assumption of qinv-univalence rather than a global assumption of ordinary univalence. *)

  Local Instance isequiv_src_compose A B
  : @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
             (A -> B)
             (fun g => (fst o pr1) o g).
  Proof.
    rapply @qinv_univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (fst o pr1) (fun x => ((x, x); idpath))
              (fun _ => idpath)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  Defined.

  Local Instance isequiv_tgt_compose A B
  : @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
             (A -> B)
             (fun g => (snd o pr1) o g).
  Proof.
    rapply @qinv_univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (snd o pr1) (fun x => ((x, x); idpath))
              (fun _ => idpath)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  Defined.

  Theorem QInv_Univalence_implies_FunextNondep (A B : Type)
  : forall f g : A -> B, f == g -> f = g.
  Proof.
    intros f g p.
    pose (d := fun x : A => exist (fun xy => fst xy = snd xy) (f x, f x) (idpath (f x))).
    pose (e := fun x : A => exist (fun xy => fst xy = snd xy) (f x, g x) (p x)).
    change f with ((snd o pr1) o d).
    change g with ((snd o pr1) o e).
    rapply (ap (fun g => snd o pr1 o g)).
    pose (fun A B x y=> @equiv_inv _ _ _ (@isequiv_ap _ _ _ (@isequiv_src_compose A B) x y)) as H'.
    apply H'.
    reflexivity.
  Defined.

  Definition QInv_Univalence_implies_Funext_type : Funext_type
    := NaiveNondepFunext_implies_Funext QInv_Univalence_implies_FunextNondep.

End Book_4_6_i.

Section EquivFunctorFunextType.
  (* We need a version of [equiv_functor_forall_id] that takes a [Funext_type] rather than a global axiom [Funext].  *)
  Context (fa : Funext_type).

  Definition ft_path_forall {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  @equiv_inv _ _ (@apD10 A P f g) (fa _ _ _ _).

  Local Instance ft_isequiv_functor_forall
        {A B:Type} `{P : A -> Type} `{Q : B -> Type}
          {f : B -> A} {g : forall b:B, P (f b) -> Q b}
        `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
    : IsEquiv (functor_forall f g) | 1000.
  Proof.
    simple refine (isequiv_adjointify
                     (functor_forall f g)
                     (functor_forall
                        (f^-1)
                        (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y
                     )) _ _);
      intros h.
    - abstract (
          apply ft_path_forall; intros b; unfold functor_forall;
          rewrite eisadj;
          rewrite <- transport_compose;
          rewrite ap_transport;
          rewrite eisretr;
          apply apD
        ).
    - abstract (
          apply ft_path_forall; intros a; unfold functor_forall;
          rewrite eissect;
          apply apD
        ).
  Defined.

  Definition ft_equiv_functor_forall
        {A B:Type} `{P : A -> Type} `{Q : B -> Type}
        (f : B -> A) `{IsEquiv B A f}
        (g : forall b:B, P (f b) -> Q b)
        `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : (forall a, P a) <~> (forall b, Q b)
    := Build_Equiv _ _ (functor_forall f g) _.

  Definition ft_equiv_functor_forall_id
        {A:Type} `{P : A -> Type} `{Q : A -> Type}
        (g : forall a, P a <~> Q a)
  : (forall a, P a) <~> (forall a, Q a)
    := ft_equiv_functor_forall (equiv_idmap A) g.

End EquivFunctorFunextType.

(** Using the Kraus-Sattler space of loops rather than the version in the book, since it is simpler and avoids use of propositional truncation. *)
Definition Book_4_6_ii
  (qua1 qua2 : QInv_Univalence_type) (* Two, since we need them at different universe levels. *)
  : ~ IsHProp (forall A : { X : Type & X = X }, A = A).
Proof.
  pose (fa := @QInv_Univalence_implies_Funext_type qua2).
  intros H.
  pose (K := forall (X:Type) (p:X=X), { q : X=X & p @ q = q @ p }).
  assert (e : K <~> forall A : { X : Type & X = X }, A = A).
  { unfold K.
    refine (equiv_sig_ind _ oE _).
    refine (ft_equiv_functor_forall_id fa _); intros X.
    refine (ft_equiv_functor_forall_id fa _); intros p.
    refine (equiv_path_sigma _ _ _ oE _); cbn.
    refine (equiv_functor_sigma_id _); intros q.
    refine ((equiv_concat_l (transport_paths_lr q p)^ p)^-1 oE _).
    refine ((equiv_concat_l (concat_p_pp _ _ _) _)^-1 oE _).
    apply equiv_moveR_Vp. }
  assert (HK := @istrunc_equiv_istrunc _ _ e^-1 (-1)).
  assert (u : forall (X:Type) (p:X=X), p @ 1 = 1 @ p).
  { intros X p; rewrite concat_p1, concat_1p; reflexivity. }
  pose (alpha := (fun X p => (idpath X ; u X p)) : K).
  pose (beta := (fun X p => (p ; 1)) : K).
  pose (isequiv_qinv (qua1 Bool Bool)).
  assert (r := pr1_path (apD10 (apD10 (path_ishprop alpha beta) Bool)
                     ((qinv_path Bool Bool)^-1 (qinv_isequiv equiv_negb)))).
  unfold alpha, beta in r; clear alpha beta.
  apply (ap (qinv_path Bool Bool)) in r.
  rewrite eisretr in r.
  apply pr1_path in r; cbn in r.
  exact (true_ne_false (ap10 r true)).
Defined.

(** Assuming qinv-univalence, every quasi-equivalence automatically satisfies one of the adjoint laws. *)
Definition allqinv_coherent (qua : QInv_Univalence_type)
           (A B : Type) (f : qinv A B)
  : (fun x => ap f.2.1 (fst f.2.2 x)) = (fun x => snd f.2.2 (f.2.1 x)).
Proof.
  (* Every quasi-equivalence is the image of a path, and can therefore be assumed to be the identity equivalence, for which the claim holds immediately. *)
  revert f.
  equiv_intro (equiv_qinv_path qua A B) p.
  destruct p; cbn; reflexivity.
Defined.

(** Qinv-univalence is inconsistent. *)
Definition Book_4_6_iii (qua1 qua2 : QInv_Univalence_type) : Empty.
Proof.
  apply (Book_4_6_ii qua1 qua2).
  nrapply istrunc_succ.
  apply (Build_Contr _ (fun A => 1)); intros u.
  exact (allqinv_coherent qua2 _ _ (idmap; (idmap; (fun A => 1, u)))).
Defined.

(* ================================================== ex:embedding-cancellable *)
(** Exercise 4.7 *)



(* ================================================== ex:cancellable-from-bool *)
(** Exercise 4.8 *)



(* ================================================== ex:funext-from-nondep *)
(** Exercise 4.9 *)



(* ================================================== ex:ind-lst *)
(** Exercise 5.1 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(** Exercise 5.2 *)

Section Book_5_2.
  (** Here is one example of functions which are propositionally equal but not judgmentally equal.  They satisfy the same reucrrence propositionally. *)
  Let ez : Bool := true.
  Let es : nat -> Bool -> Bool := fun _ => idmap.
  Definition Book_5_2_i : nat -> Bool := nat_ind (fun _ => Bool) ez es.
  Definition Book_5_2_ii : nat -> Bool := fun _ => true.
  Fail Definition Book_5_2_not_defn_eq : Book_5_2_i = Book_5_2_ii := idpath.
  Lemma Book_5_2_i_prop_eq : forall n, Book_5_2_i n = Book_5_2_ii n.
  Proof.
    induction n; simpl; trivial.
  Defined.
End Book_5_2.

Section Book_5_2'.
  Local Open Scope nat_scope.
  (** Here's another example where two functions are not (currently) definitionally equal, but satisfy the same reucrrence judgmentally.  This example is a bit less robust; it fails in CoqMT. *)
  Let ez : nat := 1.
  Let es : nat -> nat -> nat := fun _ => S.
  Definition Book_5_2'_i : nat -> nat := fun n => n + 1.
  Definition Book_5_2'_ii : nat -> nat := fun n => 1 + n.
  Fail Definition Book_5_2'_not_defn_eq : Book_5_2'_i = Book_5_2'_ii := idpath.
  Definition Book_5_2'_i_eq_ez : Book_5_2'_i 0 = ez := idpath.
  Definition Book_5_2'_ii_eq_ez : Book_5_2'_ii 0 = ez := idpath.
  Definition Book_5_2'_i_eq_es n : Book_5_2'_i (S n) = es n (Book_5_2'_i n) := idpath.
  Definition Book_5_2'_ii_eq_es n : Book_5_2'_ii (S n) = es n (Book_5_2'_ii n) := idpath.
End Book_5_2'.

(* ================================================== ex:one-function-two-recurrences *)
(** Exercise 5.3 *)

Section Book_5_3.
  Let ez : Bool := true.
  Let es : nat -> Bool -> Bool := fun _ => idmap.
  Let ez' : Bool := true.
  Let es' : nat -> Bool -> Bool := fun _ _ => true.
  Definition Book_5_3 : nat -> Bool := fun _ => true.
  Definition Book_5_3_satisfies_ez : Book_5_3 0 = ez := idpath.
  Definition Book_5_3_satisfies_ez' : Book_5_3 0 = ez' := idpath.
  Definition Book_5_3_satisfies_es n : Book_5_3 (S n) = es n (Book_5_3 n) := idpath.
  Definition Book_5_3_satisfies_es' n : Book_5_3 (S n) = es' n (Book_5_3 n) := idpath.
  Definition Book_5_3_es_ne_es' : ~(es = es')
    := fun H => false_ne_true (ap10 (ap10 H 0) false).
End Book_5_3.

(* ================================================== ex:bool *)
(** Exercise 5.4 *)

Definition Book_5_4 := @HoTT.Types.Bool.equiv_bool_forall_prod.

(* ================================================== ex:ind-nat-not-equiv *)
(** Exercise 5.5 *)

Section Book_5_5.
  Let ind_nat (P : nat -> Type) := fun x => @nat_ind P (fst x) (snd x).

  Lemma Book_5_5 `{fs : Funext} : ~forall P : nat -> Type,
                                     IsEquiv (@ind_nat P).
  Proof.
    intro H.
    specialize (H (fun _ => Bool)).
    pose proof (eissect (@ind_nat (fun _ => Bool)) (true, (fun _ _ => true))) as H1.
    pose proof (eissect (@ind_nat (fun _ => Bool)) (true, (fun _ => idmap))) as H2.
    cut (ind_nat (fun _ : nat => Bool) (true, fun (_ : nat) (_ : Bool) => true)
         = (ind_nat (fun _ : nat => Bool) (true, fun _ : nat => idmap))).
    - intro H'.
      apply true_ne_false.
      exact (ap10 (apD10 (ap snd (H1^ @ ap _ H' @ H2)) 0) false).
    - apply path_forall.
      intro n; induction n; trivial.
      unfold ind_nat in *; simpl in *.
      rewrite <- IHn.
      destruct n; reflexivity.
  Defined.
End Book_5_5.

(* ================================================== ex:no-dep-uniqueness-failure *)
(** Exercise 5.6 *)



(* ================================================== ex:loop *)
(** Exercise 5.7 *)



(* ================================================== ex:loop2 *)
(** Exercise 5.8 *)



(* ================================================== ex:inductive-lawvere *)
(** Exercise 5.9 *)



(* ================================================== ex:ilunit *)
(** Exercise 5.10 *)



(* ================================================== ex:empty-inductive-type *)
(** Exercise 5.11 *)



(* ================================================== ex:Wprop *)
(** Exercise 5.12 *)



(* ================================================== ex:Wbounds *)
(** Exercise 5.13 *)



(* ================================================== ex:Wdec *)
(** Exercise 5.14 *)



(* ================================================== ex:Wbounds-loose *)
(** Exercise 5.15 *)



(* ================================================== ex:Wimpred *)
(** Exercise 5.16 *)



(* ================================================== ex:no-nullary-constructor *)
(** Exercise 5.17 *)



(* ================================================== ex:torus *)
(** Exercise 6.1 *)

Definition Book_6_1_i := @HoTT.Cubical.DPath.dp_concat.
Definition Book_6_1_ii := @HoTT.Cubical.DPath.dp_apD_pp.
(** We don't have the full induction principle for the torus *)
(* Definition Book_6_1_iii := ? *)

(* ================================================== ex:suspS1 *)
(** Exercise 6.2 *)



(* ================================================== ex:torus-s1-times-s1 *)
(** Exercise 6.3 *)

Definition Book_6_3 := @HoTT.Spaces.Torus.TorusEquivCircles.equiv_torus_prod_Circle.

(* ================================================== ex:nspheres *)
(** Exercise 6.4 *)



(* ================================================== ex:susp-spheres-equiv *)
(** Exercise 6.5 *)



(* ================================================== ex:spheres-make-U-not-2-type *)
(** Exercise 6.6 *)



(* ================================================== ex:monoid-eq-prop *)
(** Exercise 6.7 *)



(* ================================================== ex:free-monoid *)
(** Exercise 6.8 *)



(* ================================================== ex:unnatural-endomorphisms *)
(** Exercise 6.9 *)

Section Book_6_9.
  Hypothesis LEM : forall A, IsHProp A -> A + ~A.

  Definition Book_6_9 {ua : Univalence} : forall X, X -> X.
  Proof.
    intro X.
    pose proof (@LEM (Contr { f : X <~> X & ~(forall x, f x = x) }) _) as contrXEquiv.
    destruct contrXEquiv as [C|notC].
    - (** In the case where we have exactly one autoequivalence which is not the identity, use it. *)
      exact ((@center _ C).1).
    - (** In the other case, just use the identity. *)
      exact idmap.
  Defined.

  Lemma bool_map_equiv_not_idmap (f : { f : Bool <~> Bool & ~(forall x, f x = x) })
  : forall b, ~(f.1 b = b).
  Proof.
    intro b.
    intro H''.
    apply f.2.
    intro b'.
    pose proof (eval_bool_isequiv f.1).
    destruct b', b, (f.1 true), (f.1 false);
      simpl in *;
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
  Qed.

  Lemma Book_6_9_not_id {ua : Univalence} `{fs : Funext} : Book_6_9 Bool = negb.
  Proof.
    apply path_forall; intro b.
    unfold Book_6_9.
    destruct (@LEM (Contr { f : Bool <~> Bool & ~(forall x, f x = x) }) _) as [C|H'].
    - set (f := @center _ C).
      pose proof (bool_map_equiv_not_idmap f b).
      destruct (f.1 b), b;
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : ~(_ = _) |- _ ] => exact (match H idpath with end)
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
    - refine (match H' _ with end).
      apply (Build_Contr _ (exist (fun f : Bool <~> Bool =>
                         ~(forall x, f x = x))
                      (Build_Equiv _ _ negb _)
                      (fun H => false_ne_true (H true))));
        simpl.
      intro f.
      apply path_sigma_uncurried; simpl.
      refine ((fun H'' =>
                 (equiv_path_equiv _ _ H'';
                  path_ishprop _ _))
                _);
        simpl.
      apply path_forall; intro b'.
      pose proof (bool_map_equiv_not_idmap f b').
      destruct (f.1 b'), b';
      match goal with
        | _ => assumption
        | _ => reflexivity
        | [ H : ~(_ = _) |- _ ] => exact (match H idpath with end)
        | [ H : true = false |- _ ] => exact (match true_ne_false H with end)
        | [ H : false = true |- _ ] => exact (match false_ne_true H with end)
      end.
  Qed.

(** Simpler solution not using univalence **)

  Definition AllExistsOther(X : Type) := forall x:X, { y:X | y <> x }.

  Definition centerAllExOthBool : AllExistsOther Bool :=
    fun (b:Bool) => (negb b ; not_fixed_negb b).

  Lemma centralAllExOthBool `{Funext} (f: AllExistsOther Bool) : centerAllExOthBool = f.
  Proof. apply path_forall. intro b. pose proof (inverse (negb_ne (f b).2)) as fst.
  unfold centerAllExOthBool.
  apply (@path_sigma _ _ (negb b; not_fixed_negb b) (f b) fst); simpl.
  apply equiv_hprop_allpath. apply istrunc_forall.
  Defined.

  Definition contrAllExOthBool `{Funext} : Contr (AllExistsOther Bool) :=
  (Build_Contr _ centerAllExOthBool centralAllExOthBool).

  Definition solution_6_9 `{Funext} : forall X, X -> X.
  Proof.
    intro X.
    elim (@LEM (Contr (AllExistsOther X)) _); intro.
    - exact (fun x:X => (center (AllExistsOther X) x).1).
    - exact (fun x:X => x).
  Defined.

  Lemma not_id_on_Bool `{Funext} : solution_6_9 Bool <> idmap.
  Proof.
    intro Bad. pose proof ((happly Bad) true) as Ugly.
    assert ((solution_6_9 Bool true) = false) as Good.
    - unfold solution_6_9.
      destruct (LEM (Contr (AllExistsOther Bool)) _) as [C|C];simpl.
      + elim (centralAllExOthBool (@center _ C)). reflexivity.
      + elim (C contrAllExOthBool).
    - apply false_ne_true. rewrite (inverse Good). assumption.
  Defined.

End Book_6_9.

(* ================================================== ex:funext-from-interval *)
(** Exercise 6.10 *)



(* ================================================== ex:susp-lump *)
(** Exercise 6.11 *)



(* ================================================== ex:alt-integers *)
(** Exercise 6.12 *)



(* ================================================== ex:trunc-bool-interval *)
(** Exercise 6.13 *)



(* ================================================== ex:all-types-sets *)
(** Exercise 7.1 *)

Section Book_7_1.
  Lemma Book_7_1_part_i (H : forall A, merely A -> A) A : IsHSet A.
  Proof.
    apply (@HoTT.Universes.HSet.ishset_hrel_subpaths
             A (fun x y => merely (x = y)));
    try typeclasses eauto.
    - intros ?.
      apply tr.
      reflexivity.
    - intros.
      apply H.
      assumption.
  Defined.

  Lemma Book_7_1_part_ii (H : forall A B (f : A -> B),
                                (forall b, merely (hfiber f b))
                                -> forall b, hfiber f b)
  : forall A, IsHSet A.
  Proof.
    apply Book_7_1_part_i.
    intros A a.
    apply (fun H' => (@H A (merely A) tr H' a).1).
    clear a.
    apply Trunc_ind; try exact _.
    intro x; compute; apply tr.
    exists x; reflexivity.
  Defined.
End Book_7_1.

(* ================================================== ex:s2-colim-unit *)
(** Exercise 7.2 *)



(* ================================================== ex:ntypes-closed-under-wtypes *)
(** Exercise 7.3 *)



(* ================================================== ex:connected-pointed-all-section-retraction *)
(** Exercise 7.4 *)



(* ================================================== ex:ntype-from-nconn-const *)
(** Exercise 7.5 *)



(* ================================================== ex:connectivity-inductively *)
(** Exercise 7.6 *)



(* ================================================== ex:lemnm *)
(** Exercise 7.7 *)



(* ================================================== ex:acnm *)
(** Exercise 7.8 *)



(* ================================================== ex:acnm-surjset *)
(** Exercise 7.9 *)

(** Solution for the case (oo,-1). *)
Definition Book_7_9_oo_neg1 `{Univalence} (AC_oo_neg1 : forall X : HSet, HasChoice X) (A : Type)
  : merely (exists X : HSet, exists p : X -> A, IsSurjection p)
  := @HoTT.Projective.projective_cover_AC AC_oo_neg1 _ A.

(* ================================================== ex:acconn *)
(** Exercise 7.10 *)



(* ================================================== ex:n-truncation-not-left-exact *)
(** Exercise 7.11 *)



(* ================================================== ex:double-negation-modality *)
(** Exercise 7.12 *)

Definition Book_7_12 := @HoTT.Modalities.Notnot.NotNot.

(* ================================================== ex:prop-modalities *)
(** Exercise 7.13 *)

Definition Book_7_13_part_i := @HoTT.Modalities.Open.Op.
Definition Book_7_13_part_ii := @HoTT.Modalities.Closed.Cl.

(* ================================================== ex:f-local-type *)
(** Exercise 7.14 *)



(* ================================================== ex:trunc-spokes-no-hub *)
(** Exercise 7.15 *)



(* ================================================== ex:s2-colim-unit-2 *)
(** Exercise 7.16 *)



(* ================================================== ex:fiber-map-not-conn *)
(** Exercise 7.17 *)



(* ================================================== ex:is-conn-trunc-functor *)
(** Exercise 7.18 *)



(* ================================================== ex:categorical-connectedness *)
(** Exercise 7.19 *)



(* ================================================== ex:homotopy-groups-resp-prod *)
(** Exercise 8.1 *)



(* ================================================== ex:decidable-equality-susp *)
(** Exercise 8.2 *)



(* ================================================== ex:contr-infinity-sphere-colim *)
(** Exercise 8.3 *)



(* ================================================== ex:contr-infinity-sphere-susp *)
(** Exercise 8.4 *)



(* ================================================== ex:unique-fiber *)
(** Exercise 8.5 *)



(* ================================================== ex:ap-path-inversion *)
(** Exercise 8.6 *)



(* ================================================== ex:pointed-equivalences *)
(** Exercise 8.7 *)



(* ================================================== ex:HopfJr *)
(** Exercise 8.8 *)



(* ================================================== ex:SuperHopf *)
(** Exercise 8.9 *)



(* ================================================== ex:vksusppt *)
(** Exercise 8.10 *)



(* ================================================== ex:vksuspnopt *)
(** Exercise 8.11 *)



(* ================================================== ex:slice-precategory *)
(** Exercise 9.1 *)



(* ================================================== ex:set-slice-over-equiv-functor-category *)
(** Exercise 9.2 *)



(* ================================================== ex:functor-equiv-right-adjoint *)
(** Exercise 9.3 *)



(* ================================================== ct:pre2cat *)
(** Exercise 9.4 *)



(* ================================================== ct:2cat *)
(** Exercise 9.5 *)



(* ================================================== ct:groupoids *)
(** Exercise 9.6 *)



(* ================================================== ex:2strict-cat *)
(** Exercise 9.7 *)



(* ================================================== ex:pre2dagger-cat *)
(** Exercise 9.8 *)



(* ================================================== ct:ex:hocat *)
(** Exercise 9.9 *)



(* ================================================== ex:dagger-rezk *)
(** Exercise 9.10 *)



(* ================================================== ex:rezk-vankampen *)
(** Exercise 9.11 *)



(* ================================================== ex:stack *)
(** Exercise 9.12 *)



(* ================================================== ex:utype-ct *)
(** Exercise 10.1 *)



(* ================================================== ex:surjections-have-sections-impl-ac *)
(** Exercise 10.2 *)



(* ================================================== ex:well-pointed *)
(** Exercise 10.3 *)



(* ================================================== ex:add-ordinals *)
(** Exercise 10.4 *)



(* ================================================== ex:multiply-ordinals *)
(** Exercise 10.5 *)



(* ================================================== ex:algebraic-ordinals *)
(** Exercise 10.6 *)



(* ================================================== ex:prop-ord *)
(** Exercise 10.7 *)



(* ================================================== ex:ninf-ord *)
(** Exercise 10.8 *)



(* ================================================== ex:well-founded-extensional-simulation *)
(** Exercise 10.9 *)



(* ================================================== ex:choice-function *)
(** Exercise 10.10 *)



(* ================================================== ex:cumhierhit *)
(** Exercise 10.11 *)



(* ================================================== ex:strong-collection *)
(** Exercise 10.12 *)



(* ================================================== ex:choice-cumulative-hierarchy-choice *)
(** Exercise 10.13 *)



(* ================================================== ex:plump-ordinals *)
(** Exercise 10.14 *)



(* ================================================== ex:not-plump *)
(** Exercise 10.15 *)



(* ================================================== ex:plump-successor *)
(** Exercise 10.16 *)



(* ================================================== ex:ZF-algebras *)
(** Exercise 10.17 *)



(* ================================================== ex:monos-are-split-monos-iff-LEM-holds *)
(** Exercise 10.18 *)



(* ================================================== ex:alt-dedekind-reals *)
(** Exercise 11.1 *)



(* ================================================== ex:RD-extended-reals *)
(** Exercise 11.2 *)



(* ================================================== ex:RD-lower-cuts *)
(** Exercise 11.3 *)



(* ================================================== ex:RD-interval-arithmetic *)
(** Exercise 11.4 *)



(* ================================================== ex:RD-lt-vs-le *)
(** Exercise 11.5 *)



(* ================================================== ex:reals-non-constant-into-Z *)
(** Exercise 11.6 *)



(* ================================================== ex:traditional-archimedean *)
(** Exercise 11.7 *)



(* ================================================== RC-Lipschitz-on-interval *)
(** Exercise 11.8 *)



(* ================================================== ex:metric-completion *)
(** Exercise 11.9 *)



(* ================================================== ex:reals-apart-neq-MP *)
(** Exercise 11.10 *)



(* ================================================== ex:reals-apart-zero-divisors *)
(** Exercise 11.11 *)



(* ================================================== ex:finite-cover-lebesgue-number *)
(** Exercise 11.12 *)



(* ================================================== ex:mean-value-theorem *)
(** Exercise 11.13 *)



(* ================================================== ex:knuth-surreal-check *)
(** Exercise 11.14 *)



(* ================================================== ex:reals-into-surreals *)
(** Exercise 11.15 *)



(* ================================================== ex:ord-into-surreals *)
(** Exercise 11.16 *)



(* ================================================== ex:hiit-plump *)
(** Exercise 11.17 *)



(* ================================================== ex:pseudo-ordinals *)
(** Exercise 11.18 *)



(* ================================================== ex:double-No-recursion *)
(** Exercise 11.19 *)



