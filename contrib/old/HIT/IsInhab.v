Add LoadPath "..".
Require Import Homotopy.

(** The definition of [is_inhab], the (-1)-truncation.  Here is what
   it would look like if Coq supported higher inductive types natively:

   Inductive is_inhab (A : Type) : Type :=
   | inhab : A -> is_inhab A
   | inhab_path : forall (x y: is_inhab A), x == y

   Instead we have to assume axioms that amount ot the same thing.
*)

Axiom is_inhab : forall (A : Type), Type.

Axiom inhab : forall {A : Type}, A -> is_inhab A.

Axiom inhab_path : forall {A : Type} (x y : is_inhab A), x == y.

(** By adding the following [Hint Resolve] we can simply use the [auto] tactic
   to resolve any path involving [is_inhab]. *)
Hint Resolve @inhab_path.

Axiom is_inhab_rect :
  forall
    {A : Type} {P : is_inhab A -> Type}
    (dinhab : forall a : A, P (inhab a))
    (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z == w)
    (x : is_inhab A), P x.

Axiom is_inhab_compute_inhab : forall {A : Type} {P : is_inhab A -> Type}
  (dinhab : forall (a : A), P (inhab a))
  (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z == w),
  forall (a : A), is_inhab_rect dinhab dpath (inhab a) == dinhab a.

Axiom is_inhab_compute_path : forall {A : Type} {P : is_inhab A -> Type}
  (dinhab : forall (a : A), P (inhab a))
  (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z == w),
  forall (x y : is_inhab A),
    map_dep (is_inhab_rect dinhab dpath) (inhab_path x y)
    == dpath x y (is_inhab_rect dinhab dpath x) (is_inhab_rect dinhab dpath y).

(** The non-dependent version of the eliminator. *)

Definition is_inhab_rect_nondep {A B : Type} :
  (A -> B) -> (forall (z w : B), z == w) -> (is_inhab A -> B).
Proof.
  intros dinhab' dpath'.
  apply is_inhab_rect.
  assumption.
  intros x y z w.
  apply @concat with (y := z).
  apply trans_trivial.
  apply dpath'.
Defined.

Definition is_inhab_compute_inhab_nondep {A B : Type}
  (dinhab' : A -> B) (dpath' : forall (z w : B), z == w) (a : A) :
  is_inhab_rect_nondep dinhab' dpath' (inhab a) == (dinhab' a).
Proof.
  apply @is_inhab_compute_inhab with (P := fun a => B).
Defined.

Definition is_inhab_compute_path_nondep {A B : Type}
  (dinhab' : A -> B) (dpath' : forall (z w : B), z == w)
  (x y : is_inhab A) :
  map (is_inhab_rect_nondep dinhab' dpath') (inhab_path x y)
  == dpath' (is_inhab_rect_nondep dinhab' dpath' x) (is_inhab_rect_nondep dinhab' dpath' y).
Proof.
  (* Here is a "cheating" proof which just uses the assumption that [B] is a prop:
       apply contr_path, allpath_prop; assumption.
     And here is the "real" proof which uses [is_inhab_compute_path]. *)
  unfold is_inhab_rect_nondep.
  path_via (!trans_trivial (inhab_path x y) _ @
    map_dep (is_inhab_rect (P := fun a => B) dinhab'
    (fun (x0 y0 : is_inhab A) (z w : B) => trans_trivial (inhab_path x0 y0) z @ dpath' z w))
  (inhab_path x y)).
  moveleft_onleft.
  apply opposite, map_dep_trivial.
  moveright_onleft.
  apply @is_inhab_compute_path with
    (P := fun a => B)
    (dpath := fun (x y : is_inhab A) (z w : B) => trans_trivial (inhab_path x y) z @ dpath' z w)    .
Defined.

(** [is_inhab A] is always a proposition. *)

Theorem is_inhab_is_prop (A : Type) : is_prop (is_inhab A).
Proof.
  apply allpath_prop.
  apply inhab_path.
Defined.

(** And if [A] was already a proposition, then [is_inhab A] is equivalent to [A]. *)

Theorem prop_inhab_is_equiv (A : Type) :
  is_prop A -> is_equiv (@inhab A).
Proof.
  intros H.
  apply @hequiv_is_equiv with (g := is_inhab_rect_nondep (idmap A) (prop_path H)).
  auto.
  intro a.
  apply @is_inhab_compute_inhab with (P := fun _ => A).
Defined.

(** Inhabited propositions are contractible. *)

Lemma inhab_prop_contr (A : Type) :
  is_prop A -> is_inhab A -> is_contr A.
Proof.
  intros prp.
  apply is_inhab_rect_nondep.
  apply prop_inhabited_contr; now assumption.
  intros; apply contr_path.
  apply contr_contr; now assumption.
Defined.

(** "Epi" and "mono" implies equivalence. *)

Definition is_epi {X Y : Type} (f : X -> Y) :=
  forall y:Y, is_inhab (hfiber f y).

Definition is_mono {X Y : Type} (f : X -> Y) :=
  forall y:Y, is_prop (hfiber f y).

Lemma epi_mono_equiv {X Y : Type} (f : X -> Y) :
  is_epi f -> is_mono f -> is_equiv f.
Proof.
  intros epi mono y.
  apply inhab_prop_contr. 
  apply mono. apply epi.
Defined.

Section IsInhabMonad.

(** The monadic structure of [is_inhab]. This is pretty easy to check since any
   diagram involving propositions commutes. *)

(** We first need the action of [is_inhab] on morphisms. *)
Definition is_inhab_map {A B : Type} : (A -> B) -> (is_inhab A -> is_inhab B).
Proof.
  intros f p.
  apply @is_inhab_rect_nondep with (A := A); auto.
  intro x.
  apply (inhab (f x)).
Defined.
  
(** Functoriality of [is_inhab_map]. *)
Lemma is_inhab_map_id {A : Type} :
  forall (p : is_inhab A), is_inhab_map (fun x => x) p == p.
Proof.
  auto.
Defined.

Lemma is_inhab_map_compose {A B C : Type} (f : A -> B) (g : B -> C):
  forall (p : is_inhab A), is_inhab_map (compose g f) p == is_inhab_map g (is_inhab_map f p).
Proof.
  auto.
Defined.

(** The unit. *)
Definition eta := @inhab.

  (** Naturality of unit. *)
Lemma eta_natural {A B : Type} (f : A -> B) :
  forall a : A, eta B (f a) == is_inhab_map f (eta A a).
Proof.
  auto.
Defined.

  (** The multiplication. *)
Definition mu (A : Type) : is_inhab (is_inhab A) -> is_inhab A.
Proof.
  intros p.
  apply @is_inhab_rect_nondep with (A := is_inhab A); auto.
Defined.

  (** Naturality of multiplication. *)
Lemma mu_natural {A B : Type} (f : A -> B) :
  forall p : is_inhab (is_inhab A),
    mu B (is_inhab_map (is_inhab_map f) p) == is_inhab_map f (mu A p).
Proof.
  auto.
Qed.

  (** Unit laws. *)
Lemma eta_1 (A : Type) :
  forall p : is_inhab A, mu A (eta (is_inhab A) p) == p.
Proof.
  auto.
Qed.

Lemma eta_2 (A : Type) :
  forall p : is_inhab A, mu A (is_inhab_map (eta A) p) == p.
Proof.
  auto.
Qed.

Lemma mu_1 (A : Type) :
  forall p : is_inhab (is_inhab (is_inhab A)),
    mu A (is_inhab_map (mu A) p) == mu A (mu (is_inhab A) p).
Proof.
  auto.
Qed.

  (* The strength. *)
Lemma t (A B : Type) : A * is_inhab B -> is_inhab (A * B).
Proof.
  intros [a q].
  apply (is_inhab_rect_nondep (A := B)); auto.
  intro b.
  apply inhab; auto.
Defined.

  (* Naturality of strength. *)
Lemma t_natural (A A' B B' : Type) (f : A -> A') (g : B -> B') :
  forall (a : A) (q : is_inhab B),
    is_inhab_map (fun xy => (f (fst xy), g (snd xy))) (t A B (a,q)) == t A' B' (f a, is_inhab_map g q).
Proof.
  auto.
Qed.

(* The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad *)

Lemma strength_unit (A : Type) :
  forall p : unit * is_inhab A,
    is_inhab_map (@snd unit A) (t unit A p) == snd p.
Proof.
  auto.
Qed.

Lemma strength_eta (A B : Type) :
  forall (a : A) (b : B),
    t A B (a, eta B b) == eta (A * B) (a,b).
Proof.
  auto.
Qed.

Definition alpha A B C (u : (A * B) * C) := (fst (fst u), (snd (fst u), snd u)).

Lemma strength_pentagon_1 (A B C : Type) :
  forall (a : A) (b : B) (r : is_inhab C),
    is_inhab_map (alpha A B C) (t (A * B) C ((a,b),r)) ==
    t A (B * C) (a, t B C (b, r)).
Proof.
  auto.
Qed.

Lemma strength_pentagon_2 (A B : Type) :
  forall (a : A) (p : is_inhab (is_inhab B)),
    mu (A * B) (is_inhab_map (t A B) (t A (is_inhab B) (a, p))) == t A B (a, mu B p).
Proof.
  auto.
Qed.

End IsInhabMonad.
