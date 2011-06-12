Add LoadPath "..".
Require Import Homotopy.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** The definition of [is_inhab], the (-1)-truncation.  Here is what
   it would look like if Coq supported higher inductive types natively:

   Inductive is_inhab (A : Type) : Type :=
   | inhab : A -> is_inhab A
   | inhab_path : forall (x y: is_inhab A), x ~~> y
*)

Axiom is_inhab : forall (A : Type), Type.

Axiom inhab : forall {A : Type}, A -> is_inhab A.

Axiom inhab_path : forall {A : Type} (x y : is_inhab A), x ~~> y.

Axiom is_inhab_rect : forall {A : Type} {P : is_inhab A -> Type}
  (dinhab : forall (a : A), P (inhab a))
  (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z ~~> w),
  forall (x : is_inhab A), P x.

Axiom is_inhab_compute_inhab : forall {A : Type} {P : is_inhab A -> Type}
  (dinhab : forall (a : A), P (inhab a))
  (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z ~~> w),
  forall (a : A), is_inhab_rect dinhab dpath (inhab a) ~~> dinhab a.

Axiom is_inhab_compute_path : forall {A : Type} {P : is_inhab A -> Type}
  (dinhab : forall (a : A), P (inhab a))
  (dpath : forall (x y : is_inhab A) (z : P x) (w : P y), transport (inhab_path x y) z ~~> w),
  forall (x y : is_inhab A),
    map_dep (is_inhab_rect dinhab dpath) (inhab_path x y)
    ~~> dpath x y (is_inhab_rect dinhab dpath x) (is_inhab_rect dinhab dpath y).

(** The non-dependent version of the eliminator. *)

Definition is_inhab_rect_nondep {A B : Type} :
  (A -> B) -> (forall (z w : B), z ~~> w) -> (is_inhab A -> B).
Proof.
  intros A B dinhab' dpath'.
  apply is_inhab_rect.
  assumption.
  intros x y z w.
  apply @concat with (y := z).
  apply trans_trivial.
  apply dpath'.
Defined.

Definition is_inhab_compute_inhab_nondep {A B : Type}
  (dinhab' : A -> B) (dpath' : forall (z w : B), z ~~> w) (a : A) :
  is_inhab_rect_nondep dinhab' dpath' (inhab a) ~~> (dinhab' a).
Proof.
  intros A B dinhab' dpath' a.
  apply @is_inhab_compute_inhab with (P := fun a => B).
Defined.

Definition is_inhab_compute_path_nondep {A B : Type}
  (dinhab' : A -> B) (dpath' : forall (z w : B), z ~~> w)
  (x y : is_inhab A) :
  map (is_inhab_rect_nondep dinhab' dpath') (inhab_path x y)
  ~~> dpath' (is_inhab_rect_nondep dinhab' dpath' x) (is_inhab_rect_nondep dinhab' dpath' y).
Proof.
  intros A B dinhab' dpath' x y.
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
  intros A.
  apply allpath_prop.
  apply inhab_path.
Defined.

(** And if [A] was already a proposition, then [is_inhab A] is equivalent to [A]. *)

Theorem prop_inhab_is_equiv (A : Type) :
  is_prop A -> is_equiv (@inhab A).
Proof.
  intros A.
  intros H.
  eapply @hequiv_is_equiv.
  instantiate (1 := is_inhab_rect_nondep (idmap A) (prop_path H)).
  unfold is_inhab_rect_nondep.
  apply is_inhab_rect.
  intro a.
  apply map.
  apply @is_inhab_compute_inhab with (P := fun a => A).
  intros x y z w.
  apply contr_path2.
  apply prop_inhabited_contr.
  apply is_inhab_is_prop.
  assumption.
  intro x.
  apply is_inhab_compute_inhab_nondep.
Defined.

(** Inhabited propositions are contractible. *)

Lemma inhab_prop_contr (A : Type) :
  is_prop A -> is_inhab A -> is_contr A.
Proof.
  intros A prp.
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
  intros X Y f epi mono y.
  apply inhab_prop_contr. 
  apply mono. apply epi.
Defined.
