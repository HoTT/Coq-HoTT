(** We fix a particular type universe to be used where Coq's universe
   algorithms fail. For example, in the proof that univalence implies
   function extensionality. *)

Definition Universe := Type.

(** NB: [Type] is not a type. It represents the whole type hierachy
   [Prop < Set < Type(0) < Type(1) < ...] and Coq just picks the
   lowest available level in the hierachy. To see which one was
   picked, do [Set Printing Universes.] and [Print Universe.].
*)

(* The identity map and composition. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

(** printing o $\circ$ *)

Notation "g 'o' f" := (compose g f) (left associativity, at level 37).
