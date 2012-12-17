Require Import Common Paths.

Import PathNotations.
Local Open Scope path_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".
   A theorem about a space [X] being contractible is called [contr_X]. *)

(** A space [A] is contractible if there is a point [x : A] and a
   (pointwise) homotopy connecting the identity on [A] to the constant
   map at [x].  Thus an element of [is_contr A] is a pair whose
   first component is a point [x] and the second component is a
   pointwise retraction of [A] to [x]. *)

Record Contr := BuildContr {
  contr_carrier :> Type ;
  contr_center : contr_carrier ;
  _ : (forall y : contr_carrier, contr_center = y)
}.

Arguments contr_center : simpl never.

Definition contr {A : Contr} : forall a : A, contr_center A = a.
Proof.
  destruct A as [A ? c].
  exact c.
Defined.

(** A trick which allows us to write [[center of A]] where [A] is a
   type for which a canonical structure of [Contr] exists. *)
Definition contr_center_of (A : Contr) (phA : robin A) := contr_center A.

Notation "[ 'center' 'of' T ]" := (contr_center_of _ (Robin T)).

(** We shall use the canonical structure mechanism to automagically derive
    contractibility of types. First we set up the notation which allows us
    to name the center of a contractible type easily. *)

Canonical Structure unit_contr :=
  BuildContr unit tt (fun t : unit => match t with tt => 1 end).

(** XXX: This belongs somewhere else. *)
Definition pair_path {A B : Type} {x y : A} {x' y' : B} (p : x = y) (p' : x' = y') :
  (x, x') = (y, y')
  :=
  match p with identity_refl =>
    match p' with identity_refl => 1 end
  end.

Definition prod_contr (A : Contr) (B : Contr) : Contr :=
  BuildContr
  (prod A B)
  (contr_center A, contr_center B)
  (fun y : prod A B =>
    let (a, b) as p return ((contr_center A, contr_center B) = p) := y in
      pair_path (contr a) (contr b)).

Canonical Structure prod_contr.

(** If a space is contractible, then any two points in it are
   connected by a path in a canonical way. *)
Definition contr_path {A : Contr} (x y : A) :
  x = y
  :=
  (contr x)^-1 @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic,
   which is just the principle UIP. *)
Definition contr_UIP (A : Contr) : UIP A.
Proof.
  intros x y p q.
  assert (H : forall (r : x = y), r = contr_path x y).
    intro r; destruct r; apply inverse; now apply concat_Vp.
  path_via (contr_path x y).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
Canonical Structure contr_identity {A : Contr} (x y : A) :=
  BuildContr
  (x = y)
  ((contr x)^-1 @ contr y)
  (contr_UIP A x y ((contr x)^-1 @ contr y)).

(** The total space of any based path space is contractible. *)
Definition contr_sigT_identity {X : Type} (x : X) : Contr.
Proof.
  exists {y : X & x = y} (x ; 1).
  intros [y p].
  destruct p.
  reflexivity.
Defined.

Canonical Structure contr_sigT_identity.

Definition sigT_identity' {X : Type} (x : X) := {y : X & y = x}.

Definition contr_sigT_identity' {X : Type} (x : X) : Contr.
Proof.
  exists (sigT_identity' x) (existT (fun y => y = x) x 1).
  intros [y p].
  destruct p.
  reflexivity.
Defined.
