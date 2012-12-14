Require Import Paths.

Import PathNotations.
Local Open Scope path_scope.

(** A space [A] is contractible if there is a point [x : A] and a
   (pointwise) homotopy connecting the identity on [A] to the constant
   map at [x].  Thus an element of [is_contr A] is a pair whose
   first component is a point [x] and the second component is a
   pointwise retraction of [A] to [x]. *)

Record is_contr A := IsContr {
  center : A ;
  _ : (forall y : A, center = y)
}.

Arguments IsContr {A} _ _.
Arguments center {A} i.


(** We shall use the canonical structure mechanism to automagically derive
    contractibility of types. First we set up the notation which allows us
    to name the center of a contractible type easily. *)

Inductive phantom T (p : T) := Phantom.

Definition center_of A {c : is_contr A} {pht : phantom Type A} := 
  center c.

Canonical Structure unit_is_contr :=
  IsContr tt (fun t : unit => match t with tt => 1 end).

Definition pair_path {A B : Type} {x y : A} {x' y' : B} (p : x = y) (p' : x' = y') :
  (x, x') = (y, y')
  :=
  match p with identity_refl =>
    match p' with identity_refl => 1 end
  end.

Canonical Structure prod_is_contr {A B : Type} (Ac : is_contr A) (Bc : is_contr B) : is_contr (prod A B).
Proof.
  exists (center Ac, center Bc).
  intros [a b].
  apply pair_path.




Notation "[ 'center' 'of' T ]" := (@inhab_clone T _ _ idfun id)
  (at level 0, format "[ 'inhabType'  'of'  T ]") : form_scope.


(** If a space is contractible, then any two points in it are
   connected by a path in a canonical way. *)

Lemma contr_path {A} (x y : A) : (is_contr A) -> (x = y).
Proof.
  intro H.
  destruct H as (z,p).
  path_via z.
Defined.

(** Similarly, any two parallel paths in a contractible space are homotopic.  *)

Lemma contr_path2 {A} {x y : A} (p q : x = y) : (is_contr A) -> (p = q).
Proof.
  intro ctr.
  destruct ctr as (c, ret).
  path_via (ret x @ !ret y).
  moveleft_onright.
  moveright_onleft.
  apply opposite.
  exact (! trans_is_concat_opp p (ret x)  @  map_dep ret p ).
  moveright_onright.
  moveleft_onleft.
  exact (! trans_is_concat_opp q (ret x)  @  map_dep ret q).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)

Lemma contr_pathcontr {A} (x y : A) : is_contr A -> is_contr (x = y).
Proof.
  intro ctr.
  exists (contr_path x y ctr).
  intro p.
  apply contr_path2.
  assumption.
Defined.

(** The total space of any based path space is contractible. *)

Lemma pathspace_contr {X} (x:X) : is_contr (sigT (paths x)).
Proof.
  exists (x ; idpath x).
  intros [y p].
  path_induction.
Defined.

Lemma pathspace_contr' {X} (x:X) : is_contr { y:X  &  x = y }.
Proof.
  exists (existT (fun y => x = y) x (idpath x)).
  intros [y p].
  path_induction.
Defined.

Lemma pathspace_contr_opp {X} (x:X) : is_contr { y:X & y = x }.
Proof.
  exists (existT (fun y => y = x) x (idpath x)).
  intros [y p].
  path_induction.
Defined.

(** The unit type is contractible. *)

Lemma unit_contr : is_contr unit.
Proof.
  exists tt.
  intro y.
  induction y.
  auto.
Defined.

Hint Resolve unit_contr.
