Require Export Paths Fibrations.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** A space [A] is contractible if there is a point [x : A] and a
   (pointwise) homotopy connecting the identity on [A] to the constant
   map at [x].  Thus an element of [is_contr A] is a pair whose
   first component is a point [x] and the second component is a
   pointwise retraction of [A] to [x]. *)

Definition is_contr A := {x : A & forall y : A, y == x}.

(** If a space is contractible, then any two points in it are
   connected by a path in a canonical way. *)

Lemma contr_path {A} (x y : A) : (is_contr A) -> (x == y).
Proof.
  intros A x y.
  intro H.
  destruct H as (z,p).
  path_via z.
Defined.

(** Similarly, any two parallel paths in a contractible space are homotopic.  *)

Lemma contr_path2 {A} {x y : A} (p q : x == y) : (is_contr A) -> (p == q).
Proof.
  intros X x y p q.
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

Lemma contr_pathcontr {A} (x y : A) : is_contr A -> is_contr (x == y).
Proof.
  intros A x y.
  intro ctr.
  exists (contr_path x y ctr).
  intro p.
  apply contr_path2.
  assumption.
Defined.

(** The total space of any based path space is contractible. *)

Lemma pathspace_contr {X} (x:X) : is_contr (sigT (paths x)).
Proof.
  intros X x.
  exists (x ; idpath x).
  intros [y p].
  path_induction.
Defined.

Lemma pathspace_contr' {X} (x:X) : is_contr { y:X  &  x == y }.
Proof.
  intros X x.
  exists (existT (fun y => x == y) x (idpath x)).
  intros [y p].
  path_induction.
Defined.

Lemma pathspace_contr_opp {X} (x:X) : is_contr { y:X & y == x }.
Proof.
  intros X x.
  exists (existT (fun y => y == x) x (idpath x)).
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
