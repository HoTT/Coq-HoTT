Require Export Paths Fibrations Contractible Equivalences.

(** Any two contractible types are equivalent. *)

Definition contr_contr_equiv {A B} (f : A -> B) :
  is_contr A -> is_contr B -> is_equiv f.
Proof.
  intros Acontr Bcontr.
  apply @equiv_cancel_left with
    (g := contr_equiv_unit B Bcontr).
  exact (pr2 (contr_equiv_unit A Acontr)).
Defined.

(* A type is equivalent to its product with [unit]. *)

Definition prod_unit_right_equiv A : A <~> A * unit.
Proof.
  exists (fun a => (a,tt)).
  apply hequiv_is_equiv with (g := fun att:A*unit => let (a,t):=att in a).
  intros [a t]; destruct t; auto.
  auto.
Defined.

Definition prod_unit_left_equiv A : A <~> unit * A.
Proof.
  exists (fun a => (tt,a)).
  apply hequiv_is_equiv with (g := fun att:unit*A => let (t,a):=att in a).
  intros [t a]; destruct t; auto.
  auto.
Defined.

(** The action of an equivalence on paths is an equivalence. *)

Theorem equiv_map_inv {A B} {x y : A} (f : A <~> B) :
  (f x == f y) -> (x == y).
Proof.
  intros p.
  path_via (f^-1 (f x)).
  apply opposite, inverse_is_retraction.
  path_via' (f^-1 (f y)).
  apply map. assumption.
  apply inverse_is_retraction.
Defined.

Theorem equiv_map_is_equiv {A B} {x y : A} (f : A <~> B) :
  is_equiv (@map A B x y f).
Proof.
  apply @hequiv_is_equiv with (g := equiv_map_inv f).
  intro p.
  unfold equiv_map_inv.
  do_concat_map.
  do_opposite_map.
  moveright_onleft.
  undo_compose_map.
  path_via (map (f o (f ^-1)) p @ inverse_is_section f (f y)).
  apply inverse_triangle.
  path_via (inverse_is_section f (f x) @ p).
  apply homotopy_naturality_toid with (f := f o (f^-1)).
  apply opposite, inverse_triangle.
  intro p.
  unfold equiv_map_inv.
  moveright_onleft.
  undo_compose_map.
  apply homotopy_naturality_toid with (f := (f^-1) o f).
Defined.

Definition equiv_map_equiv {A B} {x y : A} (f : A <~> B) :
  (x == y) <~> (f x == f y) :=
  (@map A B x y f ; equiv_map_is_equiv f).

(** Path-concatenation is an equivalence. *)

Lemma concat_is_equiv_left {A} (x y z : A) (p : x == y) :
  is_equiv (fun q: y == z => p @ q).
Proof.
  apply @hequiv_is_equiv with (g := @concat A y x z (!p)).
  intro q.
  associate_left.
  intro q.
  associate_left.
Defined.

Definition concat_equiv_left {A} (x y z : A) (p : x == y) :
  (y == z) <~> (x == z) :=
  (fun q: y == z => p @ q  ;  concat_is_equiv_left x y z p).

Lemma concat_is_equiv_right {A} (x y z : A) (p : y == z) :
  is_equiv (fun q : x == y => q @ p).
Proof.
  apply @hequiv_is_equiv with (g := fun r : x == z => r @ !p).
  intro q.
  associate_right.
  intro q.
  associate_right.
Defined.

Definition concat_equiv_right {A} (x y z : A) (p : y == z) :
  (x == y) <~> (x == z) :=
  (fun q: x == y => q @ p  ;  concat_is_equiv_right x y z p).

(** Oppositizing is an equivalence. *)

Definition opposite_equiv {A} (x y : A) : (x == y) <~> (y == x).
Proof.
  exists opposite.
  apply hequiv_is_equiv with opposite.
  intros p; apply opposite_opposite.
  intros p; apply opposite_opposite.
Defined.

(** The same for opposite2. *)

Definition unopposite2 {A} {x y : A} (p q : x == y) : (!p == !q) -> (p == q).
Proof.
  intros r.
  path_via (!!p).
  apply @concat with (!!q).
  apply opposite2; assumption.
  auto with path_hints.
Defined.

Lemma opposite2_functor {A} (x y : A) (p q r : x == y) (s : p == q) (t : q == r) :
  opposite2 (s @ t) == opposite2 s @ opposite2 t.
Proof.
  path_induction.
Defined.

Lemma opposite2_opposite {A} (x y : A) (p q : x == y) (s : p == q) :
  opposite2 (!s) == !opposite2 s.
Proof.
  path_induction.
Defined.

Lemma opposite_opposite_opposite {A} (x y : A) (p : x == y) :
  opposite2 (opposite_opposite A x y p) ==
  opposite_opposite A y x (!p).
Proof.
  path_induction.
Defined.

Lemma opposite_opposite_natural {A} (x y : A) (p q : x == y) (r : p == q) :
  opposite2 (opposite2 r) @ opposite_opposite A x y q ==
  opposite_opposite A x y p @ r.
Proof.
  path_induction.
Defined.

Definition opposite2_equiv {A} (x y : A) (p q : x == y) : (p == q) <~> (!p == !q).
Proof.
  exists opposite2.
  apply hequiv_is_equiv with (g := unopposite2 p q).
  intros r.
  unfold unopposite2.
  path_via (opposite2 (!opposite_opposite A x y p) @
    opposite2 (opposite2 r @ opposite_opposite A x y q)).
  apply opposite2_functor.
  path_via (!opposite2 (opposite_opposite A x y p) @
    opposite2 (opposite2 r @ opposite_opposite A x y q)).
  apply opposite2_opposite.
  path_via (!(opposite_opposite A y x (!p)) @
   opposite2 (opposite2 r @ opposite_opposite A x y q)).
  apply opposite_opposite_opposite.
  moveright_onleft.
  path_via (opposite2 (opposite2 r) @ opposite2 (opposite_opposite A x y q)).
  apply opposite2_functor.
  path_via (opposite2 (opposite2 r) @ opposite_opposite A y x (!q)).
  apply opposite_opposite_opposite.
  apply opposite_opposite_natural.
  intros r.
  unfold unopposite2.
  moveright_onleft.
  apply opposite_opposite_natural.
Defined.

(** Transporting is an equivalence. *)

Theorem trans_equiv {A} {P : A -> Type} {x y : A} (p : x == y) :
  P x <~> P y.
Proof.
  exists (transport p).
  apply @hequiv_is_equiv with (transport (!p)).
  intros z.
  path_via (transport (!p @ p) z).
  apply opposite, trans_concat.
  path_via (transport (idpath _) z).
  apply happly. apply map.
  cancel_opposites.
  intros z.
  path_via (transport (p @ !p) z).
  apply opposite, trans_concat.
  path_via (transport (idpath _) z).
  apply happly. apply map.
  cancel_opposites.
Defined.
  
(** We can characterize the path types of the total space of a
   fibration, up to equivalence. *)

Theorem total_paths_equiv (A : Type) (P : A -> Type) (x y : sigT P) :
  (x == y) <~> { p : pr1 x == pr1 y & transport p (pr2 x) == pr2 y }.
Proof.
  exists (fun r => existT (fun p => transport p (pr2 x) == pr2 y) (base_path r) (fiber_path r)).
  eapply @hequiv_is_equiv.
  instantiate (1 := fun pq => let (p,q) := pq in total_path A P x y p q).
  intros [p q].
  eapply total_path.
  instantiate (1 := base_total_path A P x y p q).
  simpl.
  apply fiber_total_path.
  intro r.
  simpl.
  apply total_path_reconstruction.
Defined.

(** And similarly for products. *)

Program Definition prod_path_equiv A B (x y : A * B) :
  (x == y) <~> ((fst x == fst y) * (snd x == snd y))
  := (fun p => (map (@fst A B) p, map (@snd A B) p) ;
    hequiv_is_equiv _ _ _ _).
Next Obligation.
  intros A B [a1 b1] [a2 b2] [p q].
  apply prod_path; assumption.
Defined.
Next Obligation.
  intros A B [a1 b1] [a2 b2] [p q].
  unfold prod_path_equiv_obligation_1.
  simpl in p, q.
  apply prod_path; induction p; induction q; auto.
Defined.
Next Obligation.
  intros A B x1 x2 pq.
  induction pq as [[a b]].
  unfold prod_path_equiv_obligation_1; auto.
Defined.


(** The homotopy fiber of a fibration is equivalent to the actual fiber. *)

Section hfiber_fibration.

  Hypothesis X:Type.
  Hypothesis P : X -> Type.

  Let hfiber_fibration_map (x : X) : { z : sigT P & pr1 z == x } -> P x.
  Proof.
    intros [z p].
    apply (transport p).
    exact (pr2 z).
  Defined.

  Let hfiber_fibration_map_path (x : X) (z : sigT P) (p : pr1 z == x) :
    (x ; hfiber_fibration_map x (z ; p)) == z.
  Proof.
    apply total_path with (p := !p).
    destruct z as [x' y']. simpl.
    path_via (transport (p @ !p) y').
    apply opposite, trans_concat.
    path_via (transport (idpath _) y').
    apply map with (f := fun q => transport q y').
    cancel_opposites.
  Defined.

  Definition hfiber_fibration (x : X) :
    P x <~> { z : sigT P & pr1 z == x }.
  Proof.
    exists (fun y: P x => (((x ; y) ; idpath _)
      : {z : sigT P & pr1 z == x})).
    apply hequiv_is_equiv with (g := hfiber_fibration_map x).
    intros [z p].
    apply total_path with (p := hfiber_fibration_map_path x z p). simpl.
    path_via (transport (P := fun x' => x' == x)
      (map pr1 (hfiber_fibration_map_path x z p))
      (idpath x)).
    apply @map_trans with (P := fun x' => x' == x).
    unfold hfiber_fibration_map_path.
    path_via (transport (P := fun x' => x' == x) (!p) (idpath x)).
    apply map with (f := fun r => transport (P := fun x' => x' == x) r (idpath x)).
    apply @base_total_path with
      (x := (x ; hfiber_fibration_map x (z ; p))).
    path_via ((!!p) @ idpath x).
    apply trans_is_concat_opp.
    cancel_units.
    intros y.
    unfold hfiber_fibration_map. simpl. auto.
  Defined.

End hfiber_fibration.

(** Replacement of a map by an equivalent fibration. *)

Section FibrationReplacement.

  Hypothesis A B : Type.
  Hypothesis f : A -> B.
  
  Definition fibration_replacement (x:A) : {y:B & {x:A & f x == y}} :=
    (f x ; (x ; idpath (f x))).

  Definition fibration_replacement_equiv : A <~> {y:B & {x:A & f x == y}}.
  Proof.
    exists fibration_replacement.
    apply hequiv_is_equiv with
      (g := fun yxp => match yxp with
                         existT y (existT x p) => x
                       end).
    intros [y [x p]].
    unfold fibration_replacement.
    apply total_path with (p := p). simpl.
    path_via (existT (fun x' => f x' == y) x (idpath (f x) @ p)).
    path_via (existT (fun x' => f x' == y) x (transport p (idpath (f x)))).
    apply opposite.
    apply @trans_map with
      (P := fun y' => f x == y')
      (Q := fun y' => {x':A & f x' == y'})
      (f := fun y' q => existT (fun x' => f x' == y') x q).
    apply trans_is_concat.
    intros x. auto.
  Defined.

  Definition fibration_replacement_factors (x:A) :
    pr1 (fibration_replacement_equiv x) == f x.
  Proof.
    auto.
  Defined.

End FibrationReplacement.

(** The construction of total spaces of fibrations is "associative". *)

Section TotalAssoc.

  Hypotheses (A:Type) (P : A -> Type) (Q : forall x, P x -> Type).

  Let ta1 : { x:A & { p:P x & Q x p}} -> { xp : sigT P & Q (pr1 xp) (pr2 xp) }.
  Proof.
    intros [x [p q]].
    exists (x;p).
    exact q.
  Defined.

  Let ta2 : { xp : sigT P & Q (pr1 xp) (pr2 xp) } -> { x:A & { p:P x & Q x p}}.
  Proof.
    intros [[x p] q].
    exists x. exists p. exact q.
  Defined.
    
  Definition total_assoc :
    { x:A & { p:P x & Q x p}} <~> { xp : sigT P & Q (pr1 xp) (pr2 xp) }.
  Proof.
    exists ta1.
    apply hequiv_is_equiv with ta2.
    intros [[x p] q]; auto.
    intros [x [p q]]; auto.
  Defined.

End TotalAssoc.

Section TotalAssocSum.

  Hypotheses (A:Type) (P : A -> Type) (Q : sigT P -> Type).

  Let ta1 : { x:A & { p:P x & Q (x;p)}} -> { xp : sigT P & Q xp }.
  Proof.
    intros [x [p q]].
    exists (x;p).
    exact q.
  Defined.

  Let ta2 : { xp : sigT P & Q xp } -> { x:A & { p:P x & Q (x;p)}}.
  Proof.
    intros [[x p] q].
    exists x. exists p. exact q.
  Defined.
    
  Definition total_assoc_sum :
    { x:A & { p:P x & Q (x;p)}} <~> { xp : sigT P & Q xp }.
  Proof.
    exists ta1.
    apply hequiv_is_equiv with ta2.
    intros [[x p] q]; auto.
    intros [x [p q]]; auto.
  Defined.

End TotalAssocSum.

(** And "commutative" *)

Section TotalComm.

  Hypotheses (A:Type) (B:Type) (P : A -> B -> Type).

  Let tc1 : {x:A & {y:B & P x y}} -> {y:B & {x:A & P x y}}.
  Proof.
    intros [x [y p]].
    exists y.  exists x.  exact p.
  Defined.

  Let tc2 : {y:B & {x:A & P x y}} -> {x:A & {y:B & P x y}}.
  Proof.
    intros [y [x p]].
    exists x.  exists y.  exact p.
  Defined.
  
  Definition total_comm :
    {x:A & {y:B & P x y}} <~> {y:B & {x:A & P x y}}.
  Proof.
    exists tc1.
    apply hequiv_is_equiv with tc2.
    intros [x [y p]]; auto.
    intros [y [x p]]; auto.
  Defined.

End TotalComm.

(** Transporting along a path is an "adjoint equivalence". *)

Lemma transport_adjoint X (P : X -> Type) (x y : X) (p : x == y)
  (a : P x) (b : P y) :
  (transport p a == b) <~> (a == transport (!p) b).
Proof.
  path_induction.
  simpl.
  apply idequiv.
Defined.

(** The product of two equivalences is an equivalence. *)

Lemma product_equiv A B C D :
  (A <~> B) -> (C <~> D) -> (A*C <~> B*D).
Proof.
  intros f g.
  exists (fun ac => (f (fst ac), g (snd ac))).
  apply @hequiv_is_equiv with
    (g := fun bd => (f ^-1 (fst bd), g ^-1 (snd bd))).
  intros [b d]; simpl.
  apply prod_path; simpl; cancel_inverses.
  intros [a c] ;simpl.
  apply prod_path; simpl; cancel_inverses.
Defined.

(** Products are equivalent to pullbacks over any contractible type. *)

Section PullbackContr.

  Hypotheses A B C : Type.
  Hypothesis Cc : is_contr C.
  Hypothesis (f : A -> C) (g : B -> C).

  Let pbu1 : {x:A & {y:B & f x == g y}} -> A * B.
  Proof.
    intros [a [b p]].
    exact (a,b).
  Defined.

  Let pbu2 : A * B -> {x:A & {y:B & f x == g y}}.
  Proof.
    intros [a b].
    exists a; exists b; apply contr_path, Cc.
  Defined.

  Definition pullback_over_contr : {x:A & {y:B & f x == g y}} <~> A * B.
  Proof.
    exists pbu1.
    apply hequiv_is_equiv with pbu2.
    intros [a b]. simpl. auto.
    intros [a [b p]]. simpl.
    apply total_path with (idpath a). simpl.
    apply total_path with (idpath b); simpl.
    apply contr_path2. apply Cc.
  Defined.
  
End PullbackContr.
