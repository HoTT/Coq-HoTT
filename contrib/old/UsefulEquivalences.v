Require Import Logic_Type.
Require Export Paths Fibrations Contractible Equivalences.

(** Any two contractible types are equivalent. *)

Lemma contr_contr_equiv {A B} :
  is_contr A -> is_contr B -> A <~> B.
Proof.
  intros Acontr Bcontr.
  exact (equiv_compose (contr_equiv_unit A Acontr) (equiv_inverse (contr_equiv_unit B Bcontr))).
Defined.

Lemma contr_contr_is_equiv {A B} (f : A -> B) :
  is_contr A -> is_contr B -> is_equiv f.
Proof.
  intros H G.
  apply is_equiv_from_hequiv with (g := fun _ => pr1 H);
    intro; apply contr_path; assumption.
Defined.

(* A type is equivalent to its product with [unit]. *)

Definition prod_unit_right_equiv A : A <~> A * unit.
Proof.
  apply (equiv_from_hequiv (fun (a : A) => (a, tt)) (@fst A unit)).
  intros [a t]; destruct t; auto.
  auto.
Defined.

Definition prod_unit_left_equiv A : A <~> unit * A.
Proof.
  apply (equiv_from_hequiv (fun (a : A) => (tt, a)) (@snd unit A)).
  intros [t a]; destruct t; auto.
  auto.
Defined.

(** The action of an equivalence on paths is an equivalence. Notice that
   we only need the "retraction" part of equivalence, so there is room
   for improvement. *)

Theorem equiv_map_inv {A B} {x y : A} (f : A <~> B) :
  (f x = f y) -> (x = y).
Proof.
  intros p.
  path_via (f^-1 (f x)).
  apply opposite.
  apply inverse_is_retraction.
  path_via' (f^-1 (f y)).
  apply map; exact p.
  apply inverse_is_retraction.
Defined.

Theorem equiv_map_equiv {A B} {x y : A} (e : A <~> B) : (x = y) <~> (e x = e y).
Proof.
  apply (equiv_from_hequiv (@map A B x y e) (equiv_map_inv (x := x) (y := y) e)).
  intro p.
  unfold equiv_map_inv.
  hott_simpl.
  moveright_onleft.
  moveright_onright.
  rewrite inverse_triangle.
  transitivity ((inverse_is_section e (e x) @ p) @ opposite (inverse_is_section e (e y))).
  apply opposite, concat_associativity.
  apply whisker_left.
  apply map.
  apply opposite.
  apply inverse_triangle.
  intro p.
  unfold equiv_map_inv.
  moveright_onleft.
  associate_left.
Defined.

(** Path-concatenation is an equivalence. *)

Lemma concat_equiv_left {A} (x y z : A) (p : x = y) : (y = z) <~> (x = z).
Proof.
  apply (equiv_from_hequiv (fun q : y = z => p @ q) (@concat A y x z (!p)));
  intro q; associate_left.
Defined.

Lemma concat_equiv_right {A} (x y z : A) (p : y = z) : (x = y) <~> (x = z).
Proof.
  apply (equiv_from_hequiv (fun q : x = y => q @ p) (fun r : x = z => r @ !p));
  intro q; associate_right.
Defined.

(** Opposite is an equivalence. *)

Definition opposite_equiv {A} (x y : A) : (x = y) <~> (y = x).
Proof.
  apply (equiv_from_hequiv (@opposite A x y) (@opposite A y x)).
  intros p; apply opposite_opposite.
  intros p; apply opposite_opposite.
Defined.

(** The same for opposite2. *)

Definition unopposite2 {A} {x y : A} (p q : x = y) : (!p = !q) -> (p = q).
Proof.
  intros r.
  path_via (!!p).
  apply @concat with (!!q).
  apply opposite2; assumption.
  auto with path_hints.
Defined.

Lemma opposite2_functor {A} (x y : A) (p q r : x = y) (s : p = q) (t : q = r) :
  opposite2 (s @ t) = opposite2 s @ opposite2 t.
Proof.
  path_induction.
Defined.

Lemma opposite2_opposite {A} (x y : A) (p q : x = y) (s : p = q) :
  opposite2 (!s) = !opposite2 s.
Proof.
  path_induction.
Defined.

Lemma opposite_opposite_opposite {A} (x y : A) (p : x = y) :
  opposite2 (opposite_opposite p) =
  opposite_opposite (!p).
Proof.
  path_induction.
Defined.

Lemma opposite_opposite_natural {A} (x y : A) (p q : x = y) (r : p = q) :
  opposite2 (opposite2 r) @ opposite_opposite q =
  opposite_opposite p @ r.
Proof.
  path_induction.
Defined.

Definition opposite2_equiv {A} (x y : A) (p q : x = y) : (p = q) <~> (!p = !q).
Proof.
  apply (equiv_from_hequiv (@opposite2 A x y p q) (unopposite2 p q)).
  intros r.
  unfold unopposite2.
  path_via' (opposite2 (!opposite_opposite p) @
    opposite2 (opposite2 r @ opposite_opposite q)).
  apply opposite2_functor.
  path_via' (!opposite2 (opposite_opposite p) @
    opposite2 (opposite2 r @ opposite_opposite q)).
  apply whisker_right.
  apply opposite2_opposite.
  path_via' (!(opposite_opposite (!p)) @
   opposite2 (opposite2 r @ opposite_opposite q)).
  apply whisker_right.
  apply map.
  apply opposite_opposite_opposite.
  moveright_onleft.
  path_via (opposite2 (opposite2 r) @ opposite2 (opposite_opposite q)).
  apply opposite2_functor.
  path_via' (opposite2 (opposite2 r) @ opposite_opposite (!q)).
  apply whisker_left.
  apply opposite_opposite_opposite.
  apply opposite_opposite_natural.
  intros r.
  unfold unopposite2.
  moveright_onleft.
  rewrite opposite_opposite_natural. hott_simpl. 
Defined.

(** Transporting is an equivalence. *)

Theorem trans_equiv {A} {P : fibration A} {x y : A} (p : x = y) :
  P x <~> P y.
Proof.
  apply (equiv_from_hequiv (transport (P := P) p) (transport (P := P) (!p))).
  intros z.
  (** XXX find out why [hott_simpl] cycles in 8.4 at this point. *)
  apply trans_trans_opp.
  intros z.
  apply trans_opp_trans.
Defined.
  
(** We can characterize the path types of the total space of a
   fibration, up to equivalence. *)

Theorem total_paths_equiv (A : Type) (P : fibration A) (x y : total P) :
  (x = y) <~> { p : pr1 x = pr1 y & transport p (pr2 x) = pr2 y }.
Proof.
  apply (equiv_from_hequiv
     (fun r => existT (fun p => transport p (pr2 x) = pr2 y) (base_path r) (fiber_path r))
     (fun (pq : { p : pr1 x = pr1 y & transport p (pr2 x) = pr2 y }) =>
          @total_path A P x y (projT1 pq) (projT2 pq))).
  intros [p q].
  simpl.
  apply @total_path with (p := base_total_path q).
  simpl.
  apply fiber_total_path.
  intro r.
  simpl.
  apply total_path_reconstruction.
Defined.

(** And similarly for products. *)

Lemma prod_eta A B (u : A * B) : (fst u, snd u) = u.
Proof.
  destruct u; path_induction.
Defined.

Definition prod_path_equiv A B (x y : A * B) :
  (x = y) <~> ((fst x = fst y) * (snd x = snd y)).
Proof.
  apply (equiv_from_hequiv 
    (fun p => (map (x:=x) (y:=y) (@fst A B) p, map (@snd A B) p))
    (fun (u : (fst x = fst y) * (snd x = snd y)) =>
      !prod_eta A B x @ prod_path (fst u) (snd u) @ prod_eta A B y)).
  intros [p q].
  destruct x; destruct y.
  simpl in * |- *.
  path_induction.
  intro p.
  path_induction.
  destruct x; auto.
Defined.

(** The homotopy fiber of a fibration is equivalent to the actual fiber. *)

Section hfiber_fibration.

  Hypothesis X : Type.
  Hypothesis P : fibration X.

  Let hfiber_fibration_map (x : X) : { z : total P & pr1 z = x } -> P x.
  Proof.
    intros [z p].
    apply (transport p).
    exact (pr2 z).
  Defined.

  Let hfiber_fibration_map_path (x : X) (z : total P) (p : pr1 z = x) :
    (x ; hfiber_fibration_map x (z ; p)) = z.
  Proof.
    apply @total_path with (p := !p).
    destruct z as [x' y']. simpl.
    apply trans_opp_trans.
  Defined.

  Definition hfiber_fibration (x : X) :
    P x <~> { z : total P & pr1 z = x }.
  Proof.
  apply (  equiv_from_hequiv
      (fun y: P x => (((x ; y) ; idpath _) : {z : sigT P & pr1 z = x}))
      (hfiber_fibration_map x)).
    intros [z p].
    apply @total_path with (p := hfiber_fibration_map_path x z p). simpl.
    path_via (transport (P := fun x' => x' = x)
      (map pr1 (hfiber_fibration_map_path x z p))
      (idpath x)).
    apply @map_trans with (P := fun x' => x' = x).
    unfold hfiber_fibration_map_path.
    path_via (transport (P := fun x' => x' = x) (!p) (idpath x)).
    apply map with (f := fun r => transport (P := fun x' => x' = x) r (idpath x)).
    apply @base_total_path with
      (x := (x ; hfiber_fibration_map x (z ; p))).
    path_via ((!!p) @ idpath x).
    cancel_units.
    intros y.
    unfold hfiber_fibration_map. simpl. auto.
  Defined.

End hfiber_fibration.

(** Replacement of a map by an equivalent fibration. *)

Section FibrationReplacement.

  Hypothesis A B : Type.
  Hypothesis f : A -> B.
  
  Definition fibration_replacement (x : A) : {y : B & {x : A & f x = y}} :=
    (f x ; (x ; idpath (f x))).

  Definition fibration_replacement_equiv : A <~> {y : B & {x : A & f x = y}}.
  Proof.
  apply (  equiv_from_hequiv
      fibration_replacement (fun (yxp : {y : B & {x : A & f x = y}}) => pr1 (pr2 yxp))).
    intros [y [x p]].
    unfold fibration_replacement; simpl.
    apply @total_path with (p := p); simpl.
    hott_simpl.
    (* This step needed in 8.3 but not 8.4. *)
    try (rewrite map_trans; hott_simpl).
    intros x. auto.
  Defined.

  Definition fibration_replacement_factors (x : A) :
    pr1 (fibration_replacement_equiv x) = f x.
  Proof.
    auto.
  Defined.

End FibrationReplacement.

(** The construction of total spaces of fibrations is "associative". *)

Section TotalAssoc.

  Hypotheses (A : Type) (P : fibration A) (Q : forall x, fibration (P x)).

  Let ta1 : { x : A & { p : P x & Q x p}} -> { xp : total P & Q (pr1 xp) (pr2 xp) }.
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
    { x : A & { p : P x & Q x p}} <~> { xp : sigT P & Q (pr1 xp) (pr2 xp) }.
  Proof.
    apply (equiv_from_hequiv ta1 ta2).
    intros [[x p] q]; auto.
    intros [x [p q]]; auto.
  Defined.

End TotalAssoc.

Section TotalAssocSum.

  Hypotheses (A : Type) (P : fibration A) (Q : total P -> Type).

  Let ta1 : {x : A & {p : P x & Q (x ; p)}} -> {xp : total P & Q xp}.
  Proof.
    intros [x [p q]].
    exists (x;p).
    exact q.
  Defined.

  Let ta2 : {xp : total P & Q xp} -> {x : A & {p : P x & Q (x ; p)}}.
  Proof.
    intros [[x p] q].
    exists x. exists p. exact q.
  Defined.
    
  Definition total_assoc_sum :
    {x : A & {p : P x & Q (x;p)}} <~> {xp : total P & Q xp}.
  Proof.
    apply (equiv_from_hequiv ta1 ta2).
    intros [[x p] q]; auto.
    intros [x [p q]]; auto.
  Defined.

End TotalAssocSum.

(** And "commutative" *)

Section TotalComm.

  Hypotheses (A : Type) (B : Type) (P : A -> B -> Type).

  Let tc1 : {x : A & {y : B & P x y}} -> {y : B & {x:A & P x y}}.
  Proof.
    intros [x [y p]].
    exists y.  exists x.  exact p.
  Defined.

  Let tc2 : {y : B & {x : A & P x y}} -> {x : A & {y : B & P x y}}.
  Proof.
    intros [y [x p]].
    exists x.  exists y.  exact p.
  Defined.
  
  Definition total_comm :
    {x : A & {y : B & P x y}} <~> {y : B & {x : A & P x y}}.
  Proof.
    apply (equiv_from_hequiv tc1 tc2).
    intros [x [y p]]; auto.
    intros [y [x p]]; auto.
  Defined.

End TotalComm.

(** Transporting along a path is an "adjoint equivalence". *)

Lemma transport_adjoint A (P : fibration A) (x y : A) (p : x = y)
  (a : P x) (b : P y) :
  (transport p a = b) <~> (a = transport (!p) b).
Proof.
  path_induction.
  simpl.
  apply idequiv.
Defined.

(** The product of two equivalences is an equivalence. *)

Lemma product_equiv (A B C D : Type):
  (A <~> B) -> (C <~> D) -> (A * C <~> B * D).
Proof.
  intros f g.
  apply (equiv_from_hequiv
    (fun ac => (f (fst ac), g (snd ac)))
    (fun bd => (f^-1 (fst bd), g^-1 (snd bd)))) ;
  intros [? ?]; simpl; apply prod_path; hott_simpl.
Defined.

(** Products are equivalent to pullbacks over any contractible type. *)

Section PullbackContr.

  Hypotheses A B C : Type.
  Hypothesis Cc : is_contr C.
  Hypothesis (f : A -> C) (g : B -> C).

  Let pbu1 : {x : A & {y : B & f x = g y}} -> A * B.
  Proof.
    intros [a [b p]].
    exact (a,b).
  Defined.

  Let pbu2 : A * B -> {x : A & {y : B & f x = g y}}.
  Proof.
    intros [a b].
    exists a; exists b; apply contr_path, Cc.
  Defined.

  Definition pullback_over_contr : {x : A & {y : B & f x = g y}} <~> A * B.
  Proof.
    apply (equiv_from_hequiv pbu1 pbu2).
    intros [a b]; simpl; auto.
    intros [a [b p]]; simpl.
    apply @total_path with (idpath a). simpl.
    apply @total_path with (idpath b); simpl.
    apply contr_path2. apply Cc.
  Defined.
  
End PullbackContr.
