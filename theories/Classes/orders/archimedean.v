Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.archimedean
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.fields
  HoTT.Classes.orders.maps
  HoTT.Classes.orders.rings
  HoTT.Classes.orders.fields
  HoTT.Classes.orders.lattices.

Generalizable Variables Q F.

Section strict_field_order.
  Context `{Rationals Q}.
  Context {Qmeet} {Qjoin} `{@LatticeOrder Q (_ : Le Q) Qmeet Qjoin}.
  Context `{OrderedField F}.
  Context {archim : ArchimedeanProperty Q F}.

  Definition qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.


  (** ** Negation *)

  Lemma char_minus_left x y : - x < y -> - y < x.
  Proof.
    exact (flip_lt_negate_l x y).
  Qed.

  Lemma char_minus_right x y : x < - y -> y < - x.
  Proof.
    exact (flip_lt_negate_r y x).
  Qed.

  Lemma char_plus_left : forall (q : Q) (x y : F),
      ' q < x + y <-> hexists (fun s : Q => (' s < x) /\ (' (q - s) < y)).
  Proof. Abort.
  Lemma char_plus_right : forall (r : Q) (x y : F),
      x + y < ' r <-> hexists (fun t : Q => (x < ' t) /\ (y < ' (r - t))).
  Proof. Abort.

  Definition hexists4 {X Y Z W} (f : X -> Y -> Z -> W -> Type) : HProp
    := hexists (fun xyzw => match xyzw with
                            | ((x , y) , (z , w)) => f x y z w
                            end).

  Lemma char_times_left : forall (q : Q) (x y : F),
          ' q < x * y
      <-> hexists4 (fun a b c d : Q =>
                      (q < meet (meet a b) (meet c d))
                      /\
                      ((' a < x < ' b)
                       /\
                       (' c < y < ' d)
                      )
                   ).
  Proof. Abort.
  Lemma char_times_right : forall (r : Q) (x y : F),
          x * y < ' r
      <-> hexists4 (fun a b c d : Q =>
                      and (join (join a b) (join c d) < r)
                          (and
                             (' a < x < ' b)
                             (' c < y < ' d)
                          )
                   ).
  Proof. Abort.

  (** ** Reciprocals *)

  Local Lemma lt_iff_mult_pos_r (z : F) (zpos : 0 < z) (a b : F) : a < b <-> a * z < b * z.
  Proof.
    split.
    - apply (strictly_order_preserving (.* z)).
    - apply (strictly_order_reflecting (.* z)).
  Qed.

  Local Lemma lt_iff_mult_neg_r (w : F) (wneg : w < 0) (a b : F) : a < b <-> b * w < a * w.
  Proof.
    assert (negwpos : 0 < - w) by exact (fst (flip_neg_negate w) wneg).
    apply (iff_compose (lt_iff_mult_pos_r (- w) negwpos a b)).
    rewrite <- 2!negate_mult_distr_r. apply flip_lt_negate.
  Qed.

  Lemma char_recip_pos_left (q : Q) (z : F) (nu : 0 < z) :
    'q < recip' z (positive_apart_zero z nu) <-> ' q * z < 1.
  Proof.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    apply lt_iff_mult_pos_r, nu.
  Qed.

  Lemma char_recip_pos_right (r : Q) (z : F) (nu : 0 < z) :
    recip' z (positive_apart_zero z nu) < ' r <-> 1 < ' r * z.
  Proof.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    apply lt_iff_mult_pos_r, nu.
  Qed.

  Lemma char_recip_neg_left (q : Q) (w : F) (nu : w < 0) :
    'q < recip' w (negative_apart_zero w nu) <-> 1 < ' q * w.
  Proof.
    rewrite <- (recip_inverse' w (negative_apart_zero w nu)), (commutativity w).
    apply lt_iff_mult_neg_r, nu.
  Qed.

  Lemma char_recip_neg_right (r : Q) (w : F) (nu : w < 0) :
    recip' w (negative_apart_zero w nu) < ' r <-> ' r * w < 1.
  Proof.
    rewrite <- (recip_inverse' w (negative_apart_zero w nu)), (commutativity w).
    apply lt_iff_mult_neg_r, nu.
  Qed.

  (** ** Meet and join *)

  Lemma char_meet_left (q : Q) (x y : F) :
      ' q < meet x y <-> ' q < x /\ ' q < y.
  Proof.
    split.
    - intros ltqm; split; (rapply lt_le_trans; [exact ltqm|]).
      + apply meet_lb_l.
      + apply meet_lb_r.
    - intros [ltqx ltqy]. apply meet_lt_l; assumption.
  Qed.

  Lemma char_meet_right (r : Q) (x y : F) :
      meet x y < 'r <-> hor (x < 'r) (y < 'r).
  Proof.
    split.
    - intros ltmr.
      assert (cx := cotransitive ltmr x).
      assert (cy := cotransitive ltmr y).
      strip_truncations.
      destruct cx as [ltmx|ltxr]; [|exact (tr (inl ltxr))].
      destruct cy as [ltmy|ltyr]; [|exact (tr (inr ltyr))].
      destruct (irreflexivity (<) (meet x y) (meet_lt_l (meet x y) x y ltmx ltmy)).
    - intros h. strip_truncations; destruct h as [ltxr|ltyr].
      + apply meet_lt_r_l. assumption.
      + apply meet_lt_r_r. assumption.
  Qed.

  Lemma char_join_left (q : Q) (x y : F) :
      ' q < join x y <-> hor ('q < x) ('q < y).
  Proof.
    split.
    - intros ltqj.
      assert (cx := cotransitive ltqj x).
      assert (cy := cotransitive ltqj y).
      strip_truncations.
      destruct cx as [ltqx|ltxj]; [exact (tr (inl ltqx))|].
      destruct cy as [ltqy|ltyj]; [exact (tr (inr ltqy))|].
      destruct (irreflexivity (<) (join x y) (join_lt_r x y (join x y) ltxj ltyj)).
    - intros h. strip_truncations; destruct h as [ltqx|ltqy].
      + apply join_lt_l_l. assumption.
      + apply join_lt_l_r. assumption.
  Qed.

  Lemma char_join_right (r : Q) (x y : F) :
      join x y < ' r <-> x < ' r /\ y < ' r.
  Proof.
    split.
    - intros ltjr; split; (rapply le_lt_trans; [|exact ltjr]).
      + apply join_ub_l.
      + apply join_ub_r.
    - intros [ltxr ltyr]. apply join_lt_r; assumption.
  Qed.

End strict_field_order.
