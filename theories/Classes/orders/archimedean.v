Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.archimedean
  HoTT.Classes.theory.groups
  HoTT.Classes.theory.rationals
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.rings.

Generalizable Variables Q F.

Section strict_field_order.
  Context `{Rationals Q}.
  Context `{LatticeOrder Q}.
  Context `{OrderedField F}.
  (* Context `{FieldCharacteristic F 0}. *)
  Context `{ArchimedeanProperty Q F}.

  Definition qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Lemma char_minus_left x y : - x < y -> - y < x.
  Proof.
    intros ltnxy. rewrite <- (negate_involutive x). apply (snd (flip_lt_negate _ _)). assumption.
  Qed.

  Lemma char_minus_right x y : x < - y -> y < - x.
  Proof.
    intros ltnxy. rewrite <- (negate_involutive y). apply (snd (flip_lt_negate _ _)). assumption.
  Qed.

  Axiom char_plus_left : forall (q : Q) (x y : F),
      ' q < x + y <-> hexists (fun s : Q => (' s < x) /\ (' (q - s) < y)).
  (* Lemma char_plus_left (q : Q) (x y : F) : ' q < x + y <-> hexists (fun s : Q => and (' s < x) (' (q - s) < y)). *)
  (* Proof. *)
  (*   split. *)
  (*   - intros ltqxy. *)
  (*     assert (heps : hexists (fun (epsilon : Qpos Q) => ' (q + ' epsilon) < x + y)) by admit. *)
  (*     refine (Trunc_ind _ _ heps); intros [epsilon ltqepsxy]. *)
  (*     assert (hs : hexists (fun (s : Q) => ' s < x < ' (s + ' epsilon))) by admit. *)
  (*     refine (Trunc_ind _ _ hs); intros [s [ltsx ltxseps]]. *)
  (*     apply tr; exists s; split. *)
  (*     + assumption. *)
  (*     + *)
  Axiom char_plus_right : forall (r : Q) (x y : F),
      x + y < ' r <-> hexists (fun t : Q => (x < ' t) /\ (y < ' (r - t))).

  Definition hexists4 {X Y Z W} (f : X -> Y -> Z -> W -> Type) : hProp
    := hexists (fun xyzw => match xyzw with
                            | ((x , y) , (z , w)) => f x y z w
                            end).
  Check (_ : Join Q).

  Axiom char_times_left : forall (q : Q) (x y : F),
          ' q < x * y
      <-> hexists4 (fun a b c d : Q =>
                      (q < meet (meet a b) (meet c d))
                      /\
                      ((' a < x < ' b)
                       /\
                       (' c < y < ' d)
                      )
                   ).
  Axiom char_times_right : forall (r : Q) (x y : F),
          x * y < ' r
      <-> hexists4 (fun a b c d : Q =>
                      and (join (join a b) (join c d) < r)
                          (and
                             (' a < x < ' b)
                             (' c < y < ' d)
                          )
                   ).

  Axiom char_recip_pos_left : forall (q : Q) (z : F) (nu : 0 < z),
    'q < recip (z ; positive_apart_zero z nu) <-> ' q * z < 1.
  Axiom char_recip_pos_right : forall (r : Q) (z : F) (nu : 0 < z),
    recip (z ; positive_apart_zero z nu) < ' r <-> 1 < ' r * z.
  Axiom char_recip_neg_left : forall (q : Q) (w : F) (nu : w < 0),
    'q < recip (w ; negative_apart_zero w nu) <-> ' q * w < 1.
  Axiom char_recip_neg_right : forall (r : Q) (w : F) (nu : w < 0),
    recip (w ; negative_apart_zero w nu) < ' r <-> ' r * w < 1.

  Axiom char_meet_left : forall (q : Q) (x y : F),
      ' q < meet x y <-> ' q < x /\ ' q < y.
  Axiom char_meet_right : forall (r : Q) (x y : F),
      meet x y < 'r <-> hor (x < 'r) (y < 'r).
  Axiom char_join_left : forall (q : Q) (x y : F),
      ' q < join x y <-> hor ('q < x) ('q < y).
  Axiom char_join_right : forall (r : Q) (x y : F),
      join x y < ' r <-> x < ' r /\ y < ' r.

End strict_field_order.
