(** Homotopy-initial two-algebras. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* A two-algebra consists of a type C and two terms (c_f c_t : C). *)

(* The type of two-algebra homomorphisms. *)
Definition TwoHom (C : U) (c_f c_t : C) (D : U) (d_f d_t : D) : U
  := Sigma (fun f : C -> D => Prod (Id (f c_f) d_f) (Id (f c_t) d_t)).

(* The type of two-algebra 2-cells. *)
Definition TwoCell {C : U} {c_f c_t : C} {D : U} {d_f d_t : D} (h_1 h_2 : TwoHom C c_f c_t D d_f d_t) : U
  := Sigma (fun p : forall (x : C), Id (p1 h_1 x) (p1 h_2 x) =>
     Prod  (Id ((p c_f) @ (p1 (p2 h_2))) (p1 (p2 h_1)))
           (Id ((p c_t) @ (p2 (p2 h_2))) (p2 (p2 h_1)))).

(* Homotopy-initial two-algebras *)
Definition two_hinitial (C : U) (c_f c_t : C) : Type
  := forall (D : U) (d_f d_t : D), iscontr (TwoHom C c_f c_t D d_f d_t).

(***********************************************************************)
(***********************************************************************)

(** Given two-algebra homomorphisms h_1 h_2, they are propositionally equal
    iff there exists a 2-cell between them. **)

Section TwoCells.

(* Fix two-algebras C and D. *)
Variable C : U.
Variable c_f : C.
Variable c_t : C.

Variable D : U.
Variable d_f : D.
Variable d_t : D.

(* Fix two-algebra homomorphisms h_1 and h_2. *)
Variable h_1 h_2 : TwoHom C c_f c_t D d_f d_t.

(***********************************************************************)
(***********************************************************************)

(* Some preliminary definitions and lemmas. *)
Section Prelim.

Definition F_f : (C -> D) -> D := fun f : C -> D => f c_f.
Definition F_t : (C -> D) -> D := fun f : C -> D => f c_t.

Definition G_f : (C -> D) -> D := fun _ : C -> D => d_f.
Definition G_t : (C -> D) -> D := fun _ : C -> D => d_t.

Definition Q_f := fun f => Id (f c_f) d_f.
Definition Q_t := fun f => Id (f c_t) d_t.

Definition P := fun f => Prod (Q_f f) (Q_t f).

(***********************************************************************)
(***********************************************************************)

Lemma mapid_F_f (f g : C -> D) (p : Id f g) :
  Id (mapid F_f p) (appid p c_f).
Proof.
apply trans with (b := appid (mapid (@id (C -> D)) p) c_f).
apply mapid_app_to_const with (N := c_f) (M := @id (C -> D)).
apply @dappid with (g := appid p).
apply appid_cong.
apply mapid_id.
Defined.

Lemma mapid_F_t (f g : C -> D) (p : Id f g) :
  Id (mapid F_t p) (appid p c_t).
Proof.
apply trans with (b := appid (mapid (@id (C -> D)) p) c_t).
apply mapid_app_to_const with (N := c_t) (M := @id (C -> D)).
apply @dappid with (g := appid p).
apply appid_cong.
apply mapid_id.
Defined.

Lemma mapid_G_f (f g : C -> D) (p : Id f g) :
  Id (mapid G_f p) (refl d_f).
Proof.
apply mapid_const.
Defined.

Lemma mapid_G_t (f g : C -> D) (p : Id f g) :
  Id (mapid G_t p) (refl d_t).
Proof.
apply mapid_const.
Defined.

(***********************************************************************)
(***********************************************************************)

Lemma transport_P {f g : C -> D} (p : Id f g) :
  Id (transport P p)
     (fun q => pair ((appid p c_f)! @ p1 q) ((appid p c_t)! @ p2 q)).
Proof.
apply trans with (b :=
  fun q : P f => pair (transport Q_f p (p1 q)) (transport Q_t p (p2 q))).
apply transport_prod.
apply funext.
intro q.
apply prodext.
simpl.
split.

apply trans with (b := (mapid F_f p)! @ p1 q @ mapid G_f p).
apply @appid with (g :=
  fun q_f : Q_f f => (mapid F_f p)! @ q_f @ mapid G_f p).
apply @transport_id with (f := F_f) (g := G_f).
apply trans with (b := (mapid F_f p)! @ p1 q @ refl d_f).
apply concat_cong_left.
apply mapid_G_f.
apply trans with (b := (mapid F_f p)! @ p1 q).
apply refl_right_id.
apply concat_cong_right.
apply inv_cong.
apply mapid_F_f.

apply trans with (b := (mapid F_t p)! @ p2 q @ mapid G_t p).
apply @appid with (g := 
  fun q_t : Q_t f => (mapid F_t p)! @ q_t @ mapid G_t p).
apply @transport_id with (f := F_t) (g := G_t).
apply trans with (b := (mapid F_t p)! @ p2 q @ refl d_t).
apply concat_cong_left.
apply mapid_G_t.
apply trans with (b := (mapid F_t p)! @ p2 q).
apply refl_right_id.
apply concat_cong_right.
apply inv_cong.
apply mapid_F_t.
Defined.

End Prelim.

(***********************************************************************)
(***********************************************************************)

(* Prop equality between h_1 and h_2 ====> Two-algebra 2-cell from h_1 to h_2. *)
Lemma prop_eq_to_two_cell : Id h_1 h_2 -> TwoCell h_1 h_2.
Proof.
intros e.
destruct e.
split with (fun x => refl (p1 h_1 x)).
split.
apply refl.
apply refl.
Defined.

(* Two-algebra 2-cell from h_1 to h_2 ====> Prop equality between h_1 and h_2. *)
Lemma two_cell_to_prop_eq : TwoCell h_1 h_2 -> Id h_1 h_2.
Proof.
intros e.
destruct e as [p q].
set (p' := funext (p1 h_1) (p1 h_2) p).
apply dprodext.
split with p'.

apply trans with (b :=
  pair ((appid p' c_f)! @ p1 (p2 h_1)) ((appid p' c_t)! @ p2 (p2 h_1))).
apply @appid with (g := fun q' : P (p1 h_1) =>
  pair ((appid p' c_f)! @ p1 q') ((appid p' c_t)! @ p2 q')).
apply transport_P.
apply prodext.
split.

change (p1 (pair (appid p' c_f ! @ p1 (p2 h_1)) (appid p' c_t ! @ p2 (p2 h_1)))) with
  (appid p' c_f ! @ p1 (p2 h_1)).
apply cancel_left.
apply sym.
apply trans with (b := p c_f @ p1 (p2 h_2)).
apply concat_cong_right.
apply dappid with (g := p).
apply appid_funext.
apply (p1 q).

change (p2 (pair (appid p' c_f ! @ p1 (p2 h_1)) (appid p' c_t ! @ p2 (p2 h_1)))) with
  (appid p' c_t ! @ p2 (p2 h_1)).
apply cancel_left.
apply sym.
apply trans with (b := p c_t @ p2 (p2 h_2)).
apply concat_cong_right.
apply dappid with (g := p).
apply appid_funext.
apply (p2 q).
Defined.

End TwoCells.