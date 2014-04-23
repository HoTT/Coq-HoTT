(* -*- mode: coq; mode: visual-line -*- *)

(** * The spheres, in all dimensions. *)

Require Import Overture PathGroupoids Trunc HProp Equivalences types.Sigma types.Forall types.Paths types.Bool Misc hit.Suspension hit.Circle.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(** ** Definition, by iterated suspension. *)

(** To match the usual indexing for spheres, we have to pad the sequence with a dummy term [Sphere minus_two]. *)
Fixpoint Sphere (n : trunc_index) : Type0
  := match n with
       | minus_two => Empty
       | minus_one => Empty
       | trunc_S n' => Susp (Sphere (n'))
     end.

(** ** Explicit equivalences in low dimensions  *)

Definition Sph0_to_Bool : (Sphere 0) -> Bool.
Proof.
  simpl. apply (Susp_rect_nd true false). intros [].
Defined.

Instance isequiv_Sph0_to_Bool : IsEquiv (Sph0_to_Bool) | 0.
Proof.
  apply isequiv_adjointify with (fun b : Bool => if b then North else South).
  intros [ | ]; exact 1.
  unfold Sect. refine (Susp_rect _ 1 1 _). intros [].
Defined.

Definition Sph1_to_S1 : (Sphere (nat_to_trunc_index 1)) -> S1.
Proof.
  apply (Susp_rect_nd base base).
  exact (fun x => if (Sph0_to_Bool x) then loop else 1).
Defined.

Definition S1_to_Sph1 : S1 -> (Sphere (nat_to_trunc_index 1)).
Proof.
  apply (S1_rectnd _ North). exact (merid North @ (merid South)^).
Defined.

Definition isequiv_Sph1_to_S1 : IsEquiv (Sph1_to_S1).
Proof.
  apply isequiv_adjointify with S1_to_Sph1.
    refine (S1_rect _ 1 _).
    refine ((transport_paths_FFlr _ _) @ _).
    unfold S1_to_Sph1; rewrite S1_rectnd_beta_loop.
    rewrite ap_pp, ap_V.
    unfold Sph1_to_S1. simpl. rewrite 2 Susp_comp_nd_merid. simpl.
    hott_simpl.
  refine (Susp_rect (fun x => S1_to_Sph1 (Sph1_to_S1 x) = x)
    1 (merid South) _); intros x.
  refine ((transport_paths_FFlr _ _) @ _).
  unfold Sph1_to_S1; rewrite (Susp_comp_nd_merid x).
  revert x. change (Susp Empty) with (Sphere 0).
  apply (equiv_rect (Sph0_to_Bool ^-1)); intros x.
  case x; simpl.
    2: apply concat_1p.
  unfold S1_to_Sph1; rewrite S1_rectnd_beta_loop.
  refine (whiskerR (concat_p1 _) _ @ _).
  apply moveR_Vp. hott_simpl.
Defined.

(** ** Truncatedness via spheres  *)

(** We show here that a type is n-truncated if and only if every map from the (n+1)-sphere into it is null-homotopic.  (One direction of this is of course the assertion that the (n+1)-sphere is n-connected.) *)

(** TODO: re-type these lemmas in terms of truncation. *)

Fixpoint allnullhomot_trunc {n : trunc_index} {X : Type} `{IsTrunc n X}
  (f : Sphere (trunc_S n) -> X) {struct n}
: NullHomotopy f.
Proof.
  destruct n as [ | n'].
  - simpl in *. exists (center X). intros [ ].
  - apply nullhomot_susp_from_paths.
    apply allnullhomot_trunc; auto with typeclass_instances.
Defined.

Fixpoint trunc_allnullhomot {n : trunc_index} {X : Type}
  (HX : forall (f : Sphere (trunc_S (trunc_S n)) -> X), NullHomotopy f) {struct n}
: IsTrunc (trunc_S n) X.
Proof.
  destruct n as [ | n'].
  (* n = -2 *) apply hprop_allpath.
    intros x0 x1. set (f := (fun b => if (Sph0_to_Bool b) then x0 else x1)).
    set (n := HX f). exact (n.2 North @ (n.2 South)^).
  (* n ≥ -1 *) intros x0 x1.
    apply (trunc_allnullhomot n').
    intro f. apply nullhomot_paths_from_susp, HX.
Defined.
