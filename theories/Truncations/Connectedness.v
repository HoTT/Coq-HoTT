(* -*- mode: coq; mode: visual-line -*-  *)
(** * Connectedness *)
Require Import Basics.
Require Import Types.

Require Import Extensions.
Require Import Factorization.
Require Export Modalities.Modality.        (* [Export] since the actual definitions of connectednes appear there, in the generality of a modality. *)
Require Import Modalities.Descent.
Require Import Truncations.Core Truncations.SeparatedTrunc.

Local Open Scope path_scope.
Local Open Scope trunc_scope.

(** There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps shoud relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

Currently, the translation is therefore as follows:

       HoTT              Traditional       Lurie

Map    (n-1)-connected   n-connected       n-connective
Type   n-connected       n-connected       (n+1)-connective

A handy benchmark: under our indexing, the map [S1 -> 1] is 0-connected but not 1-connected, while the map [1 -> S1] is (–1)–connected but not 0-connected.


One reason for our choice is that this way, the n-truncated and n-connected maps are the modal and modally-connected maps for the n-truncation modality.  Many of the basic lemmas about connected maps are in fact true for any modality, and can be found in [Modality.v].  Thus, here we consider mainly properties that involve the interaction of connectedness at different truncation levels. *)

(** ** Truncatedness of the type of extensions *)

(** A key lemma on the interaction between connectedness and truncatedness: suppose one is trying to extend along an n-connected map, into a k-truncated family of types (k ≥ n).  Then the space of possible extensions is (k–n–2)-truncated.

(Mnemonic for the indexing: think of the base case, where k=n; then we know we can eliminate, so the space of extensions is contractible.)

This lemma is most useful via corollaries like the wedge-inclusion, the wiggly wedge, and their n-ary generalizations. *)
Lemma istrunc_extension_along_conn `{Univalence} {m n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc (m +2+ n) (P b)}
  (d : forall a:A, P (f a))
  : IsTrunc m (ExtensionAlong f P d).
Proof.
  revert P HP d. induction m as [ | m' IH]; intros P HP d; simpl in *.
  (* m = –2 *)
  - exists (extension_conn_map_elim n f P d).
    intros y. apply (allpath_extension_conn_map n); assumption.
    (* m = S m' *)
  - intros e e'. refine (istrunc_isequiv_istrunc _ (path_extension e e')).
  (* magically infers: paths in extensions = extensions into paths, which by induction is m'-truncated. *)
Defined.

(** ** Connectedness of path spaces *)

Global Instance isconnected_paths `{Univalence} {n A}
       `{IsConnected n.+1 A} (x y : A)
  : IsConnected n (x = y).
Proof.
  refine (contr_equiv' _ (equiv_path_Tr x y)^-1).
Defined.

(** ** Connectivity of pointed types *)

(** The connectivity of a pointed type and (the inclusion of) its point are intimately connected. *)

(** We can't make both of these [Instance]s, as that would result in infinite loops. *)
Global Instance conn_pointed_type {n : trunc_index} {A : Type} (a0:A)
       `{IsConnMap n _ _ (unit_name a0)}
  : IsConnected n.+1 A | 1000.
Proof.
  apply isconnected_conn_map_to_unit.
  rapply (OO_cancelR_conn_map (Tr n.+1) (Tr n) (unit_name a0) (fun _:A => tt)).
Defined.

Definition conn_point_incl `{Univalence} {n : trunc_index} {A : Type} (a0:A)
           `{IsConnected n.+1 A}
  : IsConnMap n (unit_name a0).
Proof.
  rapply (OO_cancelL_conn_map (Tr n.+1) (Tr n) (unit_name a0) (fun _:A => tt)).
  apply O_lex_leq_Tr.
Defined.

#[export] Hint Immediate conn_point_incl : typeclass_instances.

(** Note that [OO_cancelR_conn_map] and [OO_cancelL_conn_map] (Proposition 2.31 of CORS) generalize the above statements to 2/3 of a 2-out-of-3 property for connected maps, for any reflective subuniverse and its subuniverse of separated types.  If useful, we could specialize that more general form explicitly to truncations. *)

(** To prove an [n]-truncated predicate on an (n+1)-connected, pointed type, it's enough to prove it for the basepoint. *)
Definition conn_point_elim `{Univalence} (n : trunc_index) {A : pType@{u}} `{IsConnected n.+1 A}
           (P : A -> Type@{u}) `{forall a, IsTrunc n (P a)} (p0 : P (point A))
  : forall a, P a.
Proof.
  (** This follows from [conn_point_incl] and [conn_map_elim], but we give a direct proof. *)
  intro a.
  (** Since [A] is [n+1]-connected, [a0 = a] is [n]-connected, which means that [Tr n (a0 = a)] has an element. *)
  pose proof (p := center _ : Tr n ((point A) = a)).
  strip_truncations.
  exact (p # p0).
Defined.

(** ** Decreasing connectedness *)

(** An [n.+1]-connected type is also [n]-connected.  This obviously can't be an [Instance]! *)
Definition isconnected_pred n A `{IsConnected n.+1 A}
  : IsConnected n A.
Proof.
  apply isconnected_from_elim; intros C ? f.
  refine (isconnected_elim n.+1 C f).
Defined.

(** By induction, an [n.+1]-connected type is also [-1]-connected. *)
Definition merely_isconnected n A `{IsConnected n.+1 A}
  : merely A.
Proof.
  induction n as [|n IHn].
  - apply center; assumption.
  - apply IHn, isconnected_pred; assumption.
Defined.

Definition isconnected_pred_add n m A `{H : IsConnected (n +2+ m) A}
  : IsConnected m A.
Proof.
  induction n.
  1: assumption.
  apply IHn.
  apply isconnected_pred.
  assumption.
Defined.

Definition isconnmap_pred_add n m A B (f : A -> B) `{IsConnMap (n +2+ m) _ _ f}
  : IsConnMap m f.
Proof.
  intro b.
  exact (isconnected_pred_add n m _).
Defined.

(** ** 0-connectedness *)

(** To be 0-connected is the same as to be (-1)-connected and that any two points are merely equal.  TODO: This should also be generalized to separated subuniverses (CORS Remark 2.35).  *)
Definition merely_path_is0connected `{Univalence}
           (A : Type) `{IsConnected 0 A} (x y : A)
  : merely (x = y).
Proof.
  (** This follows immediately from [isconnected_paths] above. *)
  rapply center.
Defined.

Definition is0connected_merely_allpath `{Univalence}
           (A : Type) `{merely A}
           (p : forall (x y:A), merely (x = y))
  : IsConnected 0 A.
Proof.
  strip_truncations.
  apply (contr_inhabited_hprop).
  - apply hprop_allpath; intros z w.
    strip_truncations.
    exact (equiv_path_Tr z w (p z w)).
  - apply tr; assumption.
Defined.

(** The path component of a point [x : X] is connected. *)
Global Instance is0connected_component {X : Type} (x : X)
  : IsConnected 0 { z : X & merely (z = x) }.
Proof.
  exists (tr (x; tr idpath)).
  rapply Trunc_ind; intros [Z p].
  strip_truncations.
  apply (ap tr).
  rapply path_sigma_hprop.
  exact p^.
Defined.

(** Any two points in a path component are merely equal.  This follows from [merely_path_is0connected], but this proof doesn't need univalence. *)
Definition merely_path_component {X : Type} {x : X}
  (z1 z2 : { z : X & merely (z = x) })
  : merely (z1 = z2).
Proof.
  destruct z1 as [z1 p1], z2 as [z2 p2].
  strip_truncations.
  apply tr.
  apply path_sigma_hprop; cbn.
  exact (p1 @ p2^).
Defined.

(** The path component of a point [x : X] is equivalent to the image of the constant map [Unit -> X] at [x]. *)
Definition equiv_component_image_unit {X : Type} (x : X)
  : { z : X & merely (z = x) } <~> image (Tr (-1)) (unit_name x).
Proof.
  unfold image; simpl.
  apply equiv_functor_sigma_id; intros z; simpl.
  apply Trunc_functor_equiv; unfold hfiber.
  refine ((equiv_contr_sigma _)^-1 oE _).
  apply equiv_path_inverse.
Defined.

(** 0-connected types are indecomposable *)
Global Instance indecomposable_0connected `{Univalence}
       (X : Type) `{IsConnected 0 X}
  : Indecomposable X.
Proof.
  assert (IsConnected (-1) X) by refine (isconnected_pred (-1) X).
  constructor.
  - intros A B f.
    assert (z := center (merely X) : merely X); generalize z.
    refine (Trunc_rec _).
    + apply ishprop_sum; try exact _.
      intros l r. strip_truncations.
      exact (not_is_inl_and_inr' (f z) (l z) (r z)).
    + intros x.
      remember (f x) as y eqn:p.
      destruct y as [a|b]; [ left | right ]; intros x'.
      all:assert (q := merely_path_is0connected X x x');
        strip_truncations.
      all:refine (transport _ (ap f q) _).
      all:exact (transport _ p^ tt).
  - intros nx.
    apply (Trunc_rec (n := -1) nx).
    exact (center (merely X)).
Defined.

(* Truncation preserves connectedness. Note that this is for different levels. *)
Global Instance isconnected_trunc {X : Type} (n m : trunc_index) `{IsConnected n X}
  : IsConnected n (Tr m X).
Proof.
  unfold IsConnected.
  srapply (contr_equiv' _ (Trunc_swap n m X)^-1).
Defined.

Section Wedge_Incl_Conn.

(** ** Connectivity of the wedge into the product.

A very useful form of the key lemma [istrunc_extension_along_conn] is the connectivity of the wedge into the product, for a pair of pointed spaces.  In fact this can be formulated without mentioning the wedge per se (so, without requiring HIT’s), since the statement only needs to talk about maps out of the wedge.

Once again, we believe that the type of the conclusion is an hprop (though we do not prove it) — essentially because it is wrapping up an elimination principle and its corresponding computation rule — and so we make the proof of this result opaque. *)

Context `{Univalence}
  {m n : trunc_index}
  {A : Type} (a0 : A) `{IsConnected m.+1 A}
  {B : Type} (b0 : B) `{IsConnected n.+1 B}
  (P : A -> B -> Type) {HP : forall a b, IsTrunc (m +2+ n) (P a b)}
  (f_a0 : forall b:B, P a0 b)
  (f_b0 : forall a:A, P a b0)
  (f_a0b0 : f_a0 b0 = f_b0 a0).

Corollary isconn_wedge_incl
  : { f : forall a b, P a b
  & { e_a0 : forall b, f a0 b = f_a0 b
  & { e_b0 : forall a, f a b0 = f_b0 a
  & e_b0 a0 = (e_a0 b0) @ f_a0b0 }}}.
Proof.
  assert (goal_as_extension :
    ExtensionAlong (unit_name a0)
      (fun a => ExtensionAlong (unit_name b0) (P a) (unit_name (f_b0 a)))
      (unit_name (f_a0 ; (unit_name f_a0b0)))).
  - apply (extension_conn_map_elim m).
    + apply (conn_point_incl a0).
    + intros a.
      apply (istrunc_extension_along_conn (n := n)).
      * apply (conn_point_incl b0).
      * apply HP.
  - destruct goal_as_extension as [f_eb name_ea_eab].
    assert (ea_eab := name_ea_eab tt); clear name_ea_eab.
    exists (fun a => pr1 (f_eb a)).
    exists (fun b => apD10 (ea_eab ..1) b).
    exists (fun a => pr2 (f_eb a) tt).
    (* The last component is essentially (g' ..2), wrapped in a bit of path-algebra. *)
    apply moveL_Mp.
    apply (concatR (apD10 (ea_eab ..2) tt)).
    set (ea := ea_eab ..1). generalize ea; simpl. clear ea_eab ea. intros.
    rewrite transport_arrow. rewrite transport_const. rewrite transport_paths_Fl.
    exact 1%path.
Qed.

(** It is easier to apply the above result with its components separated. *)
Definition wedge_incl_elim : forall a b, P a b
  := isconn_wedge_incl.1.

Definition wedge_incl_comp1 : forall b, wedge_incl_elim a0 b = f_a0 b
  := isconn_wedge_incl.2.1.

Definition wedge_incl_comp2 : forall a, wedge_incl_elim a b0 = f_b0 a
  := isconn_wedge_incl.2.2.1.

Definition wedge_incl_comp3
  : wedge_incl_comp2 a0 = (wedge_incl_comp1 b0) @ f_a0b0
  := isconn_wedge_incl.2.2.2.

End Wedge_Incl_Conn.

Definition wedge_incl_elim_uncurried `{Univalence}
  {m n : trunc_index}
  {A : Type} (a0 : A) `{IsConnected m.+1 A}
  {B : Type} (b0 : B) `{IsConnected n.+1 B}
  (P : A -> B -> Type) {HP : forall a b, IsTrunc (m +2+ n) (P a b)}
  (fs : {f_a0 : forall b:B, P a0 b
        & { f_b0 : forall a:A, P a b0
        & f_a0 b0 = f_b0 a0 }})
  : forall (a : A) (b : B), P a b.
Proof.
  destruct fs as [f_a0 [f_b0 f_a0b0]].
  refine (wedge_incl_elim _ _ _ _ _ f_a0b0).
Defined.
