(** * Connectedness *)
Require Import Basics.
Require Import Types.
Require Import HFiber.

Require Import Extensions.
Require Import Factorization.
Require Export Modalities.Modality.        (* [Export] since the actual definitions of connectedness appear there, in the generality of a modality. *)
Require Import Modalities.Descent.
Require Import Truncations.Core Truncations.SeparatedTrunc.

(** This reduces universe variables in [conn_pointed_type] and [conn_point_elim], which refer to [Unit]. *)
Local Set Universe Minimization ToSet.

Local Open Scope path_scope.
Local Open Scope trunc_scope.

(** There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps should relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

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
Lemma istrunc_extension_along_conn `{Funext} {m n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc (m +2+ n) (P b)}
  (d : forall a:A, P (f a))
  : IsTrunc m (ExtensionAlong f P d).
Proof.
  revert P HP d. simple_induction m m' IH; intros P HP d; simpl in *.
  (* m = –2 *)
  - apply (Build_Contr _ (extension_conn_map_elim n f P d)).
    intros y. apply (allpath_extension_conn_map n); assumption.
    (* m = S m' *)
  - apply istrunc_S.
    intros e e'. exact (istrunc_isequiv_istrunc _ (path_extension e e')).
    (* Magically infers: paths in extensions = extensions into paths, which by induction is [m']-truncated. *)
Defined.

(** ** Connectedness of path spaces *)

Instance isconnected_paths `{Univalence} {n A}
       `{IsConnected n.+1 A} (x y : A)
  : IsConnected n (x = y).
Proof.
  exact (contr_equiv' _ (equiv_path_Tr x y)^-1).
Defined.

(** As a consequence, we have that [ap f] is n-connected when [f] is (n+1)-connected.  See HFiber.v and Loops.v for similar results about truncated maps. *)
Instance isconnmap_ap_isconnmap `{Univalence} (n : trunc_index) {A B : Type}
  (f : A -> B) `{!IsConnMap n.+1 f} (x y : A)
  : IsConnMap n (@ap _ _ f x y)
  := fun p => isconnected_equiv (Tr n) _ (hfiber_ap p)^-1 _.

(** The converse to [isconnected_paths] holds when [A] is merely inhabited. *)
Definition isconnected_isconnected_allpath `{Univalence} (n : trunc_index)
  (A : Type) `{mA : merely A}
  (isc : forall x y : A, IsConnected n (x = y))
  : IsConnected n.+1 A.
Proof.
  strip_truncations; hnf.
  apply (Build_Contr _ (tr mA)); intro a.
  strip_truncations.
  apply equiv_path_Tr, center, isc.
Defined.

(** As a consequence, we get a converse to [isconnmap_ap_isconnmap] for (-1)-connected maps. *)
Definition isconnmap_isconnmap_ap_surj `{Univalence} (n : trunc_index) {A B : Type}
  (f : A -> B) {surj : IsConnMap (-1) f}
  (isc : forall x y : A, IsConnMap n (@ap _ _ f x y))
  : IsConnMap n.+1 f.
Proof.
  intro b.
  apply isconnected_isconnected_allpath.
  1: apply center, surj.
  intros [x p] [y q]; destruct q.
  exact (isconnected_equiv _ _ (hfiber_ap p) _).
Defined.

(** ** Connectivity of pointed types *)

(** The connectivity of a pointed type and (the inclusion of) its point are intimately connected. *)

(** We can't make both of these [Instance]s, as that would result in infinite loops. And the first one is not likely to be useful as an instance, as it requires guessing the point [a0]. *)

Definition conn_pointed_type@{u} {n : trunc_index} {A : Type@{u}} (a0:A)
  `{IsConnMap@{u} n _ _ (unit_name a0)}
  : IsConnected n.+1 A.
Proof.
  apply isconnected_conn_map_to_unit.
  exact (OO_cancelR_conn_map (Tr n.+1) (Tr n) (unit_name a0) (const_tt A)).
Defined.

Definition conn_point_incl `{Univalence} {n : trunc_index} {A : Type} (a0:A)
  `{IsConnected n.+1 A}
  : IsConnMap n (unit_name a0).
Proof.
  rapply (OO_cancelL_conn_map (Tr n.+1) (Tr n) (unit_name a0) (const_tt A)).
  apply O_lex_leq_Tr.
Defined.

(** [conn_point_incl] can be made an instance, but at the time of writing, this doesn't cause any additional goals to be solved compared to making it an immediate hint, so we do the latter. *)
#[export] Hint Immediate conn_point_incl : typeclass_instances.

(** Note that [OO_cancelR_conn_map] and [OO_cancelL_conn_map] (Proposition 2.31 of CORS) generalize the above statements to 2/3 of a 2-out-of-3 property for connected maps, for any reflective subuniverse and its subuniverse of separated types.  If useful, we could specialize that more general form explicitly to truncations. *)

(** To prove an [n]-truncated predicate on an (n+1)-connected, pointed type, it's enough to prove it for the basepoint. *)
Definition conn_point_elim `{Univalence} (n : trunc_index) {A : pType@{u}} `{IsConnected n.+1 A}
           (P : A -> Type@{u}) `{forall a, IsTrunc n (P a)} (p0 : P (point A))
  : forall a, P a.
Proof.
  (* This follows from [conn_point_incl] and [conn_map_elim], but we give a direct proof. *)
  intro a.
  (* Since [A] is [n+1]-connected, [a0 = a] is [n]-connected, which means that [Tr n (a0 = a)] has an element. *)
  pose proof (p := center (Tr n ((point A) = a))).
  strip_truncations.
  exact (p # p0).
Defined.

(** A computation rule for [conn_point_elim_comp]. *)
Definition conn_point_elim_comp `{Univalence} (n : trunc_index) {A : pType@{u}} `{IsConnected n.+1 A}
  (P : A -> Type@{u}) `{forall a, IsTrunc n (P a)} (p0 : P (point A))
  : conn_point_elim n P p0 (point A) = p0.
Proof.
  unfold conn_point_elim.
  (* The center of truncation isn't definitionally [tr 1], but is equal to it: *)
  exact (ap (Trunc_ind _ _) (contr (tr idpath))).
Defined.

(** ** Decreasing connectedness *)

(** An [n.+1]-connected type is also [n]-connected. *)
Definition isconnected_pred n A `{IsConnected n.+1 A}
  : IsConnected n A.
Proof.
  apply isconnected_from_elim; intros C ? f.
  exact (isconnected_elim n.+1 C f).
Defined.

(* As an instance, this would cause loops, but it can be added as an immediate hint. *)
Hint Immediate isconnected_pred : typeclass_instances.

(** A version explicitly using the predecessor function. *)
Definition isconnected_pred' (n : trunc_index) (A : Type) `{IsConnected n A}
  : IsConnected n.-1 A.
Proof.
  destruct n.
  1: unfold IsConnected; simpl; apply istrunc_truncation.
  by apply isconnected_pred.
Defined.

(** A [k]-connected type is [n]-connected, when [k >= n].  We constrain [k] by making it of the form [n +2+ m], which makes the induction go through smoothly. *)
Definition isconnected_pred_add n m A `{H : IsConnected (n +2+ m) A}
  : IsConnected m A.
Proof.
  induction n.
  1: assumption.
  rapply IHn.
Defined.

(** A version with the order of summands swapped, which is sometimes handy, e.g. in the next two results. *)
Definition isconnected_pred_add' n m A `{H : IsConnected (m +2+ n) A}
  : IsConnected m A.
Proof.
  apply (isconnected_pred_add n m).
  destruct (trunc_index_add_comm m n); assumption.
Defined.

(** It follows that an [n.+1]-connected type is also [-1]-connected. *)
Definition merely_isconnected n A `{IsConnected n.+1 A}
  : merely A
  := @center _ (isconnected_pred_add' n (-1) A).

(** And that an [n.+2]-connected type is [0]-connected. *)
Definition is0connected_isconnected (n : trunc_index) A `{IsConnected n.+2 A}
  : IsConnected 0 A
  := isconnected_pred_add' n 0 A.

Definition isconnmap_pred' (n : trunc_index) {A B : Type} (f : A -> B)
  `{IsConnMap n _ _ f}
  : IsConnMap n.-1 f
  := fun b => isconnected_pred' n _.

Definition isconnmap_pred_add n m A B (f : A -> B) `{IsConnMap (n +2+ m) _ _ f}
  : IsConnMap m f.
Proof.
  intro b.
  exact (isconnected_pred_add n m _).
Defined.

(** ** (-2)-connectedness *)

(** Every type is (-2)-connected. *)
Definition isconnected_minus_two A : IsConnected (-2) A
  := istrunc_truncation (-2) A.

(** Every map is (-2)-connected. *)
Definition isconnmap_minus_two {A B : Type} (f : A -> B)
  : IsConnMap (-2) f
  := fun b => isconnected_minus_two _.

Hint Immediate isconnected_minus_two : typeclass_instances.
Hint Immediate isconnmap_minus_two : typeclass_instances.

(** ** 0-connectedness *)

(** To be 0-connected is the same as to be (-1)-connected and that any two points are merely equal.  TODO: This should also be generalized to separated subuniverses (CORS Remark 2.35).  *)
Definition merely_path_is0connected `{Univalence}
           (A : Type) `{IsConnected 0 A} (x y : A)
  : merely (x = y).
Proof.
  (** This follows immediately from [isconnected_paths] above. *)
  rapply center.
Defined.

(** The converse holds when [A] is merely inhabited. *)
Definition is0connected_merely_allpath `{Univalence}
           (A : Type) `{mA : merely A}
           (p : forall (x y:A), merely (x = y))
  : IsConnected 0 A.
Proof.
  apply (isconnected_isconnected_allpath _ _ (mA:=mA)).
  intros x y; hnf.
  exact (contr_inhabited_hprop _ (p x y)).
Defined.

(** The path component of a point [x : X] is connected. *)
Instance is0connected_component {X : Type} (x : X)
  : IsConnected 0 { z : X & merely (z = x) }.
Proof.
  apply (Build_Contr _ (tr (x; tr idpath))).
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
Instance indecomposable_0connected `{Univalence}
       (X : Type) `{IsConnected 0 X}
  : Indecomposable X.
Proof.
  assert (IsConnected (-1) X) by exact (isconnected_pred (-1) X).
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
Instance isconnected_trunc {X : Type} (n m : trunc_index) `{IsConnected n X}
  : IsConnected n (Tr m X).
Proof.
  unfold IsConnected.
  exact (contr_equiv' _ (Trunc_swap n m X)^-1).
Defined.

Section Wedge_Incl_Conn.

(** ** Connectivity of the wedge into the product *)

(** A very useful form of the key lemma [istrunc_extension_along_conn] is the connectivity of the wedge into the product, for a pair of pointed spaces.  In fact this can be formulated without mentioning the wedge per se (so, without requiring HIT’s), since the statement only needs to talk about maps out of the wedge.  The version involving the wedge itself is deduced in Homotopy/Wedge.v.

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
    + exact (conn_point_incl a0).
    + intros a.
      apply (istrunc_extension_along_conn (n := n)).
      * exact (conn_point_incl b0).
      * apply HP.
  - destruct goal_as_extension as [f_eb name_ea_eab].
    assert (ea_eab := name_ea_eab tt); clear name_ea_eab.
    exists (fun a => pr1 (f_eb a)).
    exists (fun b => apD10 (ea_eab ..1) b).
    exists (fun a => pr2 (f_eb a) tt).
    (* The last component is essentially (g' ..2), wrapped in a bit of path-algebra. *)
    apply moveL_Mp.
    rhs_V napply (apD10 (ea_eab ..2) tt).
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
  exact (wedge_incl_elim _ _ _ _ _ f_a0b0).
Defined.
