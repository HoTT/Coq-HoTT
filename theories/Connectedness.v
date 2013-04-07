(* -*- mode: coq; mode: visual-line -*-  *)
(** * Connectedness *)

Require Import Overture PathGroupoids Fibrations Equivalences Trunc Truncations.
Require Import Forall Sigma Paths Unit Arrow Universe.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Connectedness *)

(** There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps shoud relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

Currently, the translation is therefore as follows:

       HoTT              Traditional       Lurie

Map    (n-1)-connected   n-connected       n-connective
Type   n-connected       n-connected       (n+1)-connective

A handy benchmark: under our indexing, the map [S1 -> 1] is 0-connected but not 1-connected, while the map [1 -> S1] is (–1)–connected but not 0-connected. *)

(** Connectedness of a type (however indexed) can be defined in two equivalent ways: quantifying over all maps into suitably truncated types, or by considering just the universal case, the truncation of the type itself.

The latter requires HIT’s, but keeps the type [IsConnected] small; the former, which we use for now, requires only core Coq, but blows up the size (universe level) of [IsConnected], since it quantifies over types. 

Question: is there a definition of connectedness that neither blows up the universe level, nor requires HIT’s? *)

Class IsConnected (n : trunc_index) (A : Type)
 := isconnected_elim :> 
      forall (C : Type) `{IsTrunc n C} (f : A -> C),
        { c:C & forall a:A, f a = c }.

Definition iscontr_truncation_from_isconnected {n} {A} `{IsConnected n A}
  : Contr (Truncation n A).
Proof.
  set (nh := isconnected_elim (Truncation n A) (@truncation_incl n A)).
  exists (nh .1).
  apply Truncation_rect. apply trunc_succ.
  intros; apply symmetry, (nh .2).
Defined.

Instance isconnected_from_iscontr_truncation {n} {A} `{Contr (Truncation n A)}
  : IsConnected n A.
Proof.
  intros C ? f.
  set (ff := Truncation_rect_nondep f).
  exists (ff (center _)).
  intros a. apply symmetry, (ap ff (contr (truncation_incl _))).
Defined.

(** Connectedness of a map can again be defined in two equivalent ways: by connectedness of its fibers (as types), or by the lifting property/elimination principle against truncated types.  We use the former; the equivalence with the latter is given below in [conn_map_elim], [conn_map_comp], and [conn_map_from_extension_elim]. *)

Class IsConnMap (n : trunc_index) {A B : Type} (f : A -> B)
  := isconnected_hfiber_conn_map :>
       forall b:B, IsConnected n (hfiber f b).
(* TODO: question — why do the implicit arguments of this seem not to work, i.e. seem to (often) need to be given explicitly? *)

(** n-connected maps are orthogonal to n-truncated maps (i.e. familes of n-truncated types). *)
Definition conn_map_elim {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
: forall b:B, P b.
Proof.
  intros b. 
  apply isconnected_elim.
    apply HP.
    instantiate (1 := b). intros [a p]. 
    exact (transport P p (d a)).
Defined.

Definition conn_map_comp {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
: forall a:A, conn_map_elim f P d (f a) = d a.
Proof.
  intros a. unfold conn_map_elim.
  set (fibermap := (fun a0p : hfiber f (f a)
    => let (a0, p) := a0p in transport P p (d a0))).
  destruct (isconnected_elim (P (f a)) fibermap) as [x e].
  change (d a) with (fibermap (a;1)).
  apply inverse, e.
Defined.

Instance conn_point_incl `{Univalence} {n : trunc_index} {A : Type} (a0:A)
 `{IsConnected (trunc_S n) A} : IsConnMap n (unit_name a0).
Proof.
  intros a.
Admitted.

Instance conn_pointed_type {n : trunc_index} {A : Type} (a0:A)
 `{IsConnMap n _ _ (unit_name a0)} : IsConnected (trunc_S n) A.
Proof.
  intros C HC f. exists (f a0).
(* TODO: try to use [refine] or similar to get more concise? *)
  apply (conn_map_elim (unit_name a0)).
    intros b; apply HC.  
  apply (fun _ => 1).
Defined.

(** ** Extensions 

Elimination properties can be nicely phrased as the existence of extensions along maps of sections. This is just the traditional categorical language of fillers for commutative squares, restricted to the case where the bottom of the square is the identity; type-theoretically, this approach is slightly more convenient. *)

Section Extensions.

Context `{Funext} `{Univalence}.

(* TODO: consider naming for [ExtensionAlong] and subsequent lemmas.  As a name for the type itself, [Extension] or [ExtensionAlong] seems great; but resultant lemma names such as [path_extension] (following existing naming conventions) are rather misleading. *)

(** This elimination rule (and others) can be seen as saying that, given a fibration over the codomain and a section of it over the domain, there is some *extension* of this to a section over the whole domain. *)
Definition ExtensionAlong {A B : Type} (f : A -> B)
  (P : B -> Type) (d : forall x:A, P (f x))
:= { s : forall y:B, P y & forall x:A, s (f x) = d x }.

Definition path_extension {A B : Type} {f : A -> B}
  {P : B -> Type} {d : forall x:A, P (f x)}
  (ext ext' : ExtensionAlong f P d)
: (ExtensionAlong f
    (fun y => projT1 ext y = projT1 ext' y)
    (fun x => projT2 ext x @ (projT2 ext' x)^))
-> ext = ext'.
Proof.
(* Note: written with liberal use of [compose], to facilitate later proving that it’s an equivalance. *)
  apply (compose (path_sigma_uncurried _ _ _)).
  apply (functor_sigma (path_forall (ext .1) (ext' .1))). intros p.
  apply (compose (path_forall _ _)). unfold pointwise_paths.
  apply (functor_forall idmap). intros x.
  apply (compose (B := (p (f x))^ @ (ext .2 x) = (ext' .2 x))).
    apply concat.
    path_via ((apD10 (path_forall _ _ p) (f x))^ @ ext .2 x).
    assert (transp_extension : forall p : ext .1 = ext' .1,
      (transport (fun (s : forall y : B, P y) => forall x : A, s (f x) = d x)
        p (ext .2) x
      = ((apD10 p (f x))^ @ ext .2 x))).
      destruct ext as [g gd], ext' as [g' gd']; simpl.
      intros q; destruct q; simpl.
      apply inverse, concat_1p.
    apply transp_extension.
    apply whiskerR, ap, apD10_path_forall.
  apply (compose (moveR_Vp _ _ _)).
  apply (compose (moveL_pM _ _ _)).
  exact inverse.
Defined.

Instance isequiv_path_extension {A B : Type} {f : A -> B}
  {P : B -> Type} {d : forall x:A, P (f x)}
  (ext ext' : ExtensionAlong f P d)
: IsEquiv (path_extension ext ext').
Proof.
  apply @isequiv_compose.
    Focus 2. apply @isequiv_path_sigma.
  apply @isequiv_functor_sigma.
    apply @isequiv_path_forall.
  intros a. apply @isequiv_compose.
    Focus 2. apply @isequiv_path_forall.
  apply (@isequiv_functor_forall _).
    apply isequiv_idmap.
  intros x. apply @isequiv_compose.
  apply @isequiv_compose.
    apply @isequiv_compose.
      apply isequiv_path_inverse.
      apply isequiv_moveL_pM.
    apply isequiv_moveR_Vp.
  apply isequiv_concat_l.
Qed.
(** Note: opaque, since this term is big enough that using its computational content will probably be pretty intractable. *)

Lemma extension_conn_map_elim {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) `{forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
: ExtensionAlong f P d.
Proof.
  exists (conn_map_elim f P d).
  apply conn_map_comp.
Defined.

Lemma allpath_extension_conn_map {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) `{forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
  (e e' : ExtensionAlong f P d)
: e = e'.
Proof.
  apply path_extension.
  apply (extension_conn_map_elim (n := n)); try assumption.
  intros b. apply trunc_succ.
Defined.

(** Conceptually, this proof can be seen as an instance of the fact that a left adjoint (here, pullback) preserves a left class of maps if the right adjoint (here, dependent product) preserves the right class. *)
Lemma conn_map_from_extension_elim  {n : trunc_index}
  {A B : Type} (f : A -> B)
: (forall (P : B -> Type) `{forall b:B, IsTrunc n (P b)}
          (d : forall a:A, P (f a)),
    ExtensionAlong f P d)
  -> (IsConnMap n f).
Proof.
  intros Hf b X ? d.
  set (P := fun (b':B) => (b' = b) -> X). 
  assert (forall b', IsTrunc n (P b')) by (intros; apply trunc_forall).
  set (dP := (fun (a:A) (p:f a = b) => (d (a;p)))
          : forall a:A, P (f a)).
  set (e := Hf P _ dP).
  exists (e .1 b 1).
  intros [a p]. apply symmetry. path_via (e .1 (f a) p).
    Focus 2. exact (ap10 (e.2 a) p).
  (* TODO: Can the following be simplified? A version of [ap] for binary functions would be one approach. *)
  set (e1 := fun (bb : {b':B & b' = b}) => (e.1 (bb.1) (bb.2))).
  change (e.1 b 1) with (e1 (b;1)).
  change (e.1 (f a) p) with (e1 (f a; p)).
  apply ap. apply path_sigma with (p^). simpl.
  refine (transport_paths_l _ _ @ _). hott_simpl.
Defined.

(** A key lemma on the interaction between connectedness and truncatedness: suppose one is trying to extend along an n-connected map, into a k-truncated family of types (k ≥ n).  Then the space of possible extensions is (k–n–2)-truncated.

(Mnemonic for the indexing: think of the base case, where k=n; then we know we can eliminate, so the space of extensions is contractible.) 

This lemma is most useful via corollaries like the wedge-inclusion, the wiggly wedge, and their n-ary generalizations. *)
Lemma istrunc_extension_along_conn {m n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc (m -2+ n) (P b)}
  (d : forall a:A, P (f a))
: IsTrunc m (ExtensionAlong f P d).
Proof.
  revert P HP d. induction m as [ | m' IH]; intros P HP d; simpl in *.
  (* m = –2 *)
  exists (extension_conn_map_elim f P d).
  intros y. apply (allpath_extension_conn_map (n := n)); assumption.
  (* m = S m' *)
  intros e e'. refine (trunc_equiv (path_extension e e')).
  (* magically infers: paths in extensions = extensions into paths,
                       which by induction is m'-truncated. *)
Defined.

End Extensions.


Section Wedge_Incl_Conn.

(** ** Connectivity of the wedge into the product.

A very useful form of the key lemma [istrunc_extension_along_conn] is the connectivity of the wedge into the product, for a pair of pointed spaces.  In fact this can be formulated without mentioning the wedge per se (so, without requiring HIT’s), since the statement only needs to talk about maps out of the wedge.

Once again, we believe that the type of the conclusion is an hprop (though we do not prove it) — essentially because it is wrapping up an elimination principle and its corresponding computation rule — and so we make the proof of this result opaque. *)

Context `{Funext} `{Univalence}
  {m n : trunc_index}
  (A : Type) (a0 : A) `{IsConnected (trunc_S m) A} 
  (B : Type) (b0 : B) `{IsConnected (trunc_S n) B} 
  (P : A -> B -> Type) {HP : forall a b, IsTrunc (m -2+ n) (P a b)}
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
    apply (extension_conn_map_elim (n := m)).
      apply (conn_point_incl a0).
    intros a.
    apply (istrunc_extension_along_conn (n := n)).
      apply (conn_point_incl b0).
    apply HP.
  destruct goal_as_extension as [f_eb name_ea_eab].
  assert (ea_eab := name_ea_eab tt); clear name_ea_eab.
  exists (fun a => projT1 (f_eb a)).
  exists (fun b => apD10 (ea_eab ..1) b).
  exists (fun a => projT2 (f_eb a) tt).
(* The last component is essentially (g' ..2), wrapped in a bit of path-algebra. *)
  apply moveL_Mp.
  apply (concatR (apD10 (ea_eab ..2) tt)).
  set (ea := ea_eab ..1). generalize ea; simpl. clear ea_eab ea. intros.
  rewrite transport_arrow. rewrite transport_const. rewrite transport_paths_Fl.
  exact 1.
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
