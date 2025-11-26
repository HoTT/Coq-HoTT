Require Import HoTT.Basics HoTT.Types.
Require Import Extensions HFiber Truncations NullHomotopy Limits.Pullback.
Require Import Descent Lex Separated.

(** We construct "canonical" binary meets of reflective subuniverses (that is, whose underlying subuniverse is an intersection), without assuming accessibility.  In particular, we will show:

1. Given two reflective subuniverses L and O, if [L O X] is [O]-modal, then it is a reflection into the canonical meet.  In particular, this is always the case if [L] preserves [O]-modal types; this is Theorem 3.30 of RSS.

1. If L and O are lex modalities satisfying an additional "composability" condition, then the composite functor [L o O] converges to a reflection into the canonical meet after n+2 applications when applied to an n-type for some finite n.

The latter gives in particular a synthetic approach to higher sheafification (stack completion).  As described at https://ncatlab.org/nlab/show/plus+construction+on+presheaves, for any site C the topos of presheaves on its Grothendieck topology is cohesive and even totally connected, so that its shape and sharp modalities are both lex.  Their canonical meet is the topos of sheaves for the given topology, and the composite functor [shape o sharp] is the usual "plus construction" on (higher) presheaves.  Thus, we recover synthetically the result that an n-truncated type can be stackified by (n+2) applications of the plus construction.  We also refer to [L o O] as a "plus construction" in the general case of reflective subuniverses.  *)

Section RSUMeet.
  Context (L O : ReflectiveSubuniverse).

  (** The canonical meet of two subuniverses is their intersection. *)

  Definition Meet : Subuniverse.
  Proof.
    unshelve econstructor.
    - intros X; exact (In L X * In O X).
    - intros ? X; exact _.
    - intros T U [? ?] f feq; split; exact (inO_equiv_inO _ f).
  Defined.

  #[export] Instance inO_inmeet_l (X : Type) `{im : In Meet X} : In L X := fst im.
  #[export] Instance inO_inmeet_r (X : Type) `{im : In Meet X} : In O X := snd im.

  (** The basic tool in studying its reflectivity is the "plus construction" that applies the two reflectors in sequence. *)

  Definition Plus (X : Type) := L (O X).

  #[export] Instance inO_plus_l (X : Type) : In L (Plus X) := _.

  (** This is not necessarily a reflector, but it is a well-pointed endofunctor. *)

  Definition to_plus (X : Type) : X -> Plus X
    := to L (O X) o to O X.

  Definition plus_functor {X Y : Type} (f : X -> Y) : Plus X -> Plus Y
    := O_functor L (O_functor O f).

  Definition to_plus_natural {X Y : Type} (f : X -> Y)
    : plus_functor f o to_plus X == to_plus Y o f.
  Proof.
    intros x.
    unfold plus_functor, to_plus.
    refine (to_O_natural L (O_functor O f) (to O X x) @ _).
    apply ap.
    apply to_O_natural.
  Defined.

  Definition wellpointed_plus (X : Type)
    : to_plus (Plus X) == plus_functor (to_plus X).
  Proof.
    rapply (@O_indpaths L).
    intros ox.
    unfold to_plus, plus_functor; cbn.
    refine (_ @ (to_O_natural L _ ox)^).
    apply ap.
    revert ox; apply O_indpaths; intros x.
    exact ((to_O_natural O _ x)^).
  Defined.

  (** Moreover, it has the desired factorization property of a reflector (though it may not belong to the meet subuniverse itself). *)

  Definition ooextendable_plus {X Y : Type} `{In Meet Y}
    : ooExtendableAlong (to_plus X) (fun _  => Y).
  Proof.
    apply (ooextendable_compose _ (to O X) (to L (O X)));
      rapply extendable_to_O.
  Defined.

  Definition plus_rec {P Q : Type} `{In Meet Q} (f : P -> Q)
    : Plus P -> Q
    := (fst (ooextendable_plus 1%nat) f).1.

  Definition plus_rec_beta {P Q : Type} `{In Meet Q} (f : P -> Q) (x : P)
    : plus_rec f (to_plus P x) = f x
    := (fst (ooextendable_plus 1%nat) f).2 x.

  Definition plus_indpaths {P Q : Type} `{In Meet Q} (g h : Plus P -> Q)
             (p : g o to_plus P == h o to_plus P)
    : g == h
    := (fst (snd (ooextendable_plus 2%nat) g h) p).1.

  Definition plus_indpaths_beta {P Q : Type} `{In Meet Q} (g h : Plus P -> Q)
             (p : g o (to_plus P) == h o (to_plus P)) (x : P)
    : plus_indpaths g h p (to_plus P x) = p x
    := (fst (snd (ooextendable_plus 2%nat) g h) p).2 x.

  (** Moreover, its fixed points, as a pointed endofunctor, are the types in the meet. *)

  Definition isequiv_plus_inmeet (X : Type) `{In Meet X} : IsEquiv (to_plus X).
  Proof.
    rapply (isequiv_compose (to O X) (to L (O X))).
    apply isequiv_to_O_inO.
    exact (inO_equiv_inO X (to O X)).
  Defined.

  Definition inmeet_isequiv_plus (X : Type) `{IsEquiv _ _ (to_plus X)} : In Meet X.
  Proof.
    split.
    - exact (inO_equiv_inO (Plus X) (to_plus X)^-1).
    - srapply inO_to_O_retract.
      + exact ((to_plus X)^-1 o (to L (O X))).
      + intros x; apply (eissect (to_plus X)).
  Defined.

  (** It follows that if [Plus X] ever *does* lie in the meet, then it is a reflection. *)

  #[export] Instance prereflects_plus_inO (X : Type) `{In O (Plus X)}
    : PreReflects Meet X.
  Proof.
    unshelve econstructor.
    - exact (Plus X).
    - split; exact _.
    - apply to_plus.
  Defined.

  #[export] Instance reflects_plus_inO (X : Type) `{In O (Plus X)}
    : Reflects Meet X.
  Proof.
    constructor; intros; exact ooextendable_plus.
  Defined.

  (** Recalling that a type is connected for a reflective subuniverse if and only if its reflector is nullhomotopic, we define a type to be "plus-connected" if its map to plus is nullhomotopic.  If the meet is reflective, this coincides with connectedness for that reflective subuniverse. *)

  Definition PlusConnected (X : Type) := NullHomotopy (to_plus X).

  Definition plusconnected_equiv {X Y : Type} (f : X <~> Y)
    : PlusConnected X -> PlusConnected Y.
  Proof.
    intros [px e].
    exists (plus_functor f px); intros y.
    refine (_ @ ap (plus_functor f) (e (f^-1 y))).
    rewrite to_plus_natural.
    symmetry; apply ap, eisretr.
  Defined.

  (** Similarly, we say a map is plus-connected if all of its fibers are. *)

  Definition PlusConnMap {X Y : Type} (f : X -> Y) := forall y, PlusConnected (hfiber f y).

End RSUMeet.

(** Let's now assume we are trying to intersect two lex modalities. *)

Section LexMeet.
  Context (L O : Modality) `{Lex L} `{Lex O}.

  (** The plus construction, being a composite of two lex functors, is also lex.  Thus, it preserves path-types. *)
  Definition plus_path {X : Type} (x y : X)
    : Plus L O (x = y) <~> (to_plus L O X x = to_plus L O X y).
  Proof.
    refine (equiv_path_O L (to O X x) (to O X y) oE _).
    apply equiv_O_functor.
    rapply equiv_path_O.
  Defined.

  Definition plus_path_to_plus {X : Type} (x y : X)
    : plus_path x y o to_plus L O (x = y) == @ap _ _ (to_plus L O X) x y.
  Proof.
    intros p; unfold plus_path, to_plus, equiv_path_O, equiv_path_OO, path_OO.
    cbn.
    rewrite to_O_natural.
    rewrite O_rec_beta.
    rewrite (ap_compose (to O X) (to L (O X))).
    apply ap.
    apply O_rec_beta.
  Defined.

  (** This implies that plus-connected types are closed under path-spaces. *)
  Definition plusconnected_path {X : Type} (x y : X)
             (pc : PlusConnected L O X) : PlusConnected L O (x = y).
  Proof.
    unfold PlusConnected in *.
    apply (cancelL_nullhomotopy_equiv _ (plus_path x y)).
    apply (nullhomotopy_homotopic (fun u => (plus_path_to_plus x y u)^)).
    apply nullhomotopy_ap; assumption.
  Defined.

  (** And hence plus-connected maps are closed under diagonals. *)
  Definition plusconnmap_diagonal {X Y : Type} (f : X -> Y)
    : PlusConnMap L O f -> PlusConnMap L O (diagonal f).
  Proof.
    intros pc p.
    refine (plusconnected_equiv L O (hfiber_diagonal f p)^-1 _).
    apply plusconnected_path, pc.
  Defined.

  (** The plus-construction also preserves fibers. *)
  Definition plus_hfiber {X Y : Type} (f : X -> Y) (y : Y)
    : Plus L O (hfiber f y) <~> hfiber (plus_functor L O f) (to_plus L O Y y).
  Proof.
    refine (equiv_O_functor_hfiber L (O_functor O f) (to O Y y) oE _).
    apply equiv_O_functor.
    rapply equiv_O_functor_hfiber.
  Defined.

  Definition plus_hfiber_to_plus {X Y : Type} (f : X -> Y) (y : Y)
    : plus_hfiber f y o to_plus L O (hfiber f y)
      == functor_hfiber (fun u => (to_plus_natural L O f u)^) y.
  Proof.
    intros [x q]; unfold plus_hfiber, to_plus.
    cbn.
    rewrite to_O_natural.
    rewrite O_functor_hfiber_natural.
    unfold O_functor_hfiber, functor_hfiber, functor_sigma; cbn.
    rewrite O_rec_beta; cbn.
    apply ap.
    unfold to_plus_natural.
    rewrite !inv_V, ap_pp, concat_p_pp.
    apply whiskerL.
    rewrite <- ap_compose.
    reflexivity.
  Defined.

  (** And pullbacks. *)
  Definition equiv_plus_pullback {A B C : Type} (f : B -> A) (g : C -> A)
    : Plus L O (Pullback f g) <~> Pullback (plus_functor L O f) (plus_functor L O g).
  Proof.
    refine (equiv_O_pullback L (O_functor O f) (O_functor O g) oE _).
    apply equiv_O_functor.
    rapply equiv_O_pullback.
  Defined.

  (** And diagonals. *)
  Definition diagonal_plus_functor {A B : Type} (f : A -> B)
    : diagonal (plus_functor L O f) == equiv_plus_pullback f f o plus_functor L O (diagonal f).
  Proof.
    intros x.
    refine (diagonal_O_functor L (O_functor O f) x @ _).
    apply (ap (equiv_O_pullback L (O_functor O f) (O_functor O f))).
    refine (O_functor_homotopy L _ _ (diagonal_O_functor O f) x @ _).
    unfold plus_functor.
    exact (O_functor_compose L _ _ x).
  Defined.

  (** Recall that a modality is characterized by connectedness of the units.  Analogously, we can now prove that the plus-units are all plus-connected.  This is equivalently a sort of coherence axiom for the homotopy [wellpointed_plus], that when precomposed with [to_plus] it becomes [to_plus_natural]. *)
  Definition plusconnmap_to_plus (X : Type) : PlusConnMap L O (to_plus L O X).
  Proof.
    intros y; unfold PlusConnected.
    apply (cancelL_nullhomotopy_equiv _ (plus_hfiber (to_plus L O X) y)).
    apply (nullhomotopy_homotopic (fun u => (plus_hfiber_to_plus (to_plus L O X) y u)^)).
    unfold NullHomotopy, hfiber.
    unshelve refine ((y ; _) ; _).
    { symmetry; apply wellpointed_plus. }
    intros [x p]; destruct p.
    unfold functor_hfiber, functor_sigma; cbn.
    apply ap.
    rewrite inv_V, concat_p1.
    unfold wellpointed_plus.
    rewrite !O_indpaths_beta.
    rewrite inv_pp, ap_V, !inv_V.
    reflexivity.
  Defined.

  (** Recall also (from [nsep_iff_trunc_to_O]) that a type is n-separated for a lex modality [O] if and only if its [O]-unit is an n-truncated map.  We can now prove the analogous fact for the plus-construction.  We state this using [MapIn (Tr n)] instead of [IsTrunc n] because we have more useful lemmas for [MapIn]. *)
  Definition nsep_iff_trunc_plus (n : trunc_index) (X : Type)
    : In (nSep n (Meet L O)) X <-> MapIn (Tr n) (to_plus L O X).
  Proof.
    revert X; induction n as [|n IHn]; intros X; split; intros H.
    - apply contr_map_isequiv.
      rapply isequiv_plus_inmeet.
    - apply inmeet_isequiv_plus.
      rapply isequiv_contr_map.
    - apply istruncmap_from_ap; intros x y.
      apply istruncmap_mapinO_tr.
      pose (i := fst (IHn _) (H x y)).
      exact (mapinO_homotopic _ _ (plus_path_to_plus x y)).
    - intros x y.
      apply (snd (IHn (x = y))).
      pose (i := istruncmap_ap n (to_plus L O X) x y).
      apply mapinO_tr_istruncmap in i.
      apply (mapinO_homotopic _ ((plus_path x y)^-1 o (@ap _ _ (to_plus L O X) x y))).
      { intros p; apply moveR_equiv_V; symmetry; apply plus_path_to_plus. }
      rapply mapinO_compose.
  Defined.

  (** We now make one more assumption, that the plus-construction inverts plus-connected embeddings.  In the case of the plus-construction for stacks, this corresponds roughly to the "local character" condition on a Grothendieck topology. *)
  Context (composing : forall (X Y : Type) (f : X -> Y)
                              (fe : IsEmbedding f) (fc : PlusConnMap L O f),
              IsEquiv (plus_functor L O f)).

  (** This implies, by induction, that the plus-construction decreases the truncation-level of any finitely truncated plus-connected map. *)
  Definition istruncmap_plus_functor {n : trunc_index} {X Y : Type} (f : X -> Y)
             `{MapIn (Tr n.+1) _ _ f} (pc : PlusConnMap L O f)
    : MapIn (Tr n) (plus_functor L O f).
  Proof.
    generalize dependent f; revert X Y; induction n as [|n IHn]; intros X Y f ? pc.
    { apply mapinO_tr_istruncmap, contr_map_isequiv, composing; assumption. }
    pose (O_eq_Tr n).
    apply (mapinO_O_leq (Sep (Tr n)) _), mapinO_from_diagonal.
    napply (mapinO_homotopic (Tr n) _ (fun u => (diagonal_plus_functor f u)^)).
    apply mapinO_compose.
    2:rapply mapinO_isequiv.
    apply IHn.
    - apply mapinO_diagonal.
      pose (O_eq_Tr n.+1).
      rapply (mapinO_O_leq _ (Sep (Tr n.+1))).
    - apply plusconnmap_diagonal; assumption.
  Defined.

  (** It follows, by applying this to the plus-unit and using well-pointedness, that the plus-construction on *types* decreases their plus-separatedness. *)
  Definition nsep_plus (n : trunc_index) (X : Type) `{In (nSep n.+1 (Meet L O)) X}
    : In (nSep n (Meet L O)) (Plus L O X).
  Proof.
    apply nsep_iff_trunc_plus.
    nrefine (mapinO_homotopic _ _ (fun u => (wellpointed_plus L O X u)^)).
    apply mapinO_tr_istruncmap, istruncmap_plus_functor.
    - apply istruncmap_mapinO_tr, nsep_iff_trunc_plus; assumption.
    - apply plusconnmap_to_plus.
  Defined.

  (** Therefore, if a type starts out as n-plus-separated, then n+2 applications of the plus-construction suffice to make it (-2)-plus-separated, i.e. in the meet subuniverse.  Hence it has a reflection. *)
  #[export] Instance prereflects_plus_nsep (n : trunc_index) (X : Type) `{In (nSep n (Meet L O)) X}
    : PreReflects (Meet L O) X.
  Proof.
    generalize dependent X; induction n as [|n IHn]; intros X ?.
    { rapply prereflects_in. }
    specialize (IHn (Plus L O X) (nsep_plus n X)).
    unshelve econstructor.
    - exact (O_reflector (Meet L O) (Plus L O X)).
    - exact _.
    - exact (to (Meet L O) (Plus L O X) o to_plus L O X).
  Defined.

  #[export] Instance reflects_plus_nsep (n : trunc_index) (X : Type) `{In (nSep n (Meet L O)) X}
    : Reflects (Meet L O) X.
  Proof.
    generalize dependent X; induction n as [|n IHn]; intros X ?.
    { rapply reflects_in. }
    specialize (IHn (Plus L O X) (nsep_plus n X)).
    constructor; intros.
    apply (ooextendable_compose _ (to_plus L O X) (to (Meet L O) (Plus L O X))).
    - apply (@extendable_to_O (Meet L O) (Plus L O X)); assumption.
    - rapply ooextendable_plus.
  Defined.

End LexMeet.
