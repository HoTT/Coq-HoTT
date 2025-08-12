Require Import Basics.
Require Import Types.Forall Types.Sigma Types.Prod Types.WType.

(** In this file we define indexed W-types. We show that indexed W-types can be reduced to W-types whilst still having definitional computation rules. We also characterize the path space of indexed W-types. This allows us to derive sufficient conditions for an indexed W-type to be truncated. *)

(** This is mostly adapted from Jasper Hugunin's formalization in Coq: https://github.com/jashug/IWTypes *)

(** On a more meta-theoretic note, this partly justifies the use of indexed inductive types in Coq with respect to homotopy type theory. *)

Inductive IW
  (I : Type) (** The indexing type *)
  (A : Type) (** The type of labels / constructors / data *)
  (B : A -> Type) (** The type of arities / arguments / children *)
  (i : A -> I) (** The index map (for labels) *)
  (j : forall x, B x -> I) (** The index map for arguments *)
  : I -> Type :=
| iw_sup (x : A)
    : (forall (y : B x), IW I A B i j (j x y)) -> IW I A B i j (i x).

Definition iw_label {A B I i j} {l : I} (w : IW I A B i j l) : A :=
  match w with
  | iw_sup x y => x
  end.

Definition iw_arity {A B I i j} (l : I) (w : IW I A B i j l)
  : forall (y : B (iw_label w)), IW I A B i j (j (iw_label w) y) :=
  match w with
  | iw_sup x y => y
  end.

Definition path_index_iw_label {A B I i j} (l : I) (w : IW I A B i j l)
  : i (iw_label w) = l.
Proof.
  by destruct w.
Defined.

Definition iw_eta {A B I i j} (l : I) (w : IW I A B i j l)
  : path_index_iw_label l w # iw_sup I A B i j (iw_label w) (iw_arity l w) = w.
Proof.
  by destruct w.
Defined.

(** We have a canonical map from the IW-type to the fiber of the index map *)
Definition iw_to_hfiber_index {A B I i j} (l : I) : IW I A B i j l -> hfiber i l.
Proof.
  intros w.
  exists (iw_label w).
  apply path_index_iw_label.
Defined.

Definition pointwise_paths_ind `{Funext} {A : Type} {B : A -> Type}
  (a : forall x, B x)
  (P : forall b, a == b -> Type)
  (f : P a (fun _ => 1%path))
  {b : forall x, B x} (p : a == b)
  : P b p.
Proof.
  refine (equiv_ind apD10 (P b) _ p).
  intros [].
  exact f.
Defined.

(** * Reduction of indexed W-types to W-types *)

(** Jasper Hugunin found this construction (typecheck un-indexed trees) in "Indexed Containers by Thorsten Altenkirch and Peter Morris". http://www.cs.nott.ac.uk/~psztxa/publ/ICont.pdf
This references the following:
  * M. Abbott, T. Altenkirch, and N. Ghani. Containers - constructing strictly positive types. Theoretical Computer Science, 342:327, September 2005. Applied Semantics: Selected Topics.
  * N. Gambino and M. Hyland. Well-founded trees and dependent polynomial functors. In S. Berardi, M. Coppo, and F. Damiani, editors, types for Proofs and Programs (TYPES 2003), Lecture Notes in Computer Science, 2004
as previous examples of the technique. *)

Section Reduction.

  Context (I : Type) (A : Type) (B : A -> Type)
    (i : A -> I) (j : forall x, B x -> I).

  Fixpoint IsIndexedBy (x : I) (w : W A B) : Type :=
    match w with
    | w_sup a b => (i a = x) * (forall c, IsIndexedBy (j a c) (b c))
    end.

  Definition IW' (x : I) := sig (IsIndexedBy x).

  Definition iw_sup' (x : A) (y : forall z : B x, IW' (j x z)) : IW' (i x)
    := (w_sup A B x (fun a => pr1 (y a)); (idpath, (fun a => pr2 (y a)))).

  (** We can derive the induction principle for IW-types *)
  Definition IW'_ind (P : forall i, IW' i -> Type)
    (S : forall x y, (forall c, P _ (y c)) -> P _ (iw_sup' x y))
    : forall x w, P x w.
  Proof.
    intros x [w r].
    revert w x r.
    induction w as [a b k].
    intros x [p IH].
    destruct p.
    refine (S a (fun c => (b c; IH c)) _).
    intros c.
    apply k.
  Defined.

  (** We have definitional computation rules for this eliminator. *)
  Definition IW'_ind_beta_iw_sup' (P : forall i, IW' i -> Type)
    (S : forall x y, (forall c, P _ (y c)) -> P _ (iw_sup' x y)) x y
    : IW'_ind P S _ (iw_sup' x y) = S x y (fun c => IW'_ind P S _ (y c))
    := idpath.

  (** Showing that IW-types are equivalent to W-types requires funext. *)
  Definition equiv_wtype_iwtype `{Funext} (x : I)
    : IW' x <~> IW I A B i j x.
  Proof.
    snapply equiv_adjointify.
    { rapply (IW'_ind (fun l _ => IW I A B i j l)).
      intros a b c.
      apply iw_sup.
      intros y.
      apply c. }
    { rapply (IW_rect I A B i j (fun l _ => IW' l)).
      intros a b c.
      apply iw_sup'.
      intros y.
      apply c. }
    { rapply (IW_rect I A B i j (fun x y => IW'_ind _ _ x _ = y)).
      cbn; intros a b c.
      apply ap.
      funext y.
      apply c. }
    simpl.
    intro y.
    rapply (IW'_ind (fun x y => IW_rect I A B i j _ _ x _ = y)).
    cbn; intros a b c.
    apply ap.
    funext d.
    apply c.
  Defined.

End Reduction.

(** * Characterization of path types of IW-types. Argument due to Jasper Hugunin. *)

Section Paths.

  Context `{Funext}
    (I : Type) (A : Type) (B : A -> Type)
    (i : A -> I) (j : forall x, B x -> I).

  (** We wish to show that path types of IW-types are IW-types themselves. We do this by showing the path type satisfies the same induction principle as the IW-type hence they are equivalent. *)

  Let I' : Type := {k : I & IW I A B i j k * IW I A B i j k}.
  Let A' : Type := {e : A & (forall c, IW I A B i j (j e c)) * (forall c, IW I A B i j (j e c))}.
  Let B' : A' -> Type := fun X => B X.1.
  Let i' : A' -> I' := functor_sigma i (fun a : A => functor_prod (iw_sup I A B i j a) (iw_sup I A B i j a)).
  Let j' : forall k, B' k -> I' := fun k c => (j k.1 c; (fst k.2 c, snd k.2 c)).

  Let IWPath : I' -> Type := fun x => fst (pr2 x) = snd (pr2 x).

  Definition iwpath_sup (x : A')
    : (forall y : B' x, IWPath (j' x y)) -> IWPath (i' x).
  Proof.
    destruct x as [x [c1 c2]].
    intros y.
    unfold IWPath.
    cbn; apply ap.
    funext l.
    apply y.
  Defined.

  Definition iwpath_sup_refl (x : A) (a : forall c : B x, IW I A B i j (j x c))
    : iwpath_sup (x; (a, a)) (apD10 1) = idpath.
  Proof.
    unfold iwpath_sup.
    rewrite path_forall_1.
    reflexivity.
  Defined.

  Section Ind.

    Context
      (P : forall xab, IWPath xab -> Type)
      (S : forall a b, (forall c, P _ (b c)) -> P (i' a) (iwpath_sup a b)).

    Definition IWPath_ind_refl : forall l a, P (l ; (a, a)) idpath.
    Proof.
      rapply (IW_rect I A B i j (fun l a => P (l; (a, a)) idpath)).
      intros x a q.
      pose (S (x; (a, a)) _ q) as p.
      unfold iwpath_sup in p.
      refine (transport (P (i x; (iw_sup I A B i j x a, iw_sup I A B i j x a))) _ p).
      change (ap (iw_sup I A B i j x) (path_forall a a (apD10 idpath))
        = ap (iw_sup I A B i j x) 1%path).
      refine (ap _ _).
      apply eissect.
    Defined.

    Definition IWPath_ind : forall x p, P x p.
    Proof.
      intros [x [a b]].
      unfold IWPath; cbn.
      destruct p.
      apply IWPath_ind_refl.
    Defined.

    (** The computation rule for the induction principle. *)
    Definition IWPath_ind_beta_iwpath_sup (x : A') (h : forall y : B' x, IWPath (j' x y))
      : IWPath_ind _ (iwpath_sup x h)
        = S x h (fun c => IWPath_ind _ (h c)).
    Proof.
      destruct x as [x [a b]].
      cbv in h.
      refine (_ @ _).
      { refine (_ @ ap _ (eisadj (path_forall _ _) h)).
        refine (paths_ind _
          (fun b p' =>
            paths_ind _ (fun r p'' => P (i x ; (iw_sup I A B i j x a , r)) p'')
              (IWPath_ind_refl (i x) (iw_sup I A B i j x a))
              _ (ap (iw_sup I A B i j x) p')
            = paths_rec (path_forall _ _ (apD10 p'))
                (fun p'' => P (_ ; (_, _)) (ap (iw_sup I A B i j x) p''))
                (S (x ; (a, b)) (apD10 p')
                (fun c => IWPath_ind (_ ; (_, _)) (apD10 p' c)))
                p' (eissect apD10 p'))
          _ _ _).
        exact (transport_compose _ _ _ _)^. }
      by cbn; destruct (eisretr apD10 h).
    Defined.

  End Ind.

  (** The path type of an IW-type is again an IW-type. *)
  Definition equiv_path_iwtype (x : I) (a b : IW I A B i j x)
    : IW I' A' B' i' j' (x; (a, b)) <~> a = b.
  Proof.
    change (IW I' A' B' i' j' (x; (a, b)) <~> IWPath (x; (a,b))).
    snapply equiv_adjointify.
    { intros y.
      induction y as [e f g].
      apply iwpath_sup.
      intros y.
      apply g. }
    { intros y.
      induction y as [e f g] using IWPath_ind.
      apply iw_sup.
      intros y.
      apply g. }
    { intros y; cbn.
      induction y as [a' b' IH] using IWPath_ind.
      rewrite IWPath_ind_beta_iwpath_sup.
      simpl; f_ap.
      funext c.
      apply IH. }
    intros y; cbn.
    induction y as [e f IH].
    rewrite IWPath_ind_beta_iwpath_sup.
    f_ap; funext c.
    apply IH.
  Defined.

  (** ** Characterization of fiber *)

  (** We begin with two auxiliary lemmas that will be explained shortly. *)
  Local Definition adjust_hfiber {X Y} {f : X -> Y} {y z}
    : hfiber f y -> y = z -> hfiber f z
    := fun '(x ; p) => match p with idpath => fun q => (x ; q) end.

  Local Definition adjust_hfiber_idpath {X Y} {f : X -> Y} {y xp}
    : adjust_hfiber (f:=f) xp (idpath : y = y) = xp.
  Proof.
    by destruct xp as [x []].
  Defined.

  (** We wish to show an induction principle coming from the path type of the fiber. However to do this we need to be a bit more general by allowing the elements of the IW-type to differ in label up to equality. This allows us to do prove this induction principle easily, and later we will derive the induction principle where the labels are the same. *)
  Local Definition path_iw_to_hfiber_ind'
    (P : forall (la lb : I) (le : lb = la) (a : IW I A B i j la) (b : IW I A B i j lb),
      iw_to_hfiber_index la a = adjust_hfiber (iw_to_hfiber_index lb b) le -> Type)
    (h : forall x a b,
      P (i x) (i x) idpath (iw_sup I A B i j x a) (iw_sup I A B i j x b) idpath)
    : forall la lb le a b p, P la lb le a b p.
  Proof.
    intros la lb le a b.
    destruct a as [xa cha], b as [xb chb].
    intros p.
    refine (paths_ind _
      (fun _ q => forall chb, P _ _ _ _ (iw_sup _ _ _ _ _ _ chb) q) _ _ p chb).
    intros x.
    apply h.
  Defined.

  (** Induction principle for paths in the fiber. *)
  Local Definition path_iw_to_hfiber_ind
    (P : forall (l : I) (a b : IW I A B i j l),
      iw_to_hfiber_index l a = iw_to_hfiber_index l b -> Type)
    (h : forall x a b,
      P (i x) (iw_sup I A B i j x a) (iw_sup I A B i j x b) idpath)
    : forall l a b p, P l a b p.
  Proof.
    intros l a b p. 
    transparent assert (Q : (forall (la lb : I) (le : lb = la)
      (a : IW I A B i j la) (b : IW I A B i j lb),
      iw_to_hfiber_index la a = adjust_hfiber (iw_to_hfiber_index lb b) le -> Type)).
    { intros la lb le.
      destruct le.
      intros a' b' p'.
      refine (P lb _ _ _).
      exact (p' @ adjust_hfiber_idpath). }
    transparent assert (h' : ((forall (x : A) (a b : forall y : B x, IW I A B i j (j x y)),
        Q (i x) (i x) idpath (iw_sup I A B i j x a) (iw_sup I A B i j x b) idpath))).
    { intros x a' b'.
      apply h. }
    pose (path_iw_to_hfiber_ind' Q h' l l idpath a b (p @ adjust_hfiber_idpath^)) as q.
    refine (transport (P l a b) _ q).
    apply concat_pV_p.
  Defined.

  (** Induction principle for families over hfiber of i' *)
  Local Definition hfiber_ind
    (P : forall l a b, hfiber i' (l; (a, b)) -> Type)
    (h : forall x a b, P (i x) (iw_sup I A B i j x a)
      (iw_sup I A B i j x b) ((x; (a, b)); idpath))
    : forall l a b p, P l a b p.
  Proof.
    intros l a b [[x [y z]] p].
    unfold i', functor_sigma, functor_prod in p; simpl in p.
    revert p.
    refine (equiv_ind (equiv_path_sigma _ _ _) _ _).
    intros [p q]; simpl in p, q.
    destruct p.
    revert q; cbn.
    refine (equiv_ind (equiv_path_prod _ _) _ _).
    cbn; intros [p q].
    destruct p, q.
    apply h.
  Defined.

  Local Definition path_iw_to_hfiber l a b
    : iw_to_hfiber_index l a = iw_to_hfiber_index l b -> hfiber i' (l; (a, b))
    := path_iw_to_hfiber_ind (fun l a b _ => hfiber i' (l ; (a, b)))
        (fun x a b => ((x ; (a, b)); idpath)) l a b.

  Local Definition hfiber_to_path_iw l a b
    : hfiber i' (l; (a, b)) -> iw_to_hfiber_index l a = iw_to_hfiber_index l b
    := hfiber_ind
        (fun l a b _ => iw_to_hfiber_index l a = iw_to_hfiber_index l b)
        (fun x a b => idpath) l a b.

  Local Definition path_iw_to_hfiber_to_path_iw
    : forall l a b p, path_iw_to_hfiber l a b (hfiber_to_path_iw l a b p) = p.
  Proof.
    refine (hfiber_ind (fun l a b p
      => path_iw_to_hfiber l a b (hfiber_to_path_iw l a b p) = p) _).
    intros x a b.
    reflexivity.
  Defined.

  Local Definition hfiber_to_path_iw_to_hfiber
    : forall l a b p, hfiber_to_path_iw l a b (path_iw_to_hfiber l a b p) = p.
  Proof.
    rapply path_iw_to_hfiber_ind.
    intros x a b.
    reflexivity.
  Defined.

  (** The path type of the fibers of [i] is equivalent to the fibers of [i']. *)
  Definition equiv_path_hfiber_index (l : I) (a b : IW I A B i j l)
    : iw_to_hfiber_index l a = iw_to_hfiber_index l b <~> hfiber i' (l; (a, b)).
  Proof.
    srapply equiv_adjointify.
    + apply path_iw_to_hfiber.
    + apply hfiber_to_path_iw.
    + rapply path_iw_to_hfiber_to_path_iw.
    + rapply hfiber_to_path_iw_to_hfiber.
  Defined.

End Paths.

(** Some properties of the (fibers of the) index map [i] hold for the IW-type as well. For example, if [i] is an embedding then the corresponding IW-type is a hprop. *)

(** ** IW-types preserve truncation *)

(** We can show that if the index map is an embedding then the IW-type is a hprop. *)
Instance ishprop_iwtype `{Funext}
  (I : Type) (A : Type) (B : A -> Type)
  (i : A -> I) (j : forall x, B x -> I) {h : IsEmbedding i}
  : forall x, IsHProp (IW I A B i j x).
Proof.
  intros l.
  apply hprop_allpath.
  intros x.
  induction x as [x x' IHx].
  intros y. 
  (** We need to induct on y and at the same time generalize the goal to become a dependent equality. This can be difficult to do with tactics so we just refine the corresponding match statement. All we have done is turn the RHS into a transport over an equality allowing the induction on y to go through. *)
  refine (
    match y in (IW _ _ _ _ _ l)
      return (forall q : l = i x,
        iw_sup I A B i j x x' = q # y)
    with iw_sup y y' => _ end idpath).
  intros q.
  pose (r := @path_ishprop _ (h (i x)) (x; idpath) (y; q)).
  set (r2 := r..2); cbn in r2.
  set (r1 := r..1) in r2; cbn in r1.
  clearbody r1 r2.
  destruct r1.
  simpl in r2.
  destruct r2.
  cbn; f_ap.
  funext a.
  apply IHx.
Defined.

(** Now by induction on truncation indices we show that IW-types are n.+1 truncated if the index maps are also n.+1 truncated. *)
Instance istrunc_iwtype `{Funext}
  (I : Type) (A : Type) (B : A -> Type) (i : A -> I)
  (j : forall x, B x -> I) (n : trunc_index) {h : IsTruncMap n.+1 i} (l : I)
  : IsTrunc n.+1 (IW I A B i j l).
Proof.
  (** We need a general induction hypothesis *)
  revert n I A B i j h l.
  induction n as [|n IHn].
  1: exact ishprop_iwtype.
  intros I A B i j h l.
  apply istrunc_S.
  intros x y.
  refine (istrunc_equiv_istrunc _
    (equiv_path_iwtype I A B i j l x y) (n := n.+1)).
  apply IHn.
  intros [k [a b]].
  (** The crucial step is to characterize the fiber of [i'] which was done previously. *)
  exact (istrunc_equiv_istrunc _
    (equiv_path_hfiber_index I A B i j k a b)).
Defined.

(** ** Decidable equality for IW-types *)

(** If A has decidable paths then it is a hset and therefore equality of sigma types over it are determined by the second component. *)
Local Definition inj_right_pair_on
  {A : Type} {A_dec : DecidablePaths A}
  (P : A -> Type) (x : A) (y y' : P x)
    (H : (x; y) = (x; y')) : y = y'.
Proof.
  apply (equiv_path_sigma _ _ _)^-1%equiv in H.
  destruct H as [p q]; cbn in p, q.
  assert (r : idpath = p) by apply path_ishprop.
  destruct r.
  exact q.
Defined.

(** IW-types have decidable equality if [liftP] holds and the fibers of the indexing map have decidable paths. Notably, if B x is finitely enumerable, then [liftP] holds. *)
Section DecidablePaths.

  Context `{Funext}
    (I : Type) (A : Type) (B : A -> Type) (i : A -> I) (j : forall x, B x -> I)
    (liftP : forall (x : A) (P : B x -> Type),
     (forall c, Decidable (P c)) -> Decidable (forall c, P c))
    (fibers_dec : forall x, DecidablePaths (hfiber i x)).

  Let children_for (x : A) : Type := forall c, IW I A B i j (j x c).
  Let getfib {x} (a : IW I A B i j x) : hfiber i x
    := match a with iw_sup x _ => (x ; idpath) end.
  Let getfib_computes x y children p
    : getfib (paths_rec (i y) _ (iw_sup _ _ _ _ _ y children) (i x) p) = exist _ y p
    := match p
         return getfib (paths_rec _ _ (iw_sup _ _ _ _ _ y children) _ p) = exist _ y p
       with idpath => idpath end.
  Let getfib_plus {x} (a : IW I A B i j x)
    : {f : hfiber i x & children_for (pr1 f)}
    := match a with iw_sup x c => ((x; idpath); c) end.
  Let children_eq (x : A) (c1 c2 : forall c, IW I A B i j (j x c))
    : iw_sup I A B i j x c1 = iw_sup I A B i j x c2 -> c1 = c2
    := fun r => inj_right_pair_on (fun f => children_for (pr1 f))
         (x; idpath) _ _ (ap getfib_plus r).

  Fixpoint decide_eq l (a : IW I A B i j l) : forall b, Decidable (a = b).
  Proof.
    destruct a as [x c1].
    intro b.
    transparent assert (decide_children : (forall c2, Decidable (c1 = c2))).
    { intros c2.
      destruct (liftP x (fun c => c1 c = c2 c) (fun c => decide_eq _ (c1 c) (c2 c)))
        as [p|p].
      + left; by apply path_forall.
      + right; intro h; by apply p, apD10. }
    snrefine (
      match b in (IW _ _ _ _ _ l)
        return
          forall iy : l = i x,
            Decidable (iw_sup I A B i j x c1
              = paths_rec l (IW I A B i j) b (i x) iy)
      with iw_sup y c2 => fun iy : i y = i x => _ end idpath).
    destruct (fibers_dec (i x) (x ; idpath) (y ; iy)) as [feq|fneq].
    + refine (
        match feq in (_ = (y ; iy))
          return forall c2,
            Decidable (iw_sup _ _ _ _ _ x c1
              = paths_rec (i y) (IW I A B i j) (iw_sup _ _ _ _ _ y c2) (i x) iy)
          with idpath => _
        end c2).
      cbn; intros c3.
      destruct (decide_children c3) as [ceq | cneq].
      - left; exact (ap _ ceq).
      - right; intros r; apply cneq.
        exact (children_eq x c1 c3 r).
    + right; intros r; apply fneq.
      exact (ap getfib r @ getfib_computes x y c2 iy).
  Defined.

  Definition decidablepaths_iwtype
    : forall x, DecidablePaths (IW I A B i j x).
  Proof.
    intros x a b.
    apply decide_eq.
  Defined.

End DecidablePaths.
