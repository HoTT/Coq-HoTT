From HoTT Require Import Basics Types.
Require Import WildCat.Core WildCat.Coproducts.
Require Import Cubical.DPath.
Require Import Spaces.List.Core Spaces.List.Theory.
Require Import Colimits.Pushout.
Require Import Truncations.Core Truncations.SeparatedTrunc.
Require Import Algebra.Groups.Group.

Local Open Scope list_scope.
Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** In this file we define the amalgamated free product of a span of group homomorphisms as a HIT. *)

(** We wish to define the amalgamated free product of a span of group homomorphisms f : G -> H, g : G -> K as the following HIT:

<<
  HIT M(f,g)
   | amal_eta : list (H + K) -> M(f,g)
   | mu_H : forall (x y : list (H + K)) (h1 h2 : H),
      amal_eta (x ++ [inl h1, inl h2] ++ y) = amal_eta (x ++ [inl (h1 * h2)] ++ y)
   | mu_K : forall (x y : list (H + K)) (k1 k2 : K),
      amal_eta (x ++ [inr k1, inr k2] ++ y) = amal_eta (x ++ [inr (k1 * k2)] ++ y)
   | tau : forall (x y : list (H + K)) (z : G),
      amal_eta (x ++ [inl (f z)] ++ y) = amal_eta (x ++ [inr (g z)] ++ y)
   | omega_H : forall (x y : list (H + K)),
      amal_eta (x ++ [inl mon_unit] ++ y) = amal_eta (x ++ y)
   | omega_K : forall (x y : list (H + K)),
      amal_eta (x ++ [inr mon_unit] ++ y) = amal_eta (x ++ y).
>>

  We will build this HIT up successively out of coequalizers. *)

(** We will call M [amal_type] and prefix all the constructors with [amal_] (for amalgamated free product). *)

Section AmalgamatedFreeProduct.

  Context {G H K : Group}
    (f : GroupHomomorphism G H) (g : GroupHomomorphism G K).

  Local Definition Words : Type := list (H + K).

  Local Fixpoint word_inverse (x : Words) : Words.
  Proof.
    destruct x as [|x xs].
    1: exact nil.
    destruct x as [h|k].
    + exact ((word_inverse xs) ++ [inl h^]).
    + exact ((word_inverse xs) ++ [inr k^]).
  Defined.

  (** Inversion changes order of concatenation. *)
  Local Definition word_inverse_ww (x y : Words)
    : word_inverse (x ++ y) = word_inverse y ++ word_inverse x.
  Proof.
    induction x as [|x xs].
    1: symmetry; apply app_nil.
    simpl.
    destruct x; rhs napply app_assoc; f_ap.
  Defined.

  (** There are five source types for the path constructors. We will construct this HIT as the colimit of five forks going into [Words]. We can bundle up this colimit as a single coequalizer. *)

  (** Source types of path constructors *)
  Local Definition pc1 : Type := Words * H * H * Words.
  Local Definition pc2 : Type := Words * K * K * Words.
  Local Definition pc3 : Type := Words * G * Words.
  Local Definition pc4 : Type := Words * Words.
  Local Definition pc5 : Type := Words * Words.

  (** End points of the first path constructor *)
  Local Definition m1 : pc1 -> Words.
  Proof.
    intros [[[x h1] h2] y].
    exact (x ++ (inl h1 :: [inl h2]) ++ y).
  Defined.

  Local Definition m1' : pc1 -> Words.
  Proof.
    intros [[[x h1] h2] y].
    exact (x ++ [inl (h1 * h2)] ++ y).
  Defined.

  (** End points of the second path construct *)
  Local Definition m2 : pc2 -> Words.
  Proof.
    intros [[[x k1] k2] y].
    exact (x ++ (inr k1 :: [inr k2]) ++ y).
  Defined.

  Local Definition m2' : pc2 -> Words.
  Proof.
    intros [[[x k1] k2] y].
    exact (x ++ [inr (k1 * k2)] ++ y).
  Defined.

  (** End points of the third path constructor *)
  Local Definition m3 : pc3 -> Words.
  Proof.
    intros [[x z] y].
    exact (x ++ [inl (f z)] ++ y).
  Defined.

  Local Definition m3' : pc3 -> Words.
  Proof.
    intros [[x z] y].
    exact (x ++ [inr (g z)] ++ y).
  Defined.

  (** End points of the fourth path constructor *)
  Local Definition m4 : pc4 -> Words.
  Proof.
    intros [x y].
    exact (x ++ [inl mon_unit] ++ y).
  Defined.

  Local Definition m4' : pc4 -> Words.
  Proof.
    intros [x y].
    exact (x ++ y).
  Defined.

  (** End points of the fifth path constructor *)
  Local Definition m5 : pc5 -> Words.
  Proof.
    intros [x y].
    exact (x ++ [inr mon_unit] ++ y).
  Defined.

  Local Definition m5' : pc5 -> Words.
  Proof.
    intros [x y].
    exact (x ++ y).
  Defined.

  (** We can then define maps going into words consisting of the corresponding endpoints of the path constructors. *)
  Local Definition map1 : pc1 + pc2 + pc3 + pc4 + pc5 -> Words.
  Proof.
    intros [[[[x|x]|x]|x]|x].
    + exact (m1 x).
    + exact (m2 x).
    + exact (m3 x).
    + exact (m4 x).
    + exact (m5 x).
  Defined.

  Local Definition map2 : pc1 + pc2 + pc3 + pc4 + pc5 -> Words.
  Proof.
    intros [[[[x|x]|x]|x]|x].
    + exact (m1' x).
    + exact (m2' x).
    + exact (m3' x).
    + exact (m4' x).
    + exact (m5' x).
  Defined.

  (** Finally we can define our type as the 0-truncation of the coequalizer of these maps *)
  Definition amal_type : Type := Tr 0 (Coeq map1 map2).

  (** We can define the constructors *)

  Definition amal_eta : Words -> amal_type := tr o coeq.

  Definition amal_mu_H (x y : Words) (h1 h2 : H)
    : amal_eta (x ++ [inl h1, inl h2] ++ y) = amal_eta (x ++ [inl (h1 * h2)] ++ y).
  Proof.
    unfold amal_eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inl (inl (x,h1,h2,y)))))).
  Defined.

  Definition amal_mu_K (x y : Words) (k1 k2 : K)
    : amal_eta (x ++ [inr k1, inr k2] ++ y) = amal_eta (x ++ [inr (k1 * k2)] ++ y).
  Proof.
    unfold amal_eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inl (inr (x,k1,k2,y)))))).
  Defined.

  Definition amal_tau (x y : Words) (z : G)
    : amal_eta (x ++ [inl (f z)] ++ y) = amal_eta (x ++ [inr (g z)] ++ y).
  Proof.
    unfold amal_eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inr (x,z,y))))).
  Defined.

  Definition amal_omega_H (x y : Words)
    : amal_eta (x ++ [inl mon_unit] ++ y) = amal_eta (x ++ y).
  Proof.
    unfold amal_eta.
    apply path_Tr, tr.
    exact (cglue (inl (inr (x,y)))).
  Defined.

  Definition amal_omega_K (x y : Words)
    : amal_eta (x ++ [inr mon_unit] ++ y) = amal_eta (x ++ y).
  Proof.
    unfold amal_eta.
    apply path_Tr, tr.
    exact (cglue (inr (x,y))).
  Defined.

  (** Now we can derive the dependent eliminator *)

  Definition amal_type_ind (P : amal_type -> Type) `{forall x, IsHSet (P x)}
    (e : forall w, P (amal_eta w))
    (mh : forall (x y : Words) (h1 h2 : H),
      DPath P (amal_mu_H x y h1 h2) (e (x ++ [inl h1, inl h2] ++ y)) (e (x ++ [inl (h1 * h2)] ++ y)))
    (mk : forall (x y : Words) (k1 k2 : K),
      DPath P (amal_mu_K x y k1 k2) (e (x ++ [inr k1, inr k2] ++ y)) (e (x ++ [inr (k1 * k2)] ++ y)))
    (t : forall (x y : Words) (z : G),
      DPath P (amal_tau x y z) (e (x ++ [inl (f z)] ++ y)) (e (x ++ [inr (g z)] ++ y)))
    (oh : forall (x y : Words),
      DPath P (amal_omega_H x y) (e (x ++ [inl mon_unit] ++ y)) (e (x ++ y)))
    (ok : forall (x y : Words),
      DPath P (amal_omega_K x y) (e (x ++ [inr mon_unit] ++ y)) (e (x ++ y)))
    : forall x, P x.
  Proof.
    snapply Trunc_ind; [exact _|].
    snapply Coeq_ind.
    1: exact e.
    intro a.
    destruct a as [ [ [ [a | a ] | a] | a ] | a ].
    + destruct a as [[[x h1] h2] y].
      apply dp_compose.
      exact (mh x y h1 h2).
    + destruct a as [[[x k1] k2] y].
      apply dp_compose.
      exact (mk x y k1 k2).
    + destruct a as [[x z] y].
      apply dp_compose.
      exact (t x y z).
    + destruct a as [x y].
      apply dp_compose.
      exact (oh x y).
    + destruct a as [x y].
      apply dp_compose.
      exact (ok x y).
  Defined.

  Definition amal_type_ind_hprop (P : amal_type -> Type) `{forall x, IsHProp (P x)}
    (e : forall w, P (amal_eta w))
    : forall x, P x.
  Proof.
    snapply amal_type_ind.
    1: exact _.
    1: exact e.
    all: intros; apply path_ishprop.
  Defined.

  (** From which we can derive the non-dependent eliminator / recursion principle *)
  Definition amal_type_rec (P : Type) `{IsHSet P} (e : Words -> P)
    (eh : forall (x y : Words) (h1 h2 : H),
      e (x ++ [inl h1, inl h2] ++ y) = e (x ++ [inl (h1 * h2)] ++ y))
    (ek : forall (x y : Words) (k1 k2 : K),
      e (x ++ [inr k1, inr k2] ++ y) = e (x ++ [inr (k1 * k2)] ++ y))
    (t : forall (x y : Words) (z : G),
      e (x ++ [inl (f z)] ++ y) = e (x ++ [inr (g z)] ++ y))
    (oh : forall (x y : Words), e (x ++ [inl mon_unit] ++ y) = e (x ++ y))
    (ok : forall (x y : Words), e (x ++ [inr mon_unit] ++ y) = e (x ++ y))
    : amal_type -> P.
  Proof.
    snapply amal_type_ind.
    1: exact _.
    1: exact e.
    all: intros; apply dp_const.
    1: apply eh.
    1: apply ek.
    1: apply t.
    1: apply oh.
    apply ok.
  Defined.

  (** Now for the group structure *)

  (** We will frequently need to use that path types in [amal_type] are hprops, and so it speeds things up to create this instance.  It is fast to use [_] here, but when the terms are large below, it becomes slower. *)
  Local Instance ishprop_paths_amal_type (x y : amal_type) : IsHProp (x = y) := _.

  (** The group operation is concatenation of the underlying list. Most of the work is spent showing that it respects the path constructors. *)
  Local Instance sgop_amal_type : SgOp amal_type.
  Proof.
    intros x y; revert x.
    snapply amal_type_rec; only 1: exact _; intros x; revert y.
    { snapply amal_type_rec; only 1: exact _; intros y.
      1: exact (amal_eta (x ++ y)).
      { intros z h1 h2.
        refine (ap amal_eta _ @ _ @ ap amal_eta _^).
        1,3: apply app_assoc.
        rapply amal_mu_H. }
      { intros z k1 k2.
        refine (ap amal_eta _ @ _ @ ap amal_eta _^).
        1,3: apply app_assoc.
        rapply amal_mu_K. }
      { intros w z.
        refine (ap amal_eta _ @ _ @ ap amal_eta _^).
        1,3: apply app_assoc.
        apply amal_tau. }
      { intros z.
        refine (ap amal_eta _ @ _ @ ap amal_eta _^).
        1,3: apply app_assoc.
        apply amal_omega_H. }
      { intros z.
        refine (ap amal_eta _ @ _ @ ap amal_eta _^).
        1,3: apply app_assoc.
        apply amal_omega_K. } }
    { intros r y h1 h2; revert r.
      rapply amal_type_ind_hprop.
      intros z;
      change (amal_eta ((x ++ [inl h1, inl h2] ++ y) ++ z)
        = amal_eta ((x ++ [inl (h1 * h2)] ++ y) ++ z)).
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      refine (ap amal_eta (ap (app x) _)^ @ _ @ ap amal_eta (ap (app x) _)).
      1,3: apply app_assoc.
      apply amal_mu_H. }
    { intros r y k1 k2; revert r.
      rapply amal_type_ind_hprop.
      intros z;
      change (amal_eta ((x ++ [inr k1, inr k2] ++ y) ++ z)
        = amal_eta ((x ++ [inr (k1 * k2)] ++ y) ++ z)).
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      refine (ap amal_eta (ap (app x) _)^ @ _ @ ap amal_eta (ap (app x) _)).
      1,3: apply app_assoc.
      apply amal_mu_K. }
    { intros r y z; revert r.
      rapply amal_type_ind_hprop.
      intros w;
      change (amal_eta ((x ++ [inl (f z)] ++ y) ++ w)
        = amal_eta ((x ++ [inr (g z)] ++ y) ++ w)).
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      refine (ap amal_eta (ap (app x) _)^ @ _ @ ap amal_eta (ap (app x) _)).
      1,3: apply app_assoc.
      apply amal_tau. }
    { intros r z; revert r.
      rapply amal_type_ind_hprop.
      intros w;
      change (amal_eta ((x ++ [inl mon_unit] ++ z) ++ w) = amal_eta ((x ++ z) ++ w)).
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      refine (ap amal_eta (ap (app x) _)^ @ _).
      1: apply app_assoc.
      apply amal_omega_H. }
    { intros r z; revert r.
      rapply amal_type_ind_hprop.
      intros w;
      change (amal_eta ((x ++ [inr mon_unit] ++ z) ++ w) = amal_eta ((x ++ z) ++ w)).
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      refine (ap amal_eta (ap (app x) _)^ @ _).
      1: apply app_assoc.
      apply amal_omega_K. }
  Defined.

  (** The identity element is the empty list *)
  Local Instance monunit_amal_type : MonUnit amal_type.
  Proof.
    exact (amal_eta nil).
  Defined.

  Local Instance inverse_amal_type : Inverse amal_type.
  Proof.
    srapply amal_type_rec.
    { intros w.
      exact (amal_eta (word_inverse w)). }
    { hnf; intros x y h1 h2.
      refine (ap amal_eta _ @ _ @ ap amal_eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1: apply word_inverse_ww.
      { refine (word_inverse_ww _ _ @ _).
        apply ap; simpl.
        rapply (ap (fun s => [s])).
        apply ap.
        apply inverse_sg_op. }
      simpl.
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      apply amal_mu_H. }
    { hnf; intros x y k1 k2.
      refine (ap amal_eta _ @ _ @ ap amal_eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1: apply word_inverse_ww.
      { refine (word_inverse_ww _ _ @ _).
        apply ap; simpl.
        rapply (ap (fun s => [s])).
        apply ap.
        apply inverse_sg_op. }
      simpl.
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      apply amal_mu_K. }
    { hnf; intros x y z.
      refine (ap amal_eta _ @ _ @ ap amal_eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1,2: cbn; refine (ap _ _).
      1,2: rapply (ap (fun s => [s])).
      1,2: apply ap.
      1,2: symmetry; apply grp_homo_inv.
      refine (ap amal_eta _^ @ _ @ ap amal_eta _).
      1,3: apply app_assoc.
      apply amal_tau. }
    { hnf; intros x z.
      refine (ap amal_eta _ @ _ @ ap amal_eta _^).
      1,3: apply word_inverse_ww.
      refine (ap amal_eta _ @ _).
      { refine (ap (fun s => s ++ _) _).
        apply word_inverse_ww. }
      refine (ap amal_eta _^ @ _).
      1: apply app_assoc.
      simpl.
      rewrite inverse_mon_unit.
      apply amal_omega_H. }
    { hnf; intros x z.
      refine (ap amal_eta _ @ _ @ ap amal_eta _^).
      1,3: apply word_inverse_ww.
      refine (ap amal_eta _ @ _).
      { refine (ap (fun s => s ++ _) _).
        apply word_inverse_ww. }
      refine (ap amal_eta _^ @ _).
      1: apply app_assoc.
      simpl.
      rewrite inverse_mon_unit.
      apply amal_omega_K. }
  Defined.

  Local Instance associative_sgop_m : Associative sg_op.
  Proof.
    intros x y.
    rapply amal_type_ind_hprop; intro z; revert y.
    rapply amal_type_ind_hprop; intro y; revert x.
    rapply amal_type_ind_hprop; intro x.
    napply (ap amal_eta).
    rapply app_assoc.
  Defined.

  Local Instance leftidentity_sgop_amal_type : LeftIdentity sg_op mon_unit.
  Proof.
    rapply amal_type_ind_hprop; intro x.
    reflexivity.
  Defined.

  Local Instance rightidentity_sgop_amal_type : RightIdentity sg_op mon_unit.
  Proof.
    rapply amal_type_ind_hprop; intro x.
    napply (ap amal_eta).
    napply app_nil.
  Defined.

  Lemma amal_eta_word_concat_Vw (x : Words) : amal_eta (word_inverse x ++ x) = mon_unit.
  Proof.
    induction x as [|x xs].
    1: reflexivity.
    destruct x as [h|k].
    + change (amal_eta (word_inverse ([inl h] ++ xs) ++ [inl h] ++ xs) = mon_unit).
      rewrite word_inverse_ww.
      rewrite <- app_assoc.
      refine (amal_mu_H _ _ _ _ @ _).
      rewrite left_inverse.
      rewrite amal_omega_H.
      exact IHxs.
    + change (amal_eta (word_inverse ([inr k] ++ xs) ++ [inr k] ++ xs) = mon_unit).
      rewrite word_inverse_ww.
      rewrite <- app_assoc.
      refine (amal_mu_K _ _ _ _ @ _).
      rewrite left_inverse.
      rewrite amal_omega_K.
      exact IHxs.
  Defined.

  Lemma amal_eta_word_concat_wV (x : Words) : amal_eta (x ++ word_inverse x) = mon_unit.
  Proof.
    induction x as [|x xs].
    1: reflexivity.
    destruct x as [h|k].
    + cbn.
      rewrite app_assoc.
      change (amal_eta ([inl h]) * amal_eta ((xs ++ word_inverse xs)) * amal_eta ([inl h^]) = mon_unit).
      rewrite IHxs.
      rewrite rightidentity_sgop_amal_type.
      rewrite <- (app_nil (cons _ _)).
      change (amal_eta (([inl h] ++ [inl h^]) ++ nil) = mon_unit).
      rewrite <- app_assoc.
      change (amal_eta (nil ++ [inl h] ++ [inl h^] ++ nil) = mon_unit).
      refine (amal_mu_H _ _ _ _ @ _).
      refine (_ @ _).
      { apply ap, ap.
        rapply (ap (fun x => x ++ _)).
        rapply (ap (fun x => [x])).
        apply ap.
        apply right_inverse. }
      apply amal_omega_H.
    +  cbn.
      rewrite app_assoc.
      change (amal_eta ([inr k]) * amal_eta ((xs ++ word_inverse xs)) * amal_eta ([inr k^]) = mon_unit).
      rewrite IHxs.
      rewrite rightidentity_sgop_amal_type.
      rewrite <- (app_nil (cons _ _)).
      change (amal_eta (([inr k] ++ [inr k^]) ++ nil) = mon_unit).
      rewrite <- app_assoc.
      change (amal_eta (nil ++ [inr k] ++ [inr k^] ++ nil) = mon_unit).
      refine (amal_mu_K _ _ _ _ @ _).
      refine (_ @ _).
      { apply ap, ap.
        rapply (ap (fun x => x ++ _)).
        rapply (ap (fun x => [x])).
        apply ap.
        apply right_inverse. }
      apply amal_omega_K.
  Defined.

  Local Instance leftinverse_sgop_amal_type : LeftInverse (.*.) (^) mon_unit.
  Proof.
    rapply amal_type_ind_hprop; intro x.
    apply amal_eta_word_concat_Vw.
  Defined.

  Local Instance rightinverse_sgop_amal_type : RightInverse (.*.) (^) mon_unit.
  Proof.
    rapply amal_type_ind_hprop; intro x.
    apply amal_eta_word_concat_wV.
  Defined.

  Definition AmalgamatedFreeProduct : Group.
  Proof.
    snapply (Build_Group amal_type); repeat split; exact _.
  Defined.

End AmalgamatedFreeProduct.

Arguments amal_eta {G H K f g} x.
Arguments amal_mu_H {G H K f g} x y.
Arguments amal_mu_K {G H K f g} x y.
Arguments amal_tau {G H K f g} x y z.
Arguments amal_omega_H {G H K f g} x y.
Arguments amal_omega_K {G H K f g} x y.

Section RecInd.

  Context {G H K : Group}
    {f : GroupHomomorphism G H} {g : GroupHomomorphism G K}.

  (** Using foldr. It's important that we use foldr as foldl is near impossible to reason about. *)
  Definition AmalgamatedFreeProduct_rec' (X : Group)
    (h : GroupHomomorphism H X) (k : GroupHomomorphism K X)
    (p : h o f == k o g)
    : AmalgamatedFreeProduct f g -> X.
  Proof.
    srapply amal_type_rec.
    { intro w.
      refine (fold_right _ _ w).
      { intros [l|r] x.
        + exact (h l * x).
        + exact (k r * x). }
      exact mon_unit. }
    { intros x y h1 h2; hnf.
      rewrite ?fold_right_app.
      f_ap.
      simpl.
      rewrite simple_associativity.
      f_ap.
      symmetry.
      exact (grp_homo_op h h1 h2). }
    { intros x y k1 k2; hnf.
      rewrite ?fold_right_app.
      f_ap.
      simpl.
      rewrite simple_associativity.
      f_ap.
      symmetry.
      exact (grp_homo_op k k1 k2). }
    { intros x y z; hnf.
      rewrite ?fold_right_app.
      f_ap; simpl; f_ap. }
    { intros x y; hnf.
      rewrite ?fold_right_app.
      f_ap. simpl. rewrite grp_homo_unit.
      rapply left_identity. }
    { intros x y; hnf.
      rewrite ?fold_right_app.
      f_ap. simpl. rewrite grp_homo_unit.
      rapply left_identity. }
  Defined.

  Local Instance issemigrouppreserving_AmalgamatedFreeProduct_rec'
    (X : Group) (h : GroupHomomorphism H X) (k : GroupHomomorphism K X)
    (p : h o f == k o g)
    : IsSemiGroupPreserving (AmalgamatedFreeProduct_rec' X h k p).
  Proof.
    intros x; srapply amal_type_ind_hprop; intro y; revert x;
    srapply amal_type_ind_hprop; intro x; simpl.
    rewrite fold_right_app.
    set (s := (fold_right
     (fun X0 : H + K => match X0 with
                        | inl l => fun x0 : X => h l * x0
                        | inr r => fun x0 : X => k r * x0
                        end) mon_unit y)).
    induction x as [|a x].
    1: symmetry; apply left_identity.
    simpl.
    rewrite IHx.
    destruct a; apply simple_associativity.
  Qed.

  Definition AmalgamatedFreeProduct_rec (X : Group)
    (h : H $-> X) (k : K $-> X)
    (p : h $o f $== k $o g)
    : AmalgamatedFreeProduct f g $-> X.
  Proof.
    snapply Build_GroupHomomorphism.
    1: srapply (AmalgamatedFreeProduct_rec' X h k p).
    exact _.
  Defined.

  Definition amal_inl : H $-> AmalgamatedFreeProduct f g.
  Proof.
    snapply Build_GroupHomomorphism.
    { intro x.
      exact (amal_eta [inl x]). }
    intros x y.
    rewrite <- (app_nil [inl (x * y)]).
    rewrite <- (amal_mu_H nil nil x y).
    rewrite app_nil.
    reflexivity.
  Defined.

  Definition amal_inr : K $-> AmalgamatedFreeProduct f g.
  Proof.
    snapply Build_GroupHomomorphism.
    { intro x.
      exact (amal_eta [inr x]). }
    intros x y.
    rewrite <- (app_nil [inr (x * y)]).
    rewrite <- (amal_mu_K nil nil x y).
    rewrite app_nil.
    reflexivity.
  Defined.
  
  Definition amal_glue : amal_inl $o f $== amal_inr $o g.
  Proof.
    hnf; apply (amal_tau nil nil).
  Defined.

  Theorem equiv_amalgamatedfreeproduct_rec `{Funext} (X : Group)
    : {h : H $-> X & {k : K $-> X & h $o f $== k $o g }}
      <~> (AmalgamatedFreeProduct f g $-> X).
  Proof.
    snapply equiv_adjointify.
    1: intros [h [k p]]; exact (AmalgamatedFreeProduct_rec X h k p).
    { intros r.
      exists (grp_homo_compose r amal_inl).
      exists (grp_homo_compose r amal_inr).
      intro x.
      apply (ap r).
      simpl.
      rewrite <- (app_nil [inl (f x)]).
      rewrite <- (app_nil [inr (g x)]).
      exact (amal_tau nil nil x). }
    { intros r.
      apply equiv_path_grouphomomorphism.
      srapply amal_type_ind_hprop.
      intro x.
      induction x as [|a x].
      1: symmetry; exact (grp_homo_unit r).
      simpl in *.
      rewrite IHx.
      destruct a; symmetry;
      rapply (grp_homo_op r (amal_eta [_]) (amal_eta x)). }
    intro hkp.
    simpl.
    tapply (equiv_ap' (equiv_sigma_prod
      (fun hk : (H $-> X) * (K $-> X)
        => fst hk o f == snd hk o g)) _ _)^-1%equiv.
    rapply path_sigma_hprop.
    destruct hkp as [h [k p]].
    apply path_prod; cbn;
    apply equiv_path_grouphomomorphism;
    intro; simpl; rapply right_identity.
  Defined.
  
  Definition amalgamatedfreeproduct_ind_hprop (P : AmalgamatedFreeProduct f g -> Type)
    `{forall x, IsHProp (P x)}
    (l : forall a, P (amal_inl a)) (r : forall b, P (amal_inr b))
    (Hop : forall x y, P x -> P y -> P (x * y))
    : forall x, P x.
  Proof.
    rapply amal_type_ind_hprop.
    intros w.
    simple_list_induction w a w IH.
    - rewrite <- (amal_omega_H nil nil).
      apply l.
    - destruct a as [a|b].
      + change (P (amal_inl a * amal_eta w)).
        by apply Hop.
      + change (P (amal_inr b * amal_eta w)).
        by apply Hop.
  Defined.

  Definition amalgamatedfreeproduct_ind_homotopy {P : Group}
    {k k' : AmalgamatedFreeProduct f g $-> P}
    (l : k $o amal_inl $== k' $o amal_inl)
    (r : k $o amal_inr $== k' $o amal_inr)
    : k $== k'.
  Proof.
    rapply (amalgamatedfreeproduct_ind_hprop _ l r).
    intros x y; napply grp_homo_op_agree.
  Defined.

  Definition equiv_amalgamatedfreeproduct_ind_homotopy `{Funext} {P : Group}
    (k k' : AmalgamatedFreeProduct f g $-> P)
    : (k $o amal_inl $== k' $o amal_inl) * (k $o amal_inr $== k' $o amal_inr)
      <~> k $== k'.
  Proof.
    rapply equiv_iff_hprop.
    - exact (uncurry amalgamatedfreeproduct_ind_homotopy).
    - intros p; split; exact (p $@R _).
  Defined.

End RecInd.

Definition FreeProduct (G H : Group) : Group
  := AmalgamatedFreeProduct (grp_trivial_rec G) (grp_trivial_rec H).

Definition freeproduct_inl {G H : Group} : GroupHomomorphism G (FreeProduct G H)
  := amal_inl.

Definition freeproduct_inr {G H : Group} : GroupHomomorphism H (FreeProduct G H)
  := amal_inr.

Definition freeproduct_ind_hprop {G H} (P : FreeProduct G H -> Type)
  `{forall x, IsHProp (P x)}
  (l : forall g, P (freeproduct_inl g))
  (r : forall h, P (freeproduct_inr h))
  (Hop : forall x y, P x -> P y -> P (x * y))
  : forall x, P x
  := amalgamatedfreeproduct_ind_hprop P l r Hop.
(* The above is slow, ~0.15s. *)

Definition freeproduct_ind_homotopy {G H K : Group}
  {f f' : FreeProduct G H $-> K}
  (l : f $o freeproduct_inl $== f' $o freeproduct_inl)
  (r : f $o freeproduct_inr $== f' $o freeproduct_inr)
  : f $== f'
  := amalgamatedfreeproduct_ind_homotopy l r.

Definition equiv_freeproduct_ind_homotopy {Funext : Funext} {G H K : Group}
  (f f' : FreeProduct G H $-> K)
  : (f $o freeproduct_inl $== f' $o freeproduct_inl)
    * (f $o freeproduct_inr $== f' $o freeproduct_inr)
    <~> f $== f'
  := equiv_amalgamatedfreeproduct_ind_homotopy _ _.

Definition FreeProduct_rec {G H K : Group} (f : G $-> K) (g : H $-> K)
  : FreeProduct G H $-> K.
Proof.
  srapply (AmalgamatedFreeProduct_rec _ f g).
  intros [].
  exact (grp_homo_unit f @ (grp_homo_unit g)^).
Defined.

Definition freeproduct_rec_beta_inl {G H K : Group}
  (f : G $-> K) (g : H $-> K)
  : FreeProduct_rec f g $o freeproduct_inl $== f
  := fun x => right_identity (f x).

Definition freeproduct_rec_beta_inr {G H K : Group}
  (f : G $-> K) (g : H $-> K)
  : FreeProduct_rec f g $o freeproduct_inr $== g
  := fun x => right_identity (g x).

Definition equiv_freeproduct_rec `{funext : Funext} (G H K : Group)
  : (GroupHomomorphism G K) * (GroupHomomorphism H K)
  <~> GroupHomomorphism (FreeProduct G H) K.
Proof.
  refine (equiv_amalgamatedfreeproduct_rec K oE _^-1).
  refine (equiv_sigma_prod0 _ _ oE equiv_functor_sigma_id (fun _ => equiv_sigma_contr _)).
  intros f.
  rapply contr_forall.
  intros []; rapply contr_inhabited_hprop.
  exact (grp_homo_unit _ @ (grp_homo_unit _)^).
Defined.

(** The free product is the coproduct in the category of groups. *)
Instance hasbinarycoproducts : HasBinaryCoproducts Group.
Proof.
  intros G H.
  snapply Build_BinaryCoproduct.
  - exact (FreeProduct G H).
  - exact freeproduct_inl.
  - exact freeproduct_inr.
  - intros Z; exact FreeProduct_rec.
  - intros; apply freeproduct_rec_beta_inl.
  - intros; apply freeproduct_rec_beta_inr.
  - intros Z f g p q.
    by snapply freeproduct_ind_homotopy.
Defined.
