Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Cubical.
Require Import Colimits.Pushout.
Require Import HIT.Coeq.

Local Open Scope list_scope.
Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** In this file we define the amalgamated free product of a span of group homomorphisms as a HIT. *)

(** We wish to define the amalgamated free product of a span of group homomorphisms f : G -> H, g : G -> K as the following HIT:

  HIT M(f,g)
   | eta : list (H + K) -> M(f,g)
   | mu_H : forall (x y : list (H + K)) (h1 h2 : H),
      eta (x ++ [inl h1, inl h2] ++ y) = eta (x ++ [inl (h1 * h2)] ++ y)
   | mu_K : forall (x y : list (H + K)) (k1 k2 : K),
      eta (x ++ [inr k1, inr k2] ++ y) = eta (x ++ [inr (k1 * k2)] ++ y)
   | tau : forall (x y : list (H + K)) (z : G),
      eta (x ++ [inl (f z)] ++ y) = eta (x ++ [inr (g z)] ++ y)
   | omega_H : forall (x y : list (H + K)),
      eta (x ++ [inl mon_unit] ++ y) = eta (x ++ y)
   | omega_K : forall (x y : list (H + K)),
      eta (x ++ [inr mon_unit] ++ y) = eta (x ++ y).

  We will build this HIT up sucessively out of coequalizers. *)


(** Here are some operations on lists from the coq stdlib *)
Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l : list B) (a0 : A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l' : list B) (i : A),
    fold_left (l ++ l') i = fold_left l' (fold_left l i).
  Proof.
    induction l; simpl; auto.
  Qed.

End Fold_Left_Recursor.

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.

  Fixpoint fold_right (a0 : A) (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right a0 t)
    end.

  Lemma fold_right_app : forall l l' i,
    fold_right i (l++l') = fold_right (fold_right i l') l.
  Proof.
    induction l; simpl; auto.
  Qed.

End Fold_Right_Recursor.

Section FreeProduct.

  Context (G H K : Group)
    (f : GroupHomomorphism G H) (g : GroupHomomorphism G K).

  Definition Words : Type := list (H + K).

  Notation "[ x ]" := (cons x nil).

  Definition word_concat_w_nil (x : Words) : x ++ nil = x.
  Proof.
    induction x; trivial.
    cbn; f_ap.
  Defined.

  Definition word_concat_w_ww (x y z : Words) : x ++ (y ++ z) = (x ++ y) ++ z.
  Proof.
    revert x z.
    induction y; intros x z.
    { f_ap; symmetry.
      apply word_concat_w_nil. }
    simpl; revert z y IHy.
    induction x; trivial.
    intros z y IHy.
    simpl; f_ap.
    apply IHx, IHy.
  Defined.

  Fixpoint word_inverse (x : Words) : Words.
  Proof.
    destruct x as [|x xs].
    1: exact nil.
    destruct x as [h|k].
    + exact ((word_inverse xs) ++ [inl (- h)]).
    + exact ((word_inverse xs) ++ [inr (- k)]).
  Defined.

  (** Inversion changes order of concatenation. *)
  Definition word_inverse_ww (x y : Words)
    : word_inverse (x ++ y) = word_inverse y ++ word_inverse x.
  Proof.
    induction x as [|x xs].
    { symmetry.
      apply word_concat_w_nil. }
    simpl.
    destruct x; refine (_ @ (word_concat_w_ww _ _ _)^); f_ap.
  Defined.


  (** There are five source types for the path constructors. We will construct this HIT as the colimit of five forks going into [Words]. We can bundle up this colimit as a single coequalizer. *)

  (** Source types of path constructors *)
  Definition pc1 : Type := Words * H * H * Words.
  Definition pc2 : Type := Words * K * K * Words.
  Definition pc3 : Type := Words * G * Words.
  Definition pc4 : Type := Words * Words.
  Definition pc5 : Type := Words * Words.

  (** End points of the first path constructor *)
  Definition m1 : pc1 -> Words.
  Proof.
    intros [[[x h1] h2] y].
    exact (x ++ (inl h1 :: [inl h2]) ++ y).
  Defined.

  Definition m1' : pc1 -> Words.
  Proof.
    intros [[[x h1] h2] y].
    exact (x ++ [inl (h1 * h2)] ++ y).
  Defined.

  (** End points of the second path construct *)
  Definition m2 : pc2 -> Words.
  Proof.
    intros [[[x k1] k2] y].
    exact (x ++ (inr k1 :: [inr k2]) ++ y).
  Defined.

  Definition m2' : pc2 -> Words.
  Proof.
    intros [[[x k1] k2] y].
    exact (x ++ [inr (k1 * k2)] ++ y).
  Defined.

  (** End points of the third path constructor *)
  Definition m3 : pc3 -> Words.
  Proof.
    intros [[x z] y].
    exact (x ++ [inl (f z)] ++ y).
  Defined.

  Definition m3' : pc3 -> Words.
  Proof.
    intros [[x z] y].
    exact (x ++ [inr (g z)] ++ y).
  Defined.

  (** End points of the fourth path constructor *)
  Definition m4 : pc4 -> Words.
  Proof.
    intros [x y].
    exact (x ++ [inl mon_unit] ++ y).
  Defined.

  Definition m4' : pc4 -> Words.
  Proof.
    intros [x y].
    exact (x ++ y).
  Defined.

  (** End points of the fifth path constructor *)
  Definition m5 : pc5 -> Words.
  Proof.
    intros [x y].
    exact (x ++ [inr mon_unit] ++ y).
  Defined.

  Definition m5' : pc5 -> Words.
  Proof.
    intros [x y].
    exact (x ++ y).
  Defined.

  (** We can then define maps going into words consisting of the corresponding endpoints of the path constructors. *)
  Definition map : pc1 + pc2 + pc3 + pc4 + pc5 -> Words.
  Proof.
    intros [[[[x|x]|x]|x]|x].
    + exact (m1 x).
    + exact (m2 x).
    + exact (m3 x).
    + exact (m4 x).
    + exact (m5 x).
  Defined.

  Definition map' : pc1 + pc2 + pc3 + pc4 + pc5 -> Words.
  Proof.
    intros [[[[x|x]|x]|x]|x].
    + exact (m1' x).
    + exact (m2' x).
    + exact (m3' x).
    + exact (m4' x).
    + exact (m5' x).
  Defined.

  (** Finally we can define our type as the 0-truncation of the coequalizer of these maps *)
  Definition M : Type := Tr 0 (Coeq map map').

  (** We can define the constructors *)

  Definition eta : Words -> M := tr o coeq.

  Definition mu_H (x y : Words) (h1 h2 : H)
    : eta (x ++ (cons (inl h1) [inl h2]) ++ y) = eta (x ++ [inl (h1 * h2)] ++ y).
  Proof.
    unfold eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inl (inl (x,h1,h2,y)))))).
  Defined.

  Definition mu_K (x y : Words) (k1 k2 : K)
    : eta (x ++ (cons (inr k1) [inr k2]) ++ y) = eta (x ++ [inr (k1 * k2)] ++ y).
  Proof.
    unfold eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inl (inr (x,k1,k2,y)))))).
  Defined.

  Definition tau (x y : Words) (z : G)
    : eta (x ++ [inl (f z)] ++ y) = eta (x ++ [inr (g z)] ++ y).
  Proof.
    unfold eta.
    apply path_Tr, tr.
    exact (cglue (inl (inl (inr (x,z,y))))).
  Defined.

  Definition omega_H (x y : Words)
    : eta (x ++ [inl mon_unit] ++ y) = eta (x ++ y).
  Proof.
    unfold eta.
    apply path_Tr, tr.
    exact (cglue (inl (inr (x,y)))).
  Defined.

  Definition omega_K (x y : Words)
    : eta (x ++ [inr mon_unit] ++ y) = eta (x ++ y).
  Proof.
    unfold eta.
    apply path_Tr, tr.
    exact (cglue (inr (x,y))).
  Defined.

  (** Now we can derive the dependent eliminator *)

  Definition M_ind (P : M -> Type) `{forall x, IsHSet (P x)}
    (e : forall w, P (eta w))
    (mh : forall (x y : Words) (h1 h2 : H),
      DPath P (mu_H x y h1 h2) (e (x ++ (inl h1 :: [inl h2]) ++ y)) (e (x ++ [inl (h1 * h2)] ++ y)))
    (mk : forall (x y : Words) (k1 k2 : K),
      DPath P (mu_K x y k1 k2) (e (x ++ (inr k1 :: [inr k2]) ++ y)) (e (x ++ [inr (k1 * k2)] ++ y)))
    (t : forall (x y : Words) (z : G),
      DPath P (tau x y z) (e (x ++ [inl (f z)] ++ y)) (e (x ++ [inr (g z)] ++ y)))
    (oh : forall (x y : Words),
      DPath P (omega_H x y) (e (x ++ [inl mon_unit] ++ y)) (e (x ++ y)))
    (ok : forall (x y : Words),
      DPath P (omega_K x y) (e (x ++ [inr mon_unit] ++ y)) (e (x ++ y)))
    : forall x, P x.
  Proof.
    snrapply Trunc_ind; [exact _|].
    snrapply Coeq_ind.
    1: exact e.
    intro a.
    nrapply dp_path_transport^-1%equiv.
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

  Definition M_ind_hprop (P : M -> Type) `{forall x, IsHProp (P x)}
    (e : forall w, P (eta w))
    : forall x, P x.
  Proof.
    srapply M_ind.
    1: exact e.
    all: intros; apply dp_path_transport, path_ishprop.
  Defined.

  (** From which we can derive the non-dependent eliminator / recursion principle *)
  Definition M_rec (P : Type) `{IsHSet P} (e : Words -> P)
    (eh : forall (x y : Words) (h1 h2 : H),
      e (x ++ (cons (inl h1) [inl h2]) ++ y) = e (x ++ [inl (h1 * h2)] ++ y))
    (ek : forall (x y : Words) (k1 k2 : K),
      e (x ++ (cons (inr k1) [inr k2]) ++ y) = e (x ++ [inr (k1 * k2)] ++ y))
    (t : forall (x y : Words) (z : G),
      e (x ++ [inl (f z)] ++ y) = e (x ++ [inr (g z)] ++ y))
    (oh : forall (x y : Words), e (x ++ [inl mon_unit] ++ y) = e (x ++ y))
    (ok : forall (x y : Words), e (x ++ [inr mon_unit] ++ y) = e (x ++ y))
    : M -> P.
  Proof.
    snrapply M_ind.
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

  (** The group operation is concatenation of the underlying list. Most of the work is spent showing that it respects the path constructors. *)
  Global Instance sgop_m : SgOp M.
  Proof.
    intros x y; revert x.
    srapply M_rec; intros x; revert y.
    { srapply M_rec; intros y.
      1: exact (eta (x ++ y)).
      { intros z h1 h2.
        refine (ap eta _ @ _ @ ap eta _^).
        1,3: apply word_concat_w_ww.
        rapply mu_H. }
      { intros z k1 k2.
        refine (ap eta _ @ _ @ ap eta _^).
        1,3: apply word_concat_w_ww.
        rapply mu_K. }
      { intros w z.
        refine (ap eta _ @ _ @ ap eta _^).
        1,3: apply word_concat_w_ww.
        apply tau. }
      { intros z.
        refine (ap eta _ @ _ @ ap eta _^).
        1,3: apply word_concat_w_ww.
        apply omega_H. }
      { intros z.
        refine (ap eta _ @ _ @ ap eta _^).
        1,3: apply word_concat_w_ww.
        apply omega_K. } }
    { intros r y h1 h2; revert r.
      rapply M_ind_hprop; cbn.
      intros z;
      change (eta ((x ++ ((inl h1 :: [inl h2]) ++ y)) ++ z)
        = eta ((x ++ [inl (h1 * h2)] ++ y) ++ z)).
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      refine (ap eta (ap (app x) _)^ @ _ @ ap eta (ap (app x) _)).
      1,3: apply word_concat_w_ww.
      apply mu_H. }
    { intros r y k1 k2; revert r.
      rapply M_ind_hprop; cbn.
      intros z;
      change (eta ((x ++ ((inr k1 :: [inr k2]) ++ y)) ++ z)
        = eta ((x ++ [inr (k1 * k2)] ++ y) ++ z)).
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      refine (ap eta (ap (app x) _)^ @ _ @ ap eta (ap (app x) _)).
      1,3: apply word_concat_w_ww.
      apply mu_K. }
    { intros r y z; revert r.
      rapply M_ind_hprop; cbn.
      intros w;
      change (eta ((x ++ [inl (f z)] ++ y) ++ w)
        = eta ((x ++ [inr (g z)] ++ y) ++ w)).
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      refine (ap eta (ap (app x) _)^ @ _ @ ap eta (ap (app x) _)).
      1,3: apply word_concat_w_ww.
      apply tau. }
    { intros r z; revert r.
      rapply M_ind_hprop; cbn.
      intros w;
      change (eta ((x ++ [inl mon_unit] ++ z) ++ w) = eta ((x ++ z) ++ w)).
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      refine (ap eta (ap (app x) _)^ @ _).
      1: apply word_concat_w_ww.
      apply omega_H. }
    { intros r z; revert r.
      rapply M_ind_hprop; cbn.
      intros w;
      change (eta ((x ++ [inr mon_unit] ++ z) ++ w) = eta ((x ++ z) ++ w)).
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      refine (ap eta (ap (app x) _)^ @ _).
      1: apply word_concat_w_ww.
      apply omega_K. }
  Defined.

  (** The identity element is the empty list *)
  Global Instance monunit_m : MonUnit M.
  Proof.
    exact (eta nil).
  Defined.

  Global Instance negate_m : Negate M.
  Proof.
    srapply M_rec.
    { intros w.
      exact (eta (word_inverse w)). }
    { hnf; intros x y h1 h2.
      refine (ap eta _ @ _ @ ap eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1: apply word_inverse_ww.
      { refine (word_inverse_ww _ _ @ _).
        apply ap; simpl.
        rapply (ap (fun s => [s])).
        apply ap.
        apply negate_sg_op. }
      simpl.
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      apply mu_H. }
    { hnf; intros x y k1 k2.
      refine (ap eta _ @ _ @ ap eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1: apply word_inverse_ww.
      { refine (word_inverse_ww _ _ @ _).
        apply ap; simpl.
        rapply (ap (fun s => [s])).
        apply ap.
        apply negate_sg_op. }
      simpl.
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      apply mu_K. }
    { hnf; intros x y z.
      refine (ap eta _ @ _ @ ap eta _^).
      1,3: refine (word_inverse_ww _ _ @ ap (fun s => s ++ _) _).
      1,2: cbn; refine (ap _ _).
      1,2: rapply (ap (fun s => [s])).
      1,2: apply ap.
      1,2: symmetry; apply grp_homo_inv.
      refine (ap eta _^ @ _ @ ap eta _).
      1,3: apply word_concat_w_ww.
      apply tau. }
    { hnf; intros x z.
      refine (ap eta _ @ _ @ ap eta _^).
      1,3: apply word_inverse_ww.
      refine (ap eta _ @ _).
      { refine (ap (fun s => s ++ _) _).
        apply word_inverse_ww. }
      refine (ap eta _^ @ _).
      1: apply word_concat_w_ww.
      simpl.
      rewrite negate_mon_unit.
      apply omega_H. }
    { hnf; intros x z.
      refine (ap eta _ @ _ @ ap eta _^).
      1,3: apply word_inverse_ww.
      refine (ap eta _ @ _).
      { refine (ap (fun s => s ++ _) _).
        apply word_inverse_ww. }
      refine (ap eta _^ @ _).
      1: apply word_concat_w_ww.
      simpl.
      rewrite negate_mon_unit.
      apply omega_K. }
  Defined.

  Global Instance associative_sgop_m : Associative sg_op.
  Proof.
    intros x y.
    rapply M_ind_hprop; intro z; revert y.
    rapply M_ind_hprop; intro y; revert x.
    rapply M_ind_hprop; intro x.
    cbn; nrapply (ap eta).
    rapply word_concat_w_ww.
  Defined.

  Global Instance leftidentity_sgop_m : LeftIdentity sg_op mon_unit.
  Proof.
    rapply M_ind_hprop; intro x.
    reflexivity.
  Defined.

  Global Instance rightidentity_sgop_m : RightIdentity sg_op mon_unit.
  Proof.
    rapply M_ind_hprop; intro x.
    cbn; nrapply (ap eta).
    apply word_concat_w_nil.
  Defined.

  Lemma eta_word_concat_Vw (x : Words) : eta (word_inverse x ++ x) = mon_unit.
  Proof.
    induction x as [|x xs].
    1: reflexivity.
    destruct x as [h|k].
    + change (eta (word_inverse ([inl h] ++ xs) ++ [inl h] ++ xs) = mon_unit).
      rewrite word_inverse_ww.
      rewrite <- word_concat_w_ww.
      refine (mu_H _ _ _ _ @ _).
      rewrite left_inverse.
      rewrite omega_H.
      apply IHxs.
    + change (eta (word_inverse ([inr k] ++ xs) ++ [inr k] ++ xs) = mon_unit).
      rewrite word_inverse_ww.
      rewrite <- word_concat_w_ww.
      refine (mu_K _ _ _ _ @ _).
      rewrite left_inverse.
      rewrite omega_K.
      apply IHxs.
  Defined.

  Lemma eta_word_concat_wV (x : Words) : eta (x ++ word_inverse x) = mon_unit.
  Proof.
    induction x as [|x xs].
    1: reflexivity.
    destruct x as [h|k].
    + cbn.
      rewrite word_concat_w_ww.
      change (eta ([inl h]) * eta ((xs ++ word_inverse xs)) * eta ([inl (- h)]) = mon_unit).
      rewrite IHxs.
      rewrite rightidentity_sgop_m.
      cbn.
      rewrite <- (word_concat_w_nil (cons _ _)).
      change (eta (([inl h] ++ [inl (- h)]) ++ nil) = mon_unit).
      rewrite <- word_concat_w_ww.
      change (eta (nil ++ [inl h] ++ [inl (- h)] ++ nil) = mon_unit).
      refine (mu_H _ _ _ _ @ _).
      refine (_ @ _).
      { apply ap, ap.
        rapply (ap (fun x => x ++ _)).
        rapply (ap (fun x => [x])).
        apply ap.
        apply right_inverse. }
      apply omega_H.
    +  cbn.
      rewrite word_concat_w_ww.
      change (eta ([inr k]) * eta ((xs ++ word_inverse xs)) * eta ([inr (-k)]) = mon_unit).
      rewrite IHxs.
      rewrite rightidentity_sgop_m.
      cbn.
      rewrite <- (word_concat_w_nil (cons _ _)).
      change (eta (([inr k] ++ [inr (- k)]) ++ nil) = mon_unit).
      rewrite <- word_concat_w_ww.
      change (eta (nil ++ [inr k] ++ [inr (- k)] ++ nil) = mon_unit).
      refine (mu_K _ _ _ _ @ _).
      refine (_ @ _).
      { apply ap, ap.
        rapply (ap (fun x => x ++ _)).
        rapply (ap (fun x => [x])).
        apply ap.
        apply right_inverse. }
      apply omega_K.
  Defined.

  Global Instance leftinverse_sgop_m : LeftInverse sg_op negate mon_unit.
  Proof.
    rapply M_ind_hprop; intro x.
    apply eta_word_concat_Vw.
  Defined.

  Global Instance rightinverse_sgop_m : RightInverse sg_op negate mon_unit.
  Proof.
    rapply M_ind_hprop; intro x.
    apply eta_word_concat_wV.
  Defined.

  Definition AmalgamatedFreeProduct : Group.
  Proof.
    snrapply (Build_Group M); repeat split; exact _.
  Defined.

  (** Using foldr. It's important that we use foldr as foldl is near impossible to reason about. *)
  Definition AmalgamatedFreeProduct_rec' (X : Group)
    (h : GroupHomomorphism H X) (k : GroupHomomorphism K X)
    (p : h o f == k o g)
    : AmalgamatedFreeProduct -> X.
  Proof.
    srapply M_rec.
    { intro w.
      refine (fold_right _ _ _ _ w).
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

  Global Instance issemigrouppreserving_AmalgamatedFreeProduct_rec'
    (X : Group) (h : GroupHomomorphism H X) (k : GroupHomomorphism K X)
    (p : h o f == k o g)
    : IsSemiGroupPreserving (AmalgamatedFreeProduct_rec' X h k p).
  Proof.
    intros x; srapply M_ind_hprop; intro y; revert x;
    srapply M_ind_hprop; intro x; simpl.
    rewrite fold_right_app.
    set (s := (fold_right X (H + K)
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
    (h : GroupHomomorphism H X) (k : GroupHomomorphism K X)
    (p : h o f == k o g)
    : GroupHomomorphism AmalgamatedFreeProduct X.
  Proof.
    snrapply Build_GroupHomomorphism.
    1: srapply (AmalgamatedFreeProduct_rec' X h k p).
    exact _.
  Defined.

  Definition amal_inl : GroupHomomorphism H AmalgamatedFreeProduct.
  Proof.
    snrapply Build_GroupHomomorphism.
    { intro x.
      exact (eta [inl x]). }
    intros x y.
    rewrite <- (word_concat_w_nil [inl (x * y)]).
    rewrite <- (mu_H nil nil x y).
    rewrite word_concat_w_nil.
    reflexivity.
  Defined.

  Definition amal_inr : GroupHomomorphism K AmalgamatedFreeProduct.
  Proof.
    snrapply Build_GroupHomomorphism.
    { intro x.
      exact (eta [inr x]). }
    intros x y.
    rewrite <- (word_concat_w_nil [inr (x * y)]).
    rewrite <- (mu_K nil nil x y).
    rewrite word_concat_w_nil.
    reflexivity.
  Defined.

  Theorem equiv_amalgamatedfreeproduct_rec `{Funext} (X : Group)
    : {h : GroupHomomorphism H X & {k : GroupHomomorphism K X & h o f == k o g }}
      <~> GroupHomomorphism AmalgamatedFreeProduct X.
  Proof.
    snrapply equiv_adjointify.
    1: intros [h [k p]]; exact (AmalgamatedFreeProduct_rec X h k p).
    { intros r.
      exists (grp_homo_compose r amal_inl).
      exists (grp_homo_compose r amal_inr).
      intro x.
      apply (ap r).
      simpl.
      rewrite <- (word_concat_w_nil [inl (f x)]).
      rewrite <- (word_concat_w_nil [inr (g x)]).
      apply (tau nil nil x). }
    { intros r.
      apply equiv_path_grouphomomorphism.
      srapply M_ind_hprop.
      intro x.
      induction x as [|a x].
      1: symmetry; apply (grp_homo_unit r).
      simpl in *.
      rewrite IHx.
      destruct a; symmetry;
      rapply (grp_homo_op r (eta [_]) (eta x)). }
    intro hkp.
    simpl.
    rapply (equiv_ap' (equiv_sigma_prod
      (fun hk : GroupHomomorphism H X * GroupHomomorphism K X
        => fst hk o f == snd hk o g)) _ _)^-1%equiv.
    rapply path_sigma_hprop.
    destruct hkp as [h [k p]].
    apply path_prod; cbn;
    apply equiv_path_grouphomomorphism;
    intro; cbn; apply right_identity.
  Defined.

End FreeProduct.




