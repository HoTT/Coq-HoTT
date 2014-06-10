(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the universe, including the Univalence Axiom. *)

Require Import Overture PathGroupoids Equivalences.
Require Import HProp EquivalenceVarieties Trunc types.Sigma.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

(** ** Paths *)

Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p) | 0
  := BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
  (fun b => ((transport_pp idmap p^ p b)^ @ transport2 idmap (concat_Vp p) b))
  (fun a => ((transport_pp idmap p p^ a)^ @ transport2 idmap (concat_pV p) a))
  (fun a => match p in _ = C return
              (transport_pp idmap p^ p (transport idmap p a))^ @
                 transport2 idmap (concat_Vp p) (transport idmap p a) =
              ap (transport idmap p) ((transport_pp idmap p p^ a) ^ @
                transport2 idmap (concat_pV p) a) with idpath => 1 end).

Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Definition equiv_path_V `{Funext} (A B : Type) (p : A = B) :
  equiv_path B A (p^) = equiv_inverse (equiv_path A B p).
Proof.
  destruct p. simpl. unfold equiv_path, equiv_inverse. simpl. apply ap.
  refine (@allpath_hprop _ (hprop_isequiv _) _ _).
Defined.

Class Univalence.

Axiom isequiv_equiv_path : forall {u:Univalence}, 
                           forall (A B : Type), IsEquiv (equiv_path A B).
Existing Instance isequiv_equiv_path.

Definition paths_unlift {A : Type@{i}} (x y : A) (p : paths@{j} x y) :  paths@{i} x y.
Proof.
  destruct p. apply idpath.
Defined.

Lemma eq_paths_lift `{Univalence} : forall (A : Type@{i}) (x y : A), 
                                      paths ((paths@{i} x y) : Type@{j}) (paths@{j} x y).
intros. apply isequiv_equiv_path. 
exists (@paths_lift A x y).
refine (BuildIsEquiv _ _ _ (@paths_unlift A x y)  _ _ _).
red. intros. destruct x0. reflexivity.
intro eq. destruct eq. reflexivity.
intro eq. destruct eq. simpl. reflexivity.
Defined.


Lemma Contr_internal_lift {A} : Contr_internal@{j} A -> Contr_internal@{i} A.
Proof.
  intros. destruct X. exists center.
  intros. apply paths_lift. apply contr.
Defined.
Require Import UniverseLevel.

Lemma IsTrunc_lift `{Univalence} n {A : Type@{j}} : IsTrunc@{j} n A -> IsTrunc@{i} n A.
Proof. revert A.
  induction n; intros A HA. simpl.
  apply Contr_internal_lift. apply HA. 
  simpl in HA.
  intros x y.
  specialize (IHn _ (HA x y)).
  red in IHn. red in IHn.
  red. red.

  rewrite <- (eq_paths_lift A x y).
  apply IHn.
Defined.

Section Univalence.
Context `{Univalence}.

Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
  := (equiv_path A B)^-1 f.

Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_universe_uncurried (BuildEquiv _ _ f feq).

Definition transport_path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z
  := ap10 (ap (equiv_fun A B) (eisretr (equiv_path A B) (BuildEquiv _ _ f feq))) z.

(* This somewhat fancier version is useful when working with HITs. *)
Definition transport_path_universe'
  {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  (f : P x <~> P y) (q : ap P p = path_universe f) (u : P x)
  : transport P p u = f u
  := transport_compose idmap P p u
   @ ap10 (ap (transport idmap) q) u
   @ transport_path_universe f u.

Definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p
  := eissect (equiv_path A B) p.

Definition isequiv_path_universe {A B : Type}
  : IsEquiv (@path_universe_uncurried A B)
 := _.

Definition equiv_path_universe (A B : Type) : (A <~> B) <~> (A = B)
  := BuildEquiv _ _ (@path_universe_uncurried A B) isequiv_path_universe.

Definition path_universe_V_uncurried `{Funext} {A B : Type} (f : A <~> B)
  : path_universe_uncurried (equiv_inverse f) = (path_universe_uncurried f)^.
Proof.
  revert f. equiv_intro ((equiv_path_universe A B)^-1) p. simpl.
  path_via (p^).
    2: exact (inverse2 (eisretr (equiv_path_universe A B) p)^).
  unfold compose. path_via (path_universe_uncurried (equiv_path B A p^)).
    by refine (ap _ (equiv_path_V A B p)^).
  by refine (eissect (equiv_path B A) p^).
Defined.

Definition path_universe_V `{Funext} `(f : A -> B) `{IsEquiv A B f}
  : path_universe (f^-1) = (path_universe f)^
  := path_universe_V_uncurried (BuildEquiv A B f _).

(** It would be nice for these to go in [HProp.v], but this file depends on that one, and these depend on having [Univalence]. *)
Instance trunc_path_IsHProp `{Funext} X Y `{IsHProp Y}
: IsHProp (X = Y).
Proof.
  apply hprop_allpath.
  intros pf1 pf2.
  rewrite <- (eta_path_universe pf1), <- (eta_path_universe pf2).
  lazymatch goal with
    | [ |- @path_universe _ _ (equiv_fun _ _ ?f) ?Hf
           = @path_universe _ _ (equiv_fun _ _ ?g) ?Hg ]
      => change Hf with (equiv_isequiv _ _ f);
        change Hg with (equiv_isequiv _ _ g);
        generalize (equiv_isequiv _ _ f) (equiv_isequiv _ _ g);
        generalize (equiv_fun _ _ f) (equiv_fun _ _ g)
  end.
  let f' := fresh in
  let g' := fresh in
  intros f' g' ? ?;
    assert (f' = g'); [ | path_induction; apply ap; apply allpath_hprop ].
  apply path_forall; intro.
  apply allpath_hprop.
Qed.

Global Instance isset_hProp `{Funext} : IsHSet hProp | 0.
Proof.
  eapply trunc_equiv'; [ apply issig_hProp | ].
  (intros ? [? ?]).
  refine (hprop_allpath _ _).
  intros.
  apply path_path_sigma_uncurried.
  (exists (allpath_hprop _ _)).
  by apply allpath_hprop.
Qed.

Definition path_iff_hprop_uncurried `{IsHProp A, IsHProp B}
: (A <-> B) -> A = B
  := @path_universe_uncurried A B o equiv_iff_hprop_uncurried.

Definition path_iff_hProp_uncurried `{Funext} {A B : hProp}
: (A <-> B) -> A = B
  := (@path_hprop _ A B) o path_iff_hprop_uncurried.

Global Instance isequiv_path_iff_hprop_uncurried `{Funext} `{IsHProp A, IsHProp B}
: IsEquiv (@path_iff_hprop_uncurried A _ B _) | 0
  := _.

Global Instance isequiv_path_iff_hProp_uncurried `{Funext} {A B : hProp}
: IsEquiv (@path_iff_hProp_uncurried _ A B).
Proof.
  unfold path_iff_hProp_uncurried.
  apply (@isequiv_compose).
  - typeclasses eauto.
  - unfold path_hprop.
    apply isequiv_inverse.
Defined.
End Univalence.
