(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the universe, including the Univalence Axiom. *)

Require Import Overture PathGroupoids Equivalences.
Require Import HProp EquivalenceVarieties Trunc types.Sigma.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

(** *** Paths *)

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

Class Univalence := {
  isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B)
}.

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

Instance trunc_hProp `{Funext} : IsHSet hProp.
Proof.
  eapply trunc_equiv'; [ apply issig_hProp | ].
  (intros ? [? ?]).
  apply hprop_allpath.
  repeat match goal with
           | _ => reflexivity
           | _ => intro
           | _ => progress simpl in *
           | [ H : _ = ?x |- _ ] => atomic x; induction H
           | [ H : @paths (sigT _) _ _ |- _ ]
             => rewrite <- (eta_path_sigma H);
               generalize (H..1) (H..2);
               clear H;
               simpl in *
           | [ x : sig _ |- _ ] => destruct x
           | [ H : _ = _ |- _ ]
             => let H' := fresh in
                assert (H' : idpath = H) by apply allpath_hprop;
                  induction H'
         end.
Qed.
End Univalence.
