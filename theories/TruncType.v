(* -*- mode: coq; mode: visual-line -*-  *)
(** * Universes of truncated types. *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesFunext.


Generalizable Variables A B n f.

(** * Universes of truncated types

Now that we have the univalence axiom (from [types/Universe]), we study further the universes [TruncType] of truncated types (including [hProp] and [hSet]) that were defined in [Basics/Trunc].  *)

(** ** Paths in [TruncType] *)

Section TruncType.
Context `{Univalence}.

Definition issig_trunctype {n : trunc_index}
  : { X : Type & IsTrunc n X } <~> TruncType n.
Proof.
  issig (@BuildTruncType n) (@trunctype_type n) (@istrunc_trunctype_type n).
Defined.

Global Instance isequiv_ap_trunctype {n : trunc_index} (A B : n-Type)
: IsEquiv (@ap _ _ (@trunctype_type n) A B).
Proof.
  (* It seems to be easier to construct its inverse directly as an equivalence. *)
  transparent assert (e : ((A = B :> Type) <~> (A = B :> n-Type))).
  { equiv_via ((issig_trunctype ^-1 A) = (issig_trunctype ^-1 B)).
    - simpl. apply (equiv_path_sigma_hprop
                      (trunctype_type A; istrunc_trunctype_type A)
                      (trunctype_type B; istrunc_trunctype_type B)).
    - symmetry. apply equiv_ap. refine _. }
  (* Apparently writing [e^-1%equiv] here instead of [e^-1%function] is much faster. *)
  refine (isequiv_homotopic e^-1%equiv _).
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_trunctype {n : trunc_index} (A B : TruncType n)
  : (A <~> B) <~> (A = B :> TruncType n).
Proof.
  equiv_via (A = B :> Type).
  - apply equiv_path_universe.
  - exact ((BuildEquiv _ _ (@ap _ _ (@trunctype_type n) A B) _)^-1)%equiv.
Defined.

Definition path_trunctype@{a b c} {n : trunc_index} {A B : TruncType n}
  : A <~> B -> (A = B :> TruncType n)
:= equiv_path_trunctype@{a b c} A B.

Global Instance isequiv_path_trunctype
       {n : trunc_index} {A B : TruncType n}
: IsEquiv (@path_trunctype n A B).
Proof.
  exact _.
Defined.

(** [path_trunctype] is functorial *)
Definition path_trunctype_1 {n : trunc_index} {A : TruncType n}
: path_trunctype (equiv_idmap A) = idpath.
Proof.
  unfold path_trunctype; simpl.
  rewrite (eta_path_universe_uncurried 1).
  rewrite path_sigma_hprop_1.
  reflexivity.
Qed.

Definition path_trunctype_V {n : trunc_index} {A B : TruncType n}
           (f : A <~> B)
  : path_trunctype f^-1 = (path_trunctype f)^.
Proof.
  unfold path_trunctype; simpl.
  rewrite path_universe_V_uncurried.
  rewrite (path_sigma_hprop_V (path_universe_uncurried f)).
  refine (concat_p1 _ @ concat_1p _ @ _).
  refine (_ @ (ap inverse (concat_1p _))^ @ (ap inverse (concat_p1 _))^).
  refine (ap_V _ _).
Qed.

Definition path_trunctype_pp {n : trunc_index} {A B C : TruncType n}
           (f : A <~> B) (g : B <~> C)
  : path_trunctype (g oE f) = path_trunctype f @ path_trunctype g.
Proof.
  unfold path_trunctype; simpl.
  rewrite path_universe_compose_uncurried.
  rewrite (path_sigma_hprop_pp _ _ _ (istrunc_trunctype_type B)).
  refine (concat_p1 _ @ concat_1p _ @ _).
  refine (_ @ (ap _ (concat_1p _))^ @ (ap _ (concat_p1 _))^).
  refine (_ @ (ap (fun z => z @ _) (concat_1p _))^ @ (ap (fun z => z @ _) (concat_p1 _))^).
  refine (ap_pp _ _ _).
Qed.

Definition ap_trunctype {n : trunc_index} {A B : TruncType n} {f : A <~> B}
  : ap trunctype_type (path_trunctype f) = path_universe_uncurried f.
Proof.
  destruct A, B.
  cbn in *.
  cbn; destruct (path_universe_uncurried f).
  rewrite concat_1p, concat_p1.
  rewrite <- 2 ap_compose.
  apply ap_const.
Qed.

Definition path_hset {A B} := @path_trunctype 0 A B.
Definition path_hprop {A B} := @path_trunctype -1 A B.

Global Instance istrunc_trunctype@{i j k | i < j, j < k} {n : trunc_index}
  : IsTrunc@{j} n.+1 (TruncType@{i} n) | 0.
Proof.
  intros A B.
  refine (trunc_equiv _ (equiv_path_trunctype@{i j k} A B)).
  case n as [ | n'].
  - apply contr_equiv_contr_contr. (* The reason is different in this case. *)
  - apply istrunc_equiv.
Defined.

Global Instance isset_hProp : IsHSet hProp.
Proof.
  exact _.
Defined.

Global Instance Sn_trunctype: forall n, IsTrunc n.+1 (sigT (IsTrunc n)) |0.
Proof.
  intro n.
  apply (trunc_equiv' _ issig_trunctype^-1).
Defined.

(** ** Some standard inhabitants *)

Definition Unit_hp : hProp := (BuildhProp Unit).
Definition False_hp : hProp := (BuildhProp Empty).
Definition Negation_hp `{Funext} (hprop : hProp) : hProp := BuildhProp (~hprop).
(** We could continue with products etc *)

(** ** The canonical map from Bool to hProp *)
Definition is_true (b : Bool) : hProp
  := if b then Unit_hp else False_hp.

(** ** Facts about HProps using univalence *)

Global Instance trunc_path_IsHProp X Y `{IsHProp Y}
: IsHProp (X = Y).
Proof.
  apply hprop_allpath.
  intros pf1 pf2.
  apply (equiv_inj (equiv_path X Y)).
  apply path_equiv, path_arrow.
  intros x; by apply path_ishprop.
Qed.

Definition path_iff_ishprop_uncurried `{IsHProp A, IsHProp B}
: (A <-> B) -> A = B :> Type
  := @path_universe_uncurried _ A B o equiv_iff_hprop_uncurried.

Definition path_iff_hprop_uncurried {A B : hProp}
: (A <-> B) -> A = B :> hProp
  := (@path_hprop A B) o (@equiv_iff_hprop_uncurried A _ B _).

Global Instance isequiv_path_iff_ishprop_uncurried `{IsHProp A, IsHProp B}
: IsEquiv (@path_iff_ishprop_uncurried A _ B _).
Proof.
  exact _.
Defined.

Global Instance isequiv_path_iff_hprop_uncurried {A B : hProp}
: IsEquiv (@path_iff_hprop_uncurried A B).
Proof.
  exact _.
Defined.

Definition path_iff_ishprop `{IsHProp A, IsHProp B}
: (A -> B) -> (B -> A) -> A = B :> Type
  := fun f g => path_iff_ishprop_uncurried (f,g).

Definition path_iff_hprop {A B : hProp}
: (A -> B) -> (B -> A) -> A = B :> hProp
  := fun f g => path_iff_hprop_uncurried (f,g).

End TruncType.
