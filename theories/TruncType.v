(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import HProp.

Generalizable Variables A B n f.

(** * Universes of truncated types

Now that we have the univalence axiom (from [types/Universe]), we study further the universes [TruncType] of truncated types (including [hProp] and [hSet]) that were defined in [Basics/Trunc].  *)

(** ** Paths in [TruncType] *)

Section TruncType.
  Context `{Univalence}.

  Definition issig_trunctype {n : trunc_index}
    : { X : Type & IsTrunc n X } <~> TruncType n.
  Proof.
    issig.
  Defined.

  Definition equiv_path_trunctype' {n : trunc_index} (A B : TruncType n)
    : (A = B :> Type) <~> (A = B :> TruncType n).
  Proof.
    refine ((equiv_ap' issig_trunctype^-1 _ _)^-1 oE _).
    exact (equiv_path_sigma_hprop (_;_) (_;_)).
  Defined.

  Global Instance isequiv_ap_trunctype {n : trunc_index} (A B : n-Type)
    : IsEquiv (@ap _ _ (@trunctype_type n) A B).
  Proof.
    srefine (isequiv_homotopic _^-1%equiv _).
    1: apply equiv_path_trunctype'.
    intros []; reflexivity.
  Defined.

  Definition equiv_path_trunctype {n : trunc_index} (A B : TruncType n)
    : (A <~> B) <~> (A = B :> TruncType n)
    := equiv_path_trunctype' _ _ oE equiv_path_universe _ _.

  Definition path_trunctype@{a b} {n : trunc_index} {A B : TruncType n}
    : A <~> B -> (A = B :> TruncType n)
  := equiv_path_trunctype@{a b} A B.

  Global Instance isequiv_path_trunctype {n : trunc_index} {A B : TruncType n}
    : IsEquiv (@path_trunctype n A B) := _.

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
    rewrite (path_sigma_hprop_pp _ _ _ (trunctype_istrunc B)).
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
  Definition path_hprop {A B} := @path_trunctype (-1) A B.

  Global Instance istrunc_trunctype {n : trunc_index}
    : IsTrunc n.+1 (TruncType n) | 0.
  Proof.
    intros A B.
    refine (istrunc_equiv_istrunc _ (equiv_path_trunctype@{i j} A B)).
    case n as [ | n'].
    - apply contr_equiv_contr_contr. (* The reason is different in this case. *)
    - apply istrunc_equiv.
  Defined.

  Global Instance isset_HProp : IsHSet HProp := _.

  Global Instance istrunc_sig_istrunc : forall n, IsTrunc n.+1 (sig (IsTrunc n)) | 0.
  Proof.
    intro n.
    apply (istrunc_equiv_istrunc _ issig_trunctype^-1).
  Defined.

  (** ** Some standard inhabitants *)

  Definition Unit_hp : HProp := (Build_HProp Unit).
  Definition False_hp : HProp := (Build_HProp Empty).
  Definition Negation_hp `{Funext} (hprop : HProp) : HProp := Build_HProp (~hprop).
  (** We could continue with products etc *)

  (** ** The canonical map from Bool to hProp *)
  Definition is_true (b : Bool) : HProp
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

  Definition path_iff_hprop_uncurried {A B : HProp}
  : (A <-> B) -> A = B :> HProp
    := (@path_hprop A B) o (@equiv_iff_hprop_uncurried A _ B _).

  Global Instance isequiv_path_iff_ishprop_uncurried `{IsHProp A, IsHProp B}
  : IsEquiv (@path_iff_ishprop_uncurried A _ B _) := _.

  Global Instance isequiv_path_iff_hprop_uncurried {A B : HProp}
  : IsEquiv (@path_iff_hprop_uncurried A B) := _.

  Definition path_iff_ishprop `{IsHProp A, IsHProp B}
  : (A -> B) -> (B -> A) -> A = B :> Type
    := fun f g => path_iff_ishprop_uncurried (f,g).

  Definition path_iff_hprop {A B : HProp}
  : (A -> B) -> (B -> A) -> A = B :> HProp
    := fun f g => path_iff_hprop_uncurried (f,g).

  Lemma equiv_path_iff_ishprop {A B : Type} `{IsHProp A, IsHProp B}
    : (A <-> B) <~> (A = B).
  Proof.
    exact (Build_Equiv _ _ path_iff_ishprop_uncurried _).
  Defined.

End TruncType.
