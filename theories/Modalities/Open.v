Require Import HoTT.Basics HoTT.Types.
Require Import Extensions.
Require Import Modality Accessible Nullification Lex.

Local Open Scope path_scope.


(** * Open modalities *)

(** ** Definition *)

Definition Op `{Funext} (U : HProp) : Modality.
Proof.
  snapply easy_modality.
  - intros X; exact (U -> X).
  - intros T x; cbn.
    exact (fun _ => x).
  - cbn; intros A B f z u.
    refine (transport B _ (f (z u) u)).
    apply path_arrow; intros u'.
    apply ap; apply path_ishprop.
  - cbn; intros A B f a.
    apply path_arrow; intros u.
    transitivity (transport B 1 (f a u));
      auto with path_hints.
    apply (ap (fun p => transport B p (f a u))).
    transitivity (path_arrow (fun _ => a) (fun _ => a) (@ap10 U _ _ _ 1));
      auto with path_hints.
    * apply ap.
      apply path_forall; intros u'.
      apply ap_const.
    * apply eta_path_arrow.
  - intros A z z'.
    srefine (isequiv_adjointify _ _ _ _).
    * intros f; apply path_arrow; intros u.
      exact (ap10 (f u) u).
    * intros f; apply path_arrow; intros u.
      transitivity (path_arrow z z' (ap10 (f u))).
      + unfold to; apply ap.
        apply path_forall; intros u'.
        apply (ap (fun u0 => ap10 (f u0) u')).
        apply path_ishprop.
      + apply eta_path_arrow.
    * intros p.
      exact (eta_path_arrow _ _ _).
Defined.

(** ** The open modality is lex *)

(** Note that unlike most other cases, we can prove this without univalence (though we do of course need funext). *)
Instance lex_open `{Funext} (U : HProp)
  : Lex (Op U).
Proof.
  apply lex_from_isconnected_paths.
  intros A Ac x y.
  napply contr_forall.
  intro u.
  pose (contr_inhabited_hprop U u).
  rapply contr_paths_contr.
  refine (contr_equiv (U -> A) (equiv_contr_forall _)).
  exact Ac.
Defined.

(** ** The open modality is accessible. *)

Instance acc_open `{Funext} (U : HProp)
  : IsAccModality (Op U).
Proof.
  unshelve econstructor.
  - econstructor.
    exact (unit_name U).
  - intros X; split.
    + intros X_inO u.
      apply (equiv_inverse (equiv_ooextendable_isequiv _ _)).
      refine (cancelR_isequiv (fun x (u:Unit) => x)).
      exact X_inO.
    + intros ext; specialize (ext tt).
      refine (isequiv_compose (fun x => unit_name x)
                              (fun h => h o const_tt U)).
      exact (isequiv_ooextendable (fun _ => X) (const_tt U) ext).
Defined.

(** Thus, arguably a better definition of [Op] would be as a nullification modality, as it would not require [Funext] and would have a judgmental computation rule.  However, the above definition is also nice to know, as it doesn't use HITs.  We name the other version [Op']. *)
Definition Op' (U : HProp) : Modality
  := Nul (Build_NullGenerators Unit (fun _ => U)).
