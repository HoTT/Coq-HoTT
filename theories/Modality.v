Require Import Overture PathGroupoids HProp Equivalences EquivalenceVarieties.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe types.ObjectClassifier.
Require Import ReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Section Modalities.
  Context {path_universe : Univalence}.
  Context {Fun : Funext}.
  Set Implicit Arguments.

  (** Quoting the HoTT Book: *)
  (** Definition 7.7.5. A _modality_ is an operation [○ : Type → Type] for which there are

    (i) functions [eta^○_A : A → ○(A)] for every type [A]

    (ii) for every [A : Type] and every type family [B : ○(A) → Type], a function

         [ind_○ : (∀ a : A, ○(B(eta^○_A(a)))) → (∀ z : ○(A), ○(B(z)))]

    (iii) A path [ind_○(f)(eta^○_A(a)) = f(a)] for each [f : ∀ a : A, ○(B(eta^○_A(a)))].

    (iv) For any [z z' : ○(A)], the function [eta^○_{z = z'} : (z = z') → ○(z = z')] is an equivalence. *)

  Class IsModality (mod : Type -> Type) :=
    { modality_eta : forall A, A -> mod A;
      modality_ind : forall A (B : mod A -> Type),
                       (forall a, mod (B (modality_eta a)))
                       -> forall z, mod (B z);
      modality_ind_compute : forall A B (f : forall a : A, mod (B _)) a,
                               modality_ind _ f (modality_eta a) = f a;
      modality_isequiv_eta_path :> forall A (z z' : mod A),
                                     IsEquiv (@modality_eta (z = z')) }.

  (** A type is modal if its eta function is an equivalence *)
  Definition ismodal (mod : Type -> Type) (ismod : IsModality mod) (A:Type)
    := IsEquiv (modality_eta (A:=A)).

  Definition hprop_ismodal (mod : Type -> Type) (ismod : IsModality mod)
  : forall A, IsHProp (ismodal ismod A)
    := fun A => hprop_isequiv _.

  (** The image of a type by [mod] is always modal *)
  Lemma ismodal_mod (mod : Type -> Type) (ismod : IsModality mod) (A:Type)
  : ismodal ismod (mod A).
  Proof.
    apply isequiv_adjointify with (g := fun X => modality_ind (A:=mod A) (fun _ => A) idmap X).
    - intro x.
      apply (equiv_inv (IsEquiv := modality_isequiv_eta_path
                                     (mod A)
                                     (modality_eta (modality_ind (fun _ : mod (mod A) => A) (fun u:mod A => u) x))
                                     x) ).
      generalize dependent x; apply modality_ind; intro a.
      apply modality_eta.
      rewrite (modality_ind_compute (fun _ : mod (mod A) => A) (fun u:mod A => u) a).
      exact idpath.
    - exact (fun x => modality_ind_compute (fun _ : mod (mod A) => A) idmap x).
  Qed.

  Lemma ismodal_paths (mod : Type -> Type) (ismod : IsModality mod) (A:Type) (H:ismodal ismod A)
  : forall (x y:A), ismodal ismod (x=y).
  Proof.
    intros x y.
    assert (X : (x=y) = (modality_eta x = modality_eta y)).
    apply path_universe_uncurried.
    exact (BuildEquiv _ _ (ap (modality_eta (A:=A)))
                      (isequiv_ap (H:=H) x y)).
    rewrite X.
    exact (modality_isequiv_eta_path A (modality_eta x) (modality_eta y)).
  Qed.

  (** Theorem 7.7.7 *)
  Theorem isequiv_postcompose_eta (mod:Type -> Type) (ismod : IsModality mod)
          (A:Type) (B:mod A -> Type)
          (H:forall a, ismodal ismod (B a))
  : IsEquiv (fun x:(forall z:mod A, B z) => (fun y => x (modality_eta y))).
  Proof.
    apply @isequiv_adjointify with
    (g := fun f a =>
            ((equiv_inv (IsEquiv := H a)))
              (modality_ind B (fun a' => modality_eta (f a')) a)).
    - intro f. apply path_forall; intro x.
      rewrite (modality_ind_compute B (fun a' : A => modality_eta (f a')) x).
      apply eissect.
    - intro s. apply path_forall; intro x.
      assert (Y := ismodal_paths
                     (H x)
                     (s x)
                     (equiv_inv
                        (IsEquiv := H x)
                        (modality_ind B (fun y => modality_eta (s (modality_eta y))) x))).
      refine (equiv_inv (IsEquiv := Y) _)^; clear Y.
      generalize dependent x; apply modality_ind; intro a; apply modality_eta.
      rewrite (modality_ind_compute B (fun x => modality_eta (s (modality_eta x))) a).
      rewrite eissect.
      exact idpath.
  Qed.

  (** Corollary 7.7.8 *)
  Definition modality_to_reflective_subuniverse (mod : Type -> Type) (ismod : IsModality mod)
  : ReflectiveSubuniverse
    := Build_ReflectiveSubuniverse
         (fun T => hp (ismodal ismod T) (@hprop_ismodal mod ismod T))
         (fun T => (mod T ; ismodal_mod ismod T))
         (modality_eta)
         (fun P Q => @isequiv_postcompose_eta mod ismod P (fun _ => Q.1) (fun _ => Q.2)).

  (** Exercise 7.12 *)
  Instance ismodality_notnot `{Funext} : IsModality (fun X => ~~X).
  Proof.
    apply (@Build_IsModality
             (fun X => ~~X)
             (fun X x nx => match nx x with end)
             (fun A B H' z nBz =>
                z (fun a => H' a (transport (fun x => ~B x)
                                            (allpath_hprop _ _)
                                            nBz))));
    abstract (
        repeat (intro || apply path_forall);
        try match goal with
              | [ |- appcontext[match ?x : Empty with end] ] => destruct x
            end;
        refine (isequiv_adjointify
                  (fun x nx => match nx x : Empty with end)
                  (fun _ => allpath_hprop z z')
                  _
                  _);
        repeat (intro || apply path_forall);
        apply allpath_hprop
      ).
  Defined.

End Modalities.
