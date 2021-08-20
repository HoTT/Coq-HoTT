Require Import Basics Types.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.FunctorCat.
Require Import WildCat.Adjoint.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda.
Require Import WildCat.Type.

(** Limits and colimits *)


(** For any category [A] there is a functor [diagonal : A $-> Fun01 J A] *)

Section ConstantFunctor.

  Context (A J : Type) `{Is1Cat A, IsGraph J}.

  Definition diagonal : A -> Fun01 J A :=
    fun x : A => Build_Fun01 J A (fun _ => x).

  Global Instance is0functor_diagonal : Is0Functor diagonal.
  Proof.
    apply Build_Is0Functor.
    intros a b f.
    snrapply Build_NatTrans.
    - intros c.
      exact f.
    - intros x y g.
      exact (cat_idr _ $@ (cat_idl _)^$).
  Defined.

  Global Instance is1functor_diagonal : Is1Functor diagonal.
  Proof.
    apply Build_Is1Functor.
    - intros a b f g p j.
      exact p.
    - intros a j.
      reflexivity.
    - intros a b c f g j.
      reflexivity.
  Defined.

  (** The property of having a [J]-shaped limit. *)
  Class HasLimit := {
    cat_limit : Fun01 J A -> A ;
    is0functor_cat_limit : Is0Functor cat_limit ;
    is1functor_cat_limit : Is1Functor cat_limit ;
    adjunction_cat_limit : Adjunction diagonal cat_limit;
  }.

  Global Existing Instances
    is0functor_cat_limit
    is1functor_cat_limit.

  Class HasColimit := {
    cat_colimit : Fun01 J A -> A ;
    is0functor_cat_colimit : Is0Functor cat_colimit ;
    is1functor_cat_colimit : Is1Functor cat_colimit ;
    adjunction_cat_colimit : Adjunction cat_colimit diagonal ;
  }.

  Global Existing Instances
    is0functor_cat_colimit
    is1functor_cat_colimit.

  Definition fun11_cat_limit `{HasLimit} : Fun11 (Fun01 J A) A
    := Build_Fun11 _ _ cat_limit.

  Definition fun11_cat_colimit `{HasColimit} : Fun11 (Fun01 J A) A
    := Build_Fun11 _ _ cat_colimit.

End ConstantFunctor.

(** Preservation of limits *)

(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  equiv_preserveslimits (x : Fun01 J A)
    : F (cat_limit A J x) $<~> cat_limit B J (fun01_compose F x).

(** This seems to be too strong *)
(* 
(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  natequiv_preserveslimits
    : NatEquiv (F o cat_limit A J) (cat_limit B J o fun01_compose F).
 *)

(** Properties of limits (and colimits) *)

(** Right adjoints preserve limits *)
Global Instance preserveslimits_right_adjoint `{Funext} (A B J : Type)
  `{Is1Cat A, !HasEquivs A, !Is1Cat_Strong A, Is01Cat J, !HasLimit A J,
    HasEquivs B, !HasMorExt B, !HasLimit B J}
  (L : Fun11 A B) (R : Fun11 B A) (adj : L ⊣ R)
  : PreservesLimits B A J R.
Proof.
  intros K.
  (** We proceed via the yoneda lemma. We will also show what the goal looks like in a more compact and readable notation. Ideally, the goal would actually look like this. *)
  srapply yon_equiv.
  (** A(x, R (lim y)) ≃ B(x, lim (R o y)) *)
  refine (natequiv_compose (natequiv_adjunction_l
    (adjunction_cat_limit _ _) (fun11_fun01_postcomp R K)) _).
  (** A(x, R (lim y)) ≃ B^J(Δx, (R o y)) *)
  refine (natequiv_compose (natequiv_prewhisker (natequiv_adjunction_l
    (adjunction_postcomp _ _ J L R adj) K) (diagonal A J)) _).
  (** A(x, R (lim y)) ≃ A^J(L o Δx, y) *)
  refine (natequiv_compose _ (natequiv_inverse _ _
    (natequiv_adjunction_l adj (cat_limit B J K)))).
  (** B(L x, lim y) ≃ A^J(L o Δx, y) *)
  refine (natequiv_compose _ (natequiv_inverse _ _ (natequiv_prewhisker
    (natequiv_adjunction_l (adjunction_cat_limit _ _) K) L))).
  (** A^J(Δ o L, y) ≃ A^J(L o Δx, y) *)
  (** Now we do some reshuffling to show that the diagonal and L commute. *)
  refine (natequiv_compose (natequiv_inverse _ _ _) _).
  1: apply natequiv_functor_assoc_ff_f.
  refine (natequiv_compose _ _).
  2: apply natequiv_functor_assoc_ff_f.
  (** This is where morphism extensionality and funext is used. *)
  snrapply natequiv_postwhisker.
  (** Why can't typeclasses find this? *)
  4: rapply hasequivs_op.
  2: rapply is1functor_yon.
  (** This can probably be generalized, but this particular proof is pretty complicated due to all the op terms involved. *)
  (** Perhaps it's time for a natequiv_adjointify? *)
  snrapply Build_NatEquiv.
  { intros a. cbn.
    srapply cate_adjointify.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_postwhisker.
      rapply fmap_id.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_prewhisker.
      rapply gpd_rev.
      rapply fmap_id.
    - intros i.
      rapply cat_idl.
    - intros j.
      rapply cat_idr. }
  intros a a' f.
  unfold trans_comp.
  unfold cate_adjointify.
  refine ((cate_buildequiv_fun _ $@R _) $@ _).
  refine (_ $@ (_ $@L _)).
  2: symmetry; rapply cate_buildequiv_fun.
  intros j; exact (cat_idr _ $@ (cat_idl _)^$).
Defined.

(** Property of a functor preserving colimits. *)
Class PreservesColimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasColimit A J,
  HasEquivs B, !HasColimit B J} (F : Fun11 A B) :=
  equiv_preservescolimits (x : Fun01 J A)
    : F (cat_colimit A J x) $<~> cat_colimit B J (fun01_compose F x).

(* TODO: there may be a clever way to do this using op *)
(** Left adjoints preserve colimits *)
Global Instance preservescolimits_left_adjoint `{Funext} (A B J : Type)
  `{Is1Cat A, !HasEquivs A, Is01Cat J, !HasColimit A J,
    HasEquivs B,  !Is1Cat_Strong B, !HasMorExt A, !HasColimit B J}
  (L : Fun11 A B) (R : Fun11 B A) (adj : L ⊣ R)
  : PreservesColimits A B J L.
Proof.
  intros K.
  (** We proceed via the coyoneda lemma. The proof is very much the same as before only dual. Ideally it would simply be a consequence of the other proof, but that seems to require cleverness I am unable to provide currently. *)
  (** Note that writing these steps can be tricky, since coq doesn't follow when they are broken up. Doing them in one go however let's coq pick the correct typeclasses. There maybe a way around this. *)
  srapply opyon_equiv.
  (** We do the right hand side first *)
  refine (natequiv_compose (natequiv_inverse _ _
    (natequiv_adjunction_r adj (cat_colimit A J K))) _).
  refine (natequiv_compose (natequiv_inverse _ _ (natequiv_prewhisker
    (natequiv_adjunction_r (adjunction_cat_colimit A J) K) R)) _).
  (** Now the left hand side *)
  refine (natequiv_compose _
    (natequiv_adjunction_r (adjunction_cat_colimit B J) _)).
  refine (natequiv_compose _ (natequiv_prewhisker
    (natequiv_adjunction_r (adjunction_postcomp _ _ _ _ _ adj) _) _)).
  (** Reassociating *)
  refine (natequiv_compose _
    (natequiv_functor_assoc_ff_f _ (fun11_fun01_postcomp R) _)).
  refine (natequiv_compose (natequiv_inverse _ _
    (natequiv_functor_assoc_ff_f (opyon K) (diagonal A J) R)) _).
  rapply natequiv_postwhisker.
  (** TODO: We can probably make this a seperate lemma *)
  (** Strange that this is shorter than the limit one. *)
  snrapply Build_NatEquiv.
  { intros b.
    snrapply Build_NatEquiv.
    1: intros j; reflexivity.
    intros a a' f.
    refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
    1,3: apply cate_buildequiv_fun.
    exact (cat_idl _ $@ fmap_id _ _ $@ (cat_idr _)^$). }
  intros a a' f j.
  refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
  1,3: apply cate_buildequiv_fun.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

(** (Co)limits in functor categories *)
Global Instance haslimit_fun01 (A B J : Type) `{IsGraph A, Is1Cat B, IsGraph J}
  `{!HasLimit B J}
  : HasLimit (Fun01 A B) J.
Proof.
Admitted.

(** ** Preservation of (co)limits by (co)limits *)

Lemma preserveslimits_cat_limit
  `{Funext}
  (A I J : Type) `{HasEquivs A, !Is1Cat_Strong A, IsGraph I, IsGraph J}
  `{!HasLimit A I, !HasLimit A J}
  : PreservesLimits _ _ I (fun11_cat_limit A J).
Proof.
  nrapply (preserveslimits_right_adjoint _ _ _ _ _).
  5: exact (adjunction_cat_limit A J).
Defined.
  10: exact _.
  4: exact _.
  2: exact _.




