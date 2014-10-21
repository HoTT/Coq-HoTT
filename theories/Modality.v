(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import ReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Record Modality :=
  {
    msubu : UnitSubuniverse ;
    mreplete : Replete msubu ;
    O_ind : forall A (B : msubu A -> Type) (B_inO : forall oa, In msubu (B oa)),
               (forall a, B (to msubu A a)) -> forall a, B a ;
    O_ind_beta : forall A B B_inO (f : forall a : A, B (to msubu A a)) a,
                    O_ind A B B_inO f (to msubu A a) = f a ;
    inO_paths : forall A (A_inO : In msubu A) (z z' : A), In msubu (z = z')
  }.

Arguments O_ind {O} {A} B {B_inO} f a : rename.
Arguments O_ind_beta {O} {A} B {B_inO} f a : rename.

(* We don't declare this as a coercion, since soon we're going to declare a coercion from [Modality] to [ReflectiveSubuniverse]; then we'll get this coercion automatically as a composite. *)
(* Coercion mod_usubu : Modality >-> UnitSubuniverse. *)
Global Existing Instance mreplete.
Global Existing Instance inO_paths.

(** Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [fun oa => O (B oa)], and similarly only that path-spaces of types [O A] are modal, where "modal" means that the unit is an equivalence.  This is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].

However, our definition is more convenient in formalized applications because in some examples (such as [Trunc] and closed modalities), there is a naturally occurring [O_ind] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.  Thus, when we apply general theorems about modalities to a particular modality such as [Trunc], the proofs will reduce definitionally to "the way we would have proved them directly" if we didn't know about general modalities.

On the other hand, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. *)

Section EasyModality.

  Context (O' : Type -> Type).

  Context (to_O : forall T, T -> O' T).

  Let inO' A := IsEquiv (to_O A).

  Context (O_indO : forall A (B : O' A -> Type),
                       (forall a, O' (B (to_O A a)))
                       -> forall z, O' (B z)).

  Context (O_indO_beta : forall A B (f : forall a, O' (B (to_O A a))) a,
      O_indO A B f (to_O A a) = f a).

  Context (inO_pathsO : forall A (z z' : O' A), inO' (z = z')).

  (** Here is the defined more general induction principle. *)

  Local Definition O_ind' A (B : O' A -> Type)
        (B_inO : forall oa, inO' (B oa))
        (f : forall a, B (to_O A a))
        (oa : O' A) : B oa.
  Proof.
    pose (H := B_inO oa); unfold inO' in H.
    apply ((to_O (B oa))^-1).
    apply O_indO.
    intros a; apply to_O, f.
  Defined.

  Local Definition O_ind_beta' A B {B_inO : forall oa, inO' (B oa)}
        (f : forall a : A, B (to_O A a)) a
  : O_ind' A B B_inO f (to_O A a) = f a.
  Proof.
    unfold O_ind'.
    apply moveR_equiv_V.
    apply @O_indO_beta with (f := fun x => to_O _ (f x)).
  Qed.

  (** We start by building a [UnitSubuniverse]. *)

  Local Definition O_inO' A : inO' (O' A).
  Proof.
    refine (isequiv_adjointify (to_O (O' A))
             (O_indO (O' A) (const A) idmap) _ _).
    - intros x; pattern x; apply O_ind'.
      + intros oa; apply inO_pathsO.
      + intros a; apply ap.
        exact (O_indO_beta (O' A) (const A) idmap a).
    - intros a.
      exact (O_indO_beta (O' A) (const A) idmap a).
  Defined.

  (** However, it seems to be surprisingly hard to show (without univalence) that this [UnitSubuniverse] is replete.  We basically have to develop enough functoriality of [O] and naturality of [to_O].  We could do that directly, but instead we piggyback by showing that it is a reflective subuniverse.  This is why we excluded repleteness from the basic definition of [ReflectiveSubuniverse] and the proofs of functoriality. *)

  Local Definition O : ReflectiveSubuniverse.
  Proof.
    refine (Build_ReflectiveSubuniverse
              (Build_UnitSubuniverse
                 (fun T => IsEquiv (to_O T))
                 O' O_inO' to_O _)
              _ _ _ _);
      intros P Q ?.
    - intros f. exact (O_ind' P (fun _ => Q) (fun _ => Q_inO) f).
    - intros f x. exact (O_ind_beta' P (fun _ => Q) f x).
    - intros g h p x.
      cbn in Q_inO.
      refine ((ap (to_O Q))^-1 _).
      refine (O_ind' P (fun y => to_O Q (g y) = to_O Q (h y)) _ _ x).
      + intros y. apply inO_pathsO.
      + intros a; apply ap, p.
    - intros g h p x; cbn.
      rewrite O_ind_beta'.
      rewrite concat_pp_p.
      apply moveR_Vp.
      rewrite <- ap_compose.
      exact (concat_A1p (eissect (to_O Q)) (p x)).
  Defined.

  (** It is now automatically replete, since in our case [inO] means by definition that [to_O] is an equivalence. *)

  Local Instance replete_rsubU : Replete O.
  Proof.
    apply replete_inO_isequiv_to_O; trivial.
  Defined.

  (** Finally, we can build a modality. *)

  Definition Build_Modality_easy : Modality.
  Proof.
    refine (Build_Modality O _ O_ind' O_ind_beta' _); cbn.
  Defined.

End EasyModality.

(** We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Trunc], that this construction uses the general [O_ind] given as part of the modality data, and not one constructed out of [O_indO] as we did when proving [Build_Modality_easy].  For instance, this ensures that [O_functor] reduces to simply an application of [O_ind].

 Note also that our choice of how to define reflective subuniverses differently from the book enables us to prove this without using funext. *)

(** Corollary 7.7.8, part 1 *)
Definition modality_to_reflective_subuniverse (O : Modality)
: ReflectiveSubuniverse
:= Build_ReflectiveSubuniverse (msubu O)
     (fun P Q H => O_ind (fun _ => Q))
     (fun P Q H => O_ind_beta (fun _ => Q))
     (fun P Q H g h => O_ind (fun y => g y = h y))
     (fun P Q H g h => O_ind_beta (fun y => g y = h y)).

Coercion modality_to_reflective_subuniverse : Modality >-> ReflectiveSubuniverse.

(** Corollary 7.7.8, part 2 *)
Global Instance inO_sigma {O : Modality} (A:Type) (B:A -> Type)
       `{In O A} `{forall a, In O (B a)}
: In O {x:A & B x}.
Proof.
  generalize dependent A.
  refine (snd (inO_sigma_iff _) _).
  intros A B ? g.
  exists (O_ind B g).
  apply O_ind_beta.
Defined.

(** Conversely, if a reflective subuniverse is closed under sigmas, it is a modality. *)

Theorem reflective_subuniverse_to_modality
  (O : ReflectiveSubuniverse) {rep : Replete O}
  (H : forall (A:Type) (B:A -> Type)
          `{In O A} `{forall a, In O (B a)},
     (In O ({x:A & B x})))
  : Modality.
Proof.
  pose (K := fst (inO_sigma_iff _) H).
  exact (Build_Modality _ _
           (fun A B B_inO g => pr1 (K A B B_inO g))
           (fun A B B_inO g => pr2 (K A B B_inO g))
           _).
Defined.

(** The induction principle [O_ind], like most induction principles, is an equivalence. *)
Section OIndEquiv.
  Context {fs : Funext} (O : Modality).

  Section OIndEquivData.

    Context {A : Type} (B : O A -> Type) `{forall a, In O (B a)}.

    Global Instance isequiv_O_ind : IsEquiv (O_ind B).
    Proof.
      apply isequiv_adjointify with (g := fun h => h oD to O A).
      - intros h. apply path_forall.
        refine (O_ind (fun oa => O_ind B (h oD to O A) oa = h oa) _).
        exact (O_ind_beta B (h oD to O A)).
      - intros f. apply path_forall.
        exact (O_ind_beta B f).
    Defined.

    Definition equiv_O_ind
    : (forall a, B (to O A a)) <~> (forall oa, B oa)
    := BuildEquiv _ _ (O_ind B) _.

    (** Theorem 7.7.7 *)
    Definition isequiv_oD_to_O
    : IsEquiv (fun (h : forall oa, B oa) => h oD to O A)
    := equiv_isequiv (equiv_inverse equiv_O_ind).

  End OIndEquivData.

  Local Definition isequiv_o_to_O (A B : Type) (B_inO : In O B)
  : IsEquiv (fun (h : O A -> B) => h o to O A)
    := isequiv_oD_to_O (fun _ => B).

End OIndEquiv.

(** Finally, we give one nontrivial example of a modality.  This is Exercise 7.12 in the book. *)
Definition notnot_modality `{Funext} : Modality.
Proof.
  refine (Build_Modality_easy
            (fun X => ~~X)
            (fun X x nx => nx x)
            (fun A B f z nBz =>
              z (fun a => f a (transport (fun x => ~B x)
                                          (path_ishprop _ _)
                                          nBz)))
            _ _).
  - intros; apply path_ishprop.
  - intros; refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
Defined.

(** Of course, there is also the trivial example. *)
Definition identity_modality : Modality
  := Build_Modality
     (Build_UnitSubuniverse
        (fun _ => Unit)
        idmap
        (fun _ => tt)
        (fun T => idmap)
        _)
     (fun T U _ _ _ => tt)
     (fun A B _ f a => f a)
     (fun A B _ f a => 1)
     (fun A _ z z' => tt).

(** For more examples of modalities, see hit/Truncations.v and hit/PropositionalFracture.v. *)
