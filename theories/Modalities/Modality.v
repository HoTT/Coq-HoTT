(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties Extensions Factorization NullHomotopy.
Require Export ReflectiveSubuniverse. (* [Export] because many of the lemmas and facts about reflective subuniverses are equally important for modalities. *)
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Module Type Modalities.

  Parameter Modality : Type2@{u a}.

  (** These are the same as for a reflective subuniverse. *)

  Parameter O_reflector : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Check O_reflector@{u a i}.    (** Verify that we have the right number of universes *)

  Parameter inO_internal : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Check inO_internal@{u a i}.

  Parameter O_inO_internal : forall (O : Modality@{u a}) (T : Type@{i}),
                               inO_internal@{u a i} O (O_reflector@{u a i} O T).
  Check O_inO_internal@{u a i}.

  Parameter to : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
  Check to@{u a i}.

  Parameter inO_equiv_inO_internal :
      forall (O : Modality@{u a}) (T U : Type@{i})
             (T_inO : inO_internal@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        inO_internal@{u a i} O U.
  Check inO_equiv_inO_internal@{u a i}.

  Parameter hprop_inO_internal
  : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
                IsHProp (inO_internal@{u a i} O T).
  Check hprop_inO_internal@{u a i}.

  (** Now instead of [extendable_to_O], we have an ordinary induction principle. *)

  Parameter O_ind_internal
  : forall (O : Modality@{u a})
           (A : Type2le@{i a})
           (B : O_reflector@{u a i} O A -> Type2le@{j a})
           (B_inO : forall oa, inO_internal@{u a j} O (B oa)),
      (** We add an extra unused universe parameter [k] that's [>= max(i,j)].  This seems to be necessary for some examples, such as [Nullification], which are constructed by way of an operation that requires such a universe.  *)
      let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
      let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
      (forall a, B (to O A a)) -> forall a, B a.
  Check O_ind_internal@{u a i j k}.

  Parameter O_ind_beta_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, inO_internal@{u a j} O (B oa))
           (f : forall a : A, B (to O A a)) (a:A),
      O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.
  Check O_ind_beta_internal@{u a i j k}.

  Parameter minO_paths
  : forall (O : Modality@{u a})
           (A : Type2le@{i a}) (A_inO : inO_internal@{u a i} O A) (z z' : A),
      inO_internal@{u a i} O (z = z').
  Check minO_paths@{u a i}.

End Modalities.

(** ** Modalities are reflective subuniverses *)

(** We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Trunc], that this construction uses the general [O_ind] given as part of the modality data.  For instance, this ensures that [O_functor] reduces to simply an application of [O_ind].

  Note also that our choice of how to define reflective subuniverses differently from the book, using [ooExtendableAlong] enables us to prove this without using funext. *)

Module Modalities_to_ReflectiveSubuniverses
       (Os : Modalities) <: ReflectiveSubuniverses.

  Import Os.

  Fixpoint O_extendable (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall a, inO_internal@{u a j} O (B a)) (n : nat)
  : ExtendableAlong@{i i j k} n (to O A) B.
  Proof.
    destruct n as [|n].
    - exact tt.
    - split.
      + intros g.
        exists (O_ind_internal@{u a i j k} O A B B_inO g); intros x.
        apply O_ind_beta_internal.
      + intros h k.
        apply O_extendable; intros x.
        apply minO_paths; trivial.
  Defined.

  Definition ReflectiveSubuniverse := Modality.

  Definition O_reflector := O_reflector.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition inO_internal := inO_internal@{u a i}.
  Definition O_inO_internal := O_inO_internal@{u a i}.
  Definition to := to.
  Definition inO_equiv_inO_internal := inO_equiv_inO_internal@{u a i}.
  Definition hprop_inO_internal := hprop_inO_internal@{u a i}.

  (** Corollary 7.7.8, part 1 *)
  Definition extendable_to_O_internal (O : ReflectiveSubuniverse@{u a})
    {P : Type@{i}} {Q : Type@{j}} {Q_inO : inO_internal@{u a j} O Q}
  : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q)
    := fun n => O_extendable O P (fun _ => Q) (fun _ => Q_inO) n.

End Modalities_to_ReflectiveSubuniverses.


(** Conversely, if a reflective subuniverse is closed under sigmas, it is a modality.  This is a bit annoying to state using modules, and in fact with our current definitions there doesn't seem to be a way to actually convince Coq to accept it.  However, this is not really a problem in practice: in most or all examples, constructing [O_ind] directly is just as easy, and preferable because it sometimes gives a judgmental computation rule.  However, for the sake of completeness, we include here the code that almost works. *)

Module Type SigmaClosed (Os : ReflectiveSubuniverses).

  Import Os.

  Parameter inO_sigma
  : forall (O : ReflectiveSubuniverse@{u a})
           (A:Type@{i}) (B:A -> Type@{j})
           (A_inO : inO_internal@{u a i} O A)
           (B_inO : forall a, inO_internal@{u a j} O (B a)),
      inO_internal@{u a k} O {x:A & B x}.
  Check inO_sigma@{u a i j k}.    (** Verify that we have the right number of universes *)

End SigmaClosed.

(** We omit the module type, because Coq won't actually accept it (see below for why). *)
Module ReflectiveSubuniverses_to_Modalities
       (Os : ReflectiveSubuniverses) (OsSigma : SigmaClosed Os).
(** <: Modalities. *)

  Import Os OsSigma.
  Module Import Os_Theory := ReflectiveSubuniverses_Theory Os.

  Definition Modality := ReflectiveSubuniverse.

  Definition O_reflector := O_reflector.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition inO_internal := inO_internal@{u a i}.
  Definition O_inO_internal := O_inO_internal@{u a i}.
  Definition to := to.
  Definition inO_equiv_inO_internal := inO_equiv_inO_internal@{u a i}.
  Definition hprop_inO_internal := hprop_inO_internal@{u a i}.

  (** The reason Coq won't actually accept this as a module of type [Modalities] is that the following definitions of [O_ind_internal] and [O_ind_beta_internal] have an extra universe parameter [k] that's at least as large as both [i] and [j].  This is because [extendable_to_O_internal] has such a parameter, which in turn is because [ooExtendableAlong] does.  Unfortunately, we can't directly instantiate [k] to [max(i,j)] because Coq doesn't allow "algebraic universes" in arbitrary position.  We could probably work around it by defining [ExtendableAlong] inductively rather than recursively, but given the non-usefulness of this construction in practice, that doesn't seem to be worth the trouble at the moment. *)
  Definition O_ind_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
  : (forall a, B (to O A a)) -> forall a, B a
  := fun g => pr1 ((O_ind_from_inO_sigma@{u a i j k k j} O (inO_sigma O))
                     A B B_inO g).

  Definition O_ind_beta_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a:A)
  : O_ind_internal O A B B_inO f (to O A a) = f a
  := pr2 ((O_ind_from_inO_sigma@{u a i j k k j} O (inO_sigma O))
                     A B B_inO f) a.

  Definition minO_paths (O : Modality@{u a})
             (A : Type@{i}) (A_inO : inO_internal@{u a i} O A) (z z' : A)
  : inO_internal O (z = z')
  := @inO_paths@{u a i i} O A A_inO z z'.

End ReflectiveSubuniverses_to_Modalities.


(** ** Easy modalities *)

(** Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [fun oa => O (B oa)], and similarly only that path-spaces of types [O A] are modal, where "modal" means that the unit is an equivalence.  This is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].

However, our definition is more convenient in formalized applications because in some examples (such as [Trunc] and closed modalities), there is a naturally occurring [O_ind] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.  Thus, when we apply general theorems about modalities to a particular modality such as [Trunc], the proofs will reduce definitionally to "the way we would have proved them directly" if we didn't know about general modalities.

On the other hand, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. *)

Module Type EasyModalities.

  Parameter Modality : Type2@{u a}.
  Check Modality@{u a}.    (** Verify that we have the right number of universes *)

  Parameter O_reflector : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Check O_reflector@{u a i}.

  Parameter to : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
  Check to@{u a i}.

  Parameter O_indO
  : forall (O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} O A -> Type@{j}),
      (forall a, O_reflector@{u a j} O (B (to O A a)))
      -> forall z, O_reflector@{u a j} O (B z).
  Check O_indO@{u a i j}.

  Parameter O_indO_beta
  : forall (O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} O A -> Type@{j})
           (f : forall a, O_reflector@{u a j} O (B (to O A a))) a,
      O_indO O A B f (to O A a) = f a.
  Check O_indO_beta@{u a i j}.

  Parameter minO_pathsO
  : forall (O : Modality@{u a}) (A : Type@{i})
           (z z' : O_reflector@{u a i} O A),
      IsEquiv (to@{u a i} O (z = z')).
  Check minO_pathsO@{u a i}.

End EasyModalities.

Module EasyModalities_to_Modalities (Os : EasyModalities)
<: Modalities.

  Import Os.

  Definition Modality := Modality.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition O_reflector := O_reflector@{u a i}.
  Definition to := to@{u a i}.

  Definition inO_internal
  : forall (O : Modality@{u a}), Type@{i} -> Type@{i}
  := fun O A => IsEquiv@{i i} (to O A).

  Definition hprop_inO_internal `{Funext} (O : Modality@{u a})
             (T : Type@{i})
  : IsHProp (inO_internal@{u a i} O T).
  Proof.
    unfold inO_internal.
    exact (hprop_isequiv (to O T)).
  Defined.

  Definition O_ind_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    (forall a, B (to O A a)) -> forall oa, B oa.
  Proof.
    simpl; intros f oa.
    pose (H := B_inO oa); unfold inO_internal in H.
    apply ((to O (B oa))^-1).
    apply O_indO.
    intros a; apply to, f.
  Defined.

  Definition O_ind_beta_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a:A)
  : O_ind_internal O A B B_inO f (to O A a) = f a.
  Proof.
    unfold O_ind_internal.
    apply moveR_equiv_V.
    apply @O_indO_beta with (f := fun x => to O _ (f x)).
  Qed.

  Definition O_inO_internal (O : Modality@{u a}) (A : Type@{i})
  : inO_internal@{u a i} O (O_reflector@{u a i} O A).
  Proof.
    refine (isequiv_adjointify (to O (O_reflector O A))
             (O_indO O (O_reflector O A) (fun _ => A) idmap) _ _).
    - intros x; pattern x; apply O_ind_internal.
      + intros oa; apply minO_pathsO.
      + intros a; apply ap.
        exact (O_indO_beta O (O_reflector O A) (fun _ => A) idmap a).
    - intros a.
      exact (O_indO_beta O (O_reflector O A) (fun _ => A) idmap a).
  Defined.

  (** It seems to be surprisingly hard to show repleteness (without univalence).  We basically have to manually develop enough functoriality of [O] and naturality of [to O]. *)
  Definition inO_equiv_inO_internal (O : Modality@{u a}) (A B : Type@{i})
    (A_inO : inO_internal@{u a i} O A) (f : A -> B) (feq : IsEquiv f)
  : inO_internal@{u a i} O B.
  Proof.
    refine (isequiv_commsq (to O A) (to O B) f
             (O_ind_internal O A (fun _ => O_reflector O B) _ (fun a => to O B (f a))) _).
    - intros; apply O_inO_internal.
    - intros a; refine (O_ind_beta_internal O A (fun _ => O_reflector O B) _ _ a).
    - apply A_inO.
    - refine (isequiv_adjointify _
               (O_ind_internal O B (fun _ => O_reflector O A) _ (fun b => to O A (f^-1 b))) _ _);
        intros x.
      + apply O_inO_internal.
      + pattern x; refine (O_ind_internal O B _ _ _ x); intros.
        * apply minO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_beta_internal; apply ap, eisretr).
      + pattern x; refine (O_ind_internal O A _ _ _ x); intros.
        * apply minO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_beta_internal; apply ap, eissect).
  Defined.

  Definition minO_paths (O : Modality@{u a})
             (A : Type@{i}) (A_inO : inO_internal@{u a i} O A) (a a' : A)
  : inO_internal O (a = a').
  Proof.
    refine (inO_equiv_inO_internal O (to O A a = to O A a') _ _
                          (@ap _ _ (to O A) a a')^-1 _).
    - apply minO_pathsO.
    - refine (@isequiv_ap _ _ _ A_inO _ _).
    - apply isequiv_inverse.
  Defined.

End EasyModalities_to_Modalities.

(** We now move on to the general theory of modalities. *)

Module Modalities_Theory (Os : Modalities).

Export Os.
Module Export Os_ReflectiveSubuniverses
  := Modalities_to_ReflectiveSubuniverses Os.
Module Export RSU
  := ReflectiveSubuniverses_Theory Os_ReflectiveSubuniverses.

(** As with reflective subuniverses, we put this in a module so it can be exported separately (and it should be). *)
Module Export Coercions.
  Coercion modality_to_reflective_subuniverse
    := idmap : Modality -> ReflectiveSubuniverse.
End Coercions.

Definition O_ind {O : Modality@{u a}}
           {A : Type@{i}} (B : O A -> Type@{j})
           {B_inO : forall oa, In O (B oa)}
           (f : forall a, B (to O A a)) (oa : O A)
: B oa
:= O_ind_internal O A B B_inO f oa.

Definition O_ind_beta {O : Modality@{u a}}
           {A : Type@{i}} (B : O A -> Type@{j})
           {B_inO : forall oa, In O (B oa)}
           (f : forall a : A, B (to O A a)) (a : A)
: @O_ind O A B B_inO f (to O A a) = f a
:= O_ind_beta_internal O A B B_inO f a.

(** Corollary 7.7.8, part 2 *)
Global Instance inO_sigma {O : Modality} (A:Type) (B:A -> Type)
       `{In O A} `{forall a, In O (B a)}
: In O {x:A & B x}.
Proof.
  generalize dependent A.
  refine (inO_sigma_from_O_ind _ _).
  intros A B ? g.
  exists (O_ind B g).
  apply O_ind_beta.
Defined.

(** Theorem 7.3.9: The reflector [O] can be discarded inside a reflected sum. *)
Definition equiv_O_sigma_O {O : Modality} {A} (P : A -> Type)
: O {x:A & O (P x)} <~> O {x:A & P x}.
Proof.
  refine (equiv_adjointify _ _ _ _).
  - apply O_rec; intros [a op]; revert op.
    apply O_rec; intros p.
    exact (to O _ (a;p)).
  - apply O_rec; intros [a p].
    exact (to O _ (a ; to O _ p)).
  - unfold Sect; apply O_ind; try exact _.
    intros [a p]; simpl.
    abstract (repeat rewrite O_rec_beta; reflexivity).
  - unfold Sect; apply O_ind; try exact _.
    intros [a op]; revert op; apply O_ind; try exact _; intros p; simpl.
    abstract (repeat rewrite O_rec_beta; reflexivity).
Defined.

(** Corollary 7.3.10 *)
Corollary equiv_sigma_inO_O {O : Modality} {A} `{In O A} (P : A -> Type)
: {x:A & O (P x)} <~> O {x:A & P x}.
Proof.
  transitivity (O {x:A & O (P x)}).
  - apply equiv_to_O; exact _.
  - apply equiv_O_sigma_O.
Defined.

(** ** The induction principle [O_ind], like most induction principles, is an equivalence. *)
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

(** ** Modally connected types *)

(** Connectedness of a type, relative to a modality, can be defined in two equivalent ways: quantifying over all maps into modal types, or by considering just the universal case, the modal reflection of the type itself.  The former requires only core Coq, but blows up the size (universe level) of [IsConnected], since it quantifies over types; moreover, it is not even quite correct since (at least with a polymorphic modality) it should really be quantified over all universes.  Thus, we use the latter, although in most examples it requires HITs to define the modal reflection.

Question: is there a definition of connectedness (say, for n-types) that neither blows up the universe level, nor requires HIT's? *)

Class IsConnected (O : Modality@{u a}) (A : Type@{i})
  := isconnected_contr_O : IsTrunc@{i} -2 (O A).
Check IsConnected@{u a i}.

Global Existing Instance isconnected_contr_O.

Section ConnectedTypes.
  Context (O : Modality).

  (** Being connected is an hprop *)
  Global Instance ishprop_isconnected `{Funext} A
  : IsHProp (IsConnected O A).
  Proof.
    unfold IsConnected; exact _.
  Defined.

  (** Anything equivalent to a connected type is connected. *)
  Definition isconnected_equiv (A : Type) {B : Type} (f : A -> B) `{IsEquiv _ _ f}
  : IsConnected O A -> IsConnected O B.
  Proof.
    intros ?; refine (contr_equiv (O A) (O_functor O f)).
  Defined.

  Definition isconnected_equiv' (A : Type) {B : Type} (f : A <~> B)
  : IsConnected O A -> IsConnected O B
    := isconnected_equiv A f.

  (** Connectedness of a type [A] can equivalently be characterized by the fact that any map to an [O]-type [C] is nullhomotopic.  Here is one direction of that equivalence. *)
  Definition isconnected_elim {A : Type} `{IsConnected O A} (C : Type) `{In O C} (f : A -> C)
  : NullHomotopy f.
  Proof.
    set (ff := @O_rec O _ _ _ f).
    exists (ff (center _)).
    intros a. symmetry.
    refine (ap ff (contr (to O _ a)) @ _).
    apply O_rec_beta.
  Defined.

  (** For the other direction of the equivalence, it's sufficient to consider the case when [C] is [O A]. *)
  Definition isconnected_from_elim_to_O {A : Type}
  : NullHomotopy (to O A) -> IsConnected O A.
  Proof.
    intros nh.
    exists (nh .1).
    apply O_ind; try exact _.
    intros; symmetry; apply (nh .2).
  Defined.

  (** Now the general case follows. *)
  Definition isconnected_from_elim {A : Type}
  : (forall (C : Type) `{In O C} (f : A -> C), NullHomotopy f)
    -> IsConnected O A.
  Proof.
    intros H.
    exact (isconnected_from_elim_to_O (H (O A) (O_inO A) (to O A))).
  Defined.

  (** A type which is both connected and truncated is contractible. *)

  Definition contr_trunc_conn {A : Type} `{In O A} `{IsConnected O A}
  : Contr A.
  Proof.
    apply (contr_equiv _ (to O A)^-1).
  Defined.

  (** Here's another way of stating the universal property for mapping out of connected types into modal ones. *)
  Definition extendable_const_isconnected_inO (n : nat)
             (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3811 *)
             (A : Type@{i}) {conn_A : IsConnected@{u a i} O A}
             (C : Type@{j}) `{In@{u a j} O C}
  : ExtendableAlong@{i i j j} n (@const A Unit@{i} tt) (fun _ => C).
  Proof.
    generalize dependent C;
      simple_induction n n IHn; intros C ?;
      [ exact tt | split ].
    - intros f.
      exists (fun _ => (isconnected_elim C f).1); intros a.
      symmetry; apply ((isconnected_elim C f).2).
    - intros h k.
      refine (extendable_postcompose' n _ _ _ _ (IHn (h tt = k tt) _)).
      intros []; apply equiv_idmap.
  Defined.

  Definition ooextendable_const_isconnected_inO
             (A : Type@{i}) `{IsConnected@{u a i} O A}
             (C : Type@{j}) `{In@{u a j} O C}
  : ooExtendableAlong (@const A Unit tt) (fun _ => C)
    := fun n => extendable_const_isconnected_inO@{i j k k j} n A C.

  Definition isequiv_const_isconnected_inO `{Funext}
             {A : Type} `{IsConnected O A} (C : Type) `{In O C}
  : IsEquiv (@const A C).
  Proof.
    refine (@isequiv_compose _ _ (fun c u => c) _ _ _
              (isequiv_ooextendable (fun _ => C) (@const A Unit tt)
                                    (ooextendable_const_isconnected_inO A C))).
  Defined.

End ConnectedTypes.

(** ** Modally truncated maps *)

(** A map is "in [O]" if each of its fibers is. *)

Class MapIn (O : Modality@{u a}) {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  := inO_hfiber_ino_map : forall (b:B), In@{u a k} O (hfiber f b).
Check MapIn@{u a i j k}.        (** k >= max(i,j) *)

Global Existing Instance inO_hfiber_ino_map.

Section ModalMaps.
  Context (O : Modality).

  (** Any equivalence is modal *)
  Global Instance mapinO_isequiv {A B : Type} (f : A -> B) `{IsEquiv _ _ f}
  : MapIn O f.
  Proof.
    intros b.
    pose (fcontr_isequiv f _ b).
    exact _.
  Defined.

  (** Any map between modal types is modal. *)
  Definition mapinO_between_inO {A B : Type} (f : A -> B)
             `{In O A} `{In O B}
  : MapIn O f.
  Proof.
    intros b; exact _.
  Defined.

  (** Anything homotopic to a modal map is modal. *)
  Definition mapinO_homotopic {A B : Type} (f : A -> B) {g : A -> B}
             (p : f == g) `{MapIn O _ _ f}
  : MapIn O g.
  Proof.
    intros b.
    refine (inO_equiv_inO (hfiber f b)
                          (equiv_hfiber_homotopic f g p b)).
  Defined.

  (** Being modal is an hprop *)
  Global Instance ishprop_mapinO `{Funext} {A B : Type} (f : A -> B)
  : IsHProp (MapIn O f).
  Proof.
    apply trunc_forall.
  Defined.

  (** The composite of modal maps is modal *)
  Global Instance mapinO_compose {A B C : Type} (f : A -> B) (g : B -> C)
         `{MapIn O _ _ f} `{MapIn O _ _ g}
  : MapIn O (g o f).
  Proof.
    intros c.
    refine (inO_equiv_inO _ (hfiber_compose f g c)^-1).
  Defined.

End ModalMaps.

(** ** Modally connected maps *)

(** Connectedness of a map can again be defined in two equivalent ways: by connectedness of its fibers (as types), or by the lifting property/elimination principle against truncated types.  We use the former; the equivalence with the latter is given below in [conn_map_elim], [conn_map_comp], and [conn_map_from_extension_elim]. *)

Class IsConnMap (O : Modality@{u a}) {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  := isconnected_hfiber_conn_map : forall b:B, IsConnected@{u a k} O (hfiber f b).
Check IsConnMap@{u a i j k}.        (** k >= max(i,j) *)

Global Existing Instance isconnected_hfiber_conn_map.

Section ConnectedMaps.
  Context `{Univalence} `{Funext}.
  Context (O : Modality).

  (** Any equivalence is connected *)
  Global Instance conn_map_isequiv {A B : Type} (f : A -> B) `{IsEquiv _ _ f}
  : IsConnMap O f.
  Proof.
    intros b.
    pose (fcontr_isequiv f _ b).
    unfold IsConnected; exact _.
  Defined.

  (** Anything homotopic to a connected map is connected. *)
  Definition conn_map_homotopic {A B : Type} (f g : A -> B) (h : f == g)
  : IsConnMap O f -> IsConnMap O g.
  Proof.
    intros ? b.
    exact (isconnected_equiv O (hfiber f b)
                             (equiv_hfiber_homotopic f g h b) _).
  Defined.

  (** Being connected is an hprop *)
  Global Instance ishprop_isconnmap `{Funext} {A B : Type} (f : A -> B)
  : IsHProp (IsConnMap O f).
  Proof.
    apply trunc_forall.
  Defined.

  (** n-connected maps are orthogonal to n-truncated maps (i.e. familes of n-truncated types). *)
  Definition conn_map_elim
             {A B : Type} (f : A -> B) `{IsConnMap O _ _ f}
             (P : B -> Type) `{forall b:B, In O (P b)}
             (d : forall a:A, P (f a))
  : forall b:B, P b.
  Proof.
    intros b.
    refine (pr1 (isconnected_elim O _ _)).
    2:exact b.
    intros [a p].
    exact (transport P p (d a)).
  Defined.

  Definition conn_map_comp
             {A B : Type} (f : A -> B) `{IsConnMap O _ _ f}
             (P : B -> Type) `{forall b:B, In O (P b)}
             (d : forall a:A, P (f a))
  : forall a:A, conn_map_elim f P d (f a) = d a.
  Proof.
    intros a. unfold conn_map_elim.
    set (fibermap := (fun a0p : hfiber f (f a)
                      => let (a0, p) := a0p in transport P p (d a0))).
    destruct (isconnected_elim O (P (f a)) fibermap) as [x e].
    change (d a) with (fibermap (a;1)).
    apply inverse, e.
  Defined.

  Definition isequiv_conn_ino_map {A B : Type} (f : A -> B)
             `{IsConnMap O _ _ f} `{MapIn O _ _ f}
  : IsEquiv f.
  Proof.
    apply isequiv_fcontr. intros b.
    apply (contr_trunc_conn O).
  Defined.

  (** We can re-express this in terms of extensions. *)
  Lemma extension_conn_map_elim
        {A B : Type} (f : A -> B) `{IsConnMap O _ _ f}
        (P : B -> Type) `{forall b:B, In O (P b)}
        (d : forall a:A, P (f a))
  : ExtensionAlong f P d.
  Proof.
    exists (conn_map_elim f P d).
    apply conn_map_comp.
  Defined.

  Lemma allpath_extension_conn_map
        {A B : Type} (f : A -> B) `{IsConnMap O _ _ f}
        (P : B -> Type) `{forall b:B, In O (P b)}
        (d : forall a:A, P (f a))
        (e e' : ExtensionAlong f P d)
  : e = e'.
  Proof.
    apply path_extension.
    refine (extension_conn_map_elim _ _ _).
  Defined.

  (** It follows that [conn_map_elim] is actually an equivalence. *)
  Theorem isequiv_o_conn_map 
          {A B : Type} (f : A -> B) `{IsConnMap O _ _ f}
          (P : B -> Type) `{forall b:B, In O (P b)}
  : IsEquiv (fun (g : forall b:B, P b) => g oD f).
  Proof.
    apply isequiv_fcontr; intros d.
    apply contr_inhabited_hprop.
    - refine (@trunc_equiv' {g : forall b, P b & g oD f == d} _ _ _ _).
      { refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
        apply equiv_path_forall. }
      apply hprop_allpath. intros g h.
      exact (allpath_extension_conn_map f P d g h).
    - exists (conn_map_elim f P d).
      apply path_forall; intros x; apply conn_map_comp.
  Defined.

  (** Conversely, if a map satisfies this elimination principle (expressed via extensions), then it is connected.  This completes the proof of Lemma 7.5.7 from the book. *)
  Lemma conn_map_from_extension_elim {A B : Type} (f : A -> B)
  : (forall (P : B -> Type) {P_inO : forall b:B, In O (P b)}
            (d : forall a:A, P (f a)),
       ExtensionAlong f P d)
    -> IsConnMap O f.
  Proof.
    intros Hf b. apply isconnected_from_elim_to_O.
    assert (e := Hf (fun b => O (hfiber f b)) _ (fun a => to O _ (a;1))).
    exists (e.1 b).
    intros [a p]. destruct p.
    symmetry; apply (e.2).
  Defined.

  (** Corollary 7.5.8: It follows that the unit maps [to O A] are connected. *)
  Global Instance conn_map_to_O (A : Type) : IsConnMap O (to O A).
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (O_ind P d); intros a.
    apply O_ind_beta.
  Defined.

  (** Lemma 7.5.6: Connected maps compose and cancel on the right. *)
  Global Instance conn_map_compose {A B C : Type} (f : A -> B) (g : B -> C)
         `{IsConnMap O _ _ f} `{IsConnMap O _ _ g}
  : IsConnMap O (g o f).
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (conn_map_elim g P (conn_map_elim f (P o g) d)); intros a.
    exact (conn_map_comp g P _ _ @ conn_map_comp f (P o g) d a).
  Defined.      

  Definition cancelR_conn_map {A B C : Type} (f : A -> B) (g : B -> C)
         `{IsConnMap O _ _ f} `{IsConnMap O _ _ (g o f)}
  :  IsConnMap O g.
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (conn_map_elim (g o f) P (d oD f)); intros b.
    pattern b; refine (conn_map_elim f _ _ b); intros a.
    exact (conn_map_comp (g o f) P (d oD f) a).
  Defined.

  (* Lemma 7.5.10: A map to a type in [O] exhibits its codomain as the [O]-reflection of its domain if (and only if) it is [O]-connected. *)
  Definition isequiv_O_rec_conn_map {A B : Type} `{In O B}
             (f : A -> B) `{IsConnMap O _ _ f}
  : IsEquiv (O_rec f).
  Proof.
    apply isequiv_conn_ino_map.
    - refine (cancelR_conn_map (to O A) (O_rec f)).
      refine (conn_map_homotopic f _ _ _).
      intros a; symmetry; apply O_rec_beta.
    - apply mapinO_between_inO; exact _.
  Defined.

  (** Lemma 7.5.12 *)
  Section ConnMapFunctorSigma.

    Context {A B : Type} {P : A -> Type} {Q : B -> Type}
            (f : A -> B) (g : forall a, P a -> Q (f a))
            `{forall a, IsConnMap O (g a)}.

    Definition equiv_O_hfiber_functor_sigma (b:B) (v:Q b)
    : O (hfiber (functor_sigma f g) (b;v)) <~> O (hfiber f b).
    Proof.
      equiv_via (O {w : hfiber f b & hfiber (g w.1) ((w.2)^ # v)}).
      { apply equiv_O_functor, hfiber_functor_sigma. }
      equiv_via (O {w : hfiber f b & O (hfiber (g w.1) ((w.2)^ # v))}).
      { symmetry; apply equiv_O_sigma_O. }
      apply equiv_O_functor.
      apply equiv_sigma_contr; intros [a p]; simpl; exact _.
    Defined.

    Global Instance conn_map_functor_sigma `{IsConnMap O _ _ f}
    : IsConnMap O (functor_sigma f g).
    Proof.
      intros [b v].
      (* Why is this so slow? *)
      refine (contr_equiv _ (equiv_inverse (equiv_O_hfiber_functor_sigma b v))).
    Defined.

    Definition conn_map_base_inhabited (inh : forall b, Q b)
               `{IsConnMap O _ _ (functor_sigma f g)}
    : IsConnMap O f.
    Proof.
      intros b.
      refine (contr_equiv _ (equiv_O_hfiber_functor_sigma b (inh b))).
    Defined.

  End ConnMapFunctorSigma.

  (** Lemma 7.5.13.  The "if" direction is a special case of [conn_map_functor_sigma], so we prove only the "only if" direction. *)
  Definition conn_map_fiber
             {A : Type} {P Q : A -> Type} (f : forall a, P a -> Q a)
             `{IsConnMap O _ _ (functor_sigma idmap f)}
  : forall a, IsConnMap O (f a).
  Proof.
    intros a q.
    refine (isconnected_equiv' O (hfiber (functor_sigma idmap f) (a;q)) _ _).
    exact (hfiber_functor_sigma_idmap P Q f a q).
  Defined.

  (** Lemma 7.5.14: Connected maps are inverted by [O]. *)
  Global Instance O_inverts_conn_map {A B : Type} (f : A -> B)
         `{IsConnMap O _ _ f}
  : IsEquiv (O_functor O f).
  Proof.
    refine (isequiv_adjointify _ _ _ _).
    - apply O_rec; intros y.
      exact (O_functor O pr1 (center (O (hfiber f y)))).
    - unfold Sect; apply O_ind; try exact _; intros b.
      refine (ap (O_functor O f) (O_rec_beta _ b) @ _).
      refine ((O_functor_compose _ _ _ _)^ @ _).
      set (x := (center (O (hfiber f b)))).
      clearbody x; revert x; apply O_ind; try exact _; intros [a p].
      refine (O_rec_beta (to O B o (f o pr1)) (a;p) @ _).
      exact (ap (to O B) p).
    - unfold Sect; apply O_ind; try exact _; intros a.
      refine (ap (O_rec _) (to_O_natural O f a) @ _).
      refine (O_rec_beta _ _ @ _).
      transitivity (O_functor O pr1 (to O (hfiber f (f a)) (a;1))).
      + apply ap, contr.
      + refine (to_O_natural _ _ _).
  Defined.

End ConnectedMaps.

(** ** The modal factorization system *)

Section ModalFact.
  Context `{fs : Funext} (O : Modality).

  (** Lemma 7.6.4 *)
  Definition image {A B : Type} (f : A -> B)
  : Factorization (@IsConnMap O) (@MapIn O) f.
  Proof.
    refine (Build_Factorization {b : B & O (hfiber f b)}
                                (fun a => (f a ; to O _ (a;1)))
                                pr1
                                (fun a => 1)
                                _ _).
    - exact (conn_map_compose O
              (equiv_fibration_replacement f)
              (functor_sigma idmap (fun b => to O (hfiber f b)))).
    - intros b.
      exact (inO_equiv_inO _ (hfiber_fibration b (O o (hfiber f)))).
  Defined.

  (** This is the composite of the three displayed equivalences at the beginning of the proof of Lemma 7.6.5.  Note that it involves only a single factorization of [f]. *)
  Lemma O_hfiber_O_fact {A B : Type} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f) (b : B)
  : O (hfiber (factor2 fact o factor1 fact) b)
      <~> hfiber (factor2 fact) b.
  Proof.
    refine (equiv_compose' _
             (equiv_O_functor O
               (hfiber_compose (factor1 fact) (factor2 fact) b))).
    refine (equiv_compose'
             (equiv_sigma_contr (fun w => O (hfiber (factor1 fact) w.1)))
             _).
    - intros w; exact (inclass1 fact w.1).
    - refine (equiv_inverse
                (equiv_sigma_inO_O (fun w => hfiber (factor1 fact) w.1))).
      exact (inclass2 fact b).
  Defined.

  (** This is the corresponding first three of the displayed "mapsto"s in proof of Lemma 7.6.5, and also the last three in reverse order, generalized to an arbitrary path [p].  Note that it is much harder to prove than in the book, because we are working in the extra generality of a modality where [O_ind_beta] is only propositional. *)
  Lemma O_hfiber_O_fact_inverse_beta {A B : Type} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f)
        (a : A) (b : B) (p : factor2 fact (factor1 fact a) = b)
  : (O_hfiber_O_fact fact b)^-1
      (factor1 fact a ; p) = to O _ (a ; p).
  Proof.
    set (g := factor1 fact); set (h := factor2 fact).
    apply moveR_equiv_V.
    unfold O_hfiber_O_fact.
    ev_equiv.
    apply moveL_equiv_M.
    transitivity (existT (fun (w : hfiber h b) => O (hfiber g w.1))
                         (g a; p) (to O (hfiber g (g a)) (a ; 1))).
    - apply moveR_equiv_V; reflexivity.
    - apply moveL_equiv_V.
      transitivity (to O _ (existT (fun (w : hfiber h b) => (hfiber g w.1))
                         (g a; p) (a ; 1))).
      + simpl; repeat rewrite O_rec_beta; reflexivity.
      + symmetry; apply to_O_natural.
  Qed.

  Section TwoFactorizations.
    Context {A B : Type} (f : A -> B)
            (fact fact' : Factorization (@IsConnMap O) (@MapIn O) f).

    Let H := fun x => fact_factors fact x @ (fact_factors fact' x)^.

    (** Lemma 7.6.5, part 1. *)
    Definition equiv_O_factor_hfibers (b:B)
    : hfiber (factor2 fact) b <~> hfiber (factor2 fact') b.
    Proof.
      refine (equiv_compose' (O_hfiber_O_fact fact' b) _).
      refine (equiv_compose' _ (equiv_inverse (O_hfiber_O_fact fact b))).
      apply equiv_O_functor.
      apply equiv_hfiber_homotopic.
      exact H.
    Defined.

    (** Lemma 7.6.5, part 2. *)
    Definition equiv_O_factor_hfibers_beta (a : A)
    : equiv_O_factor_hfibers (factor2 fact (factor1 fact a))
                             (factor1 fact a ; 1)
      = (factor1 fact' a ; (H a)^).
    Proof.
      unfold equiv_O_factor_hfibers.
      ev_equiv.
      apply moveR_equiv_M.
      do 2 rewrite O_hfiber_O_fact_inverse_beta.
      unfold equiv_fun, equiv_O_functor.
      transitivity (to O _
                       (equiv_hfiber_homotopic
                          (factor2 fact o factor1 fact)
                          (factor2 fact' o factor1 fact') H
                          (factor2 fact (factor1 fact a)) (a;1))).
      - refine (to_O_natural O _ _).
      - apply ap.
        simpl.
        apply ap; auto with path_hints.
    Qed.

  End TwoFactorizations.

  (** Theorem 7.6.6.  Recall that a lot of hard work was done in [Factorization.path_factorization]. *)
  Definition O_factsys : FactorizationSystem.
  Proof.
    refine (Build_FactorizationSystem
              (@IsConnMap O) _ _ _
              (@MapIn O) _ _ _
              (@image) _).
    intros A B f fact fact'.
    refine (Build_PathFactorization fact fact' _ _ _ _).
    - refine (equiv_compose' _ (equiv_fibration_replacement (factor2 fact))).
      refine (equiv_compose' (equiv_inverse (equiv_fibration_replacement (factor2 fact'))) _).
      refine (equiv_functor_sigma' (equiv_idmap B) _); intros b; simpl.
      apply equiv_O_factor_hfibers.
    - intros a; exact (pr1_path (equiv_O_factor_hfibers_beta f fact fact' a)).
    - intros x.
      exact ((equiv_O_factor_hfibers f fact fact' (factor2 fact x) (x ; 1)).2 ^).
    - intros a.
      apply moveR_pM.
      refine ((inv_V _)^ @ _ @ inv_V _); apply inverse2.
      refine (_ @ pr2_path (equiv_O_factor_hfibers_beta f fact fact' a)).
      refine (_ @ (transport_paths_Fl _ _)^).
      (** Apparently Coq needs a little help to see that these paths are the same. *)
      match goal with
          |- ((?p)^ @ ?q)^ = _ @ _ => change ((p^ @ q)^ = q^ @ p)
      end.
      refine (inv_pp _ _ @ (1 @@ inv_V _)).
  Defined.

End ModalFact.

End Modalities_Theory.

(** ** Restriction of a family of modalities *)

(** This is just like restriction of reflective subuniverses. *)
Module Type Modalities_Restriction_Data (Os : Modalities).

  Parameter New_Modality : Type2@{u a}.

  Parameter Modalities_restriction
  : New_Modality -> Os.Modality.

End Modalities_Restriction_Data.

Module Modalities_Restriction
       (Os : Modalities)
       (Res : Modalities_Restriction_Data Os)
<: Modalities.

  Definition Modality := Res.New_Modality.

  Definition O_reflector (O : Modality@{u a})
    := Os.O_reflector@{u a i} (Res.Modalities_restriction O).
  Definition inO_internal (O : Modality@{u a})
    := Os.inO_internal@{u a i} (Res.Modalities_restriction O).
  Definition O_inO_internal (O : Modality@{u a})
    := Os.O_inO_internal@{u a i} (Res.Modalities_restriction O).
  Definition to (O : Modality@{u a})
    := Os.to@{u a i} (Res.Modalities_restriction O).
  Definition inO_equiv_inO_internal (O : Modality@{u a})
    := Os.inO_equiv_inO_internal@{u a i} (Res.Modalities_restriction O).
  Definition hprop_inO_internal (H : Funext) (O : Modality@{u a})
    := Os.hprop_inO_internal@{u a i} H (Res.Modalities_restriction O).
  Definition O_ind_internal (O : Modality@{u a})
    := Os.O_ind_internal@{u a i j k} (Res.Modalities_restriction O).
  Definition O_ind_beta_internal (O : Modality@{u a})
    := Os.O_ind_beta_internal@{u a i j k} (Res.Modalities_restriction O).
  Definition minO_paths (O : Modality@{u a})
    := Os.minO_paths@{u a i} (Res.Modalities_restriction O).

End Modalities_Restriction.

(** For examples of modalities, see the files Notnot, Identity, Nullification, PropositionalFracture, and hit/Localization. *)
