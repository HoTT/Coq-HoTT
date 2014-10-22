(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties Factorization NullHomotopy.
Require Export ReflectiveSubuniverse. (* [Export] because many of the lemmas and facts about reflective subuniverses are equally important for modalities. *)
Require Import HoTT.Tactics.

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

(** ** Easy modalities *)

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

(** ** Modalities are reflective subuniverses *)

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
    abstract (repeat (rewrite O_ind_beta; simpl); reflexivity).
  - unfold Sect; apply O_ind; try exact _.
    intros [a op]; revert op; apply O_ind; try exact _; intros p; simpl.
    abstract (repeat (rewrite O_ind_beta; simpl); reflexivity).
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

Class IsConnected (O : Modality) (A : Type)
  := isconnected_contr_O : Contr (O A).

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
  Definition isconnected_equiv A {B} (f : A -> B) `{IsEquiv _ _ f}
  : IsConnected O A -> IsConnected O B.
  Proof.
    intros ?; refine (contr_equiv (O A) (O_functor O f)).
  Defined.

  Definition isconnected_equiv' A {B} (f : A <~> B)
  : IsConnected O A -> IsConnected O B
    := isconnected_equiv A f.

  Definition isconnected_elim {A} `{IsConnected O A} C `{In O C} (f : A -> C)
  : NullHomotopy f.
  Proof.
    set (ff := @O_rec O _ _ _ f).
    exists (ff (center _)).
    intros a. symmetry.
    refine (ap ff (contr (to O _ a)) @ _).
    apply O_rec_beta.
  Defined.

  Definition isconnected_from_elim {A}
  : (forall (C : Type) `{In O C} (f : A -> C), NullHomotopy f)
    -> IsConnected O A.
  Proof.
    intros H.
    set (nh := H (O A) _ (to O A)).
    exists (nh .1).
    apply O_ind; try exact _.
    intros; symmetry; apply (nh .2).
  Defined.

  (** A type which is both connected and truncated is contractible. *)

  Definition contr_trunc_conn {A} `{In O A} `{IsConnected O A}
  : Contr A.
  Proof.
    apply (contr_equiv _ (to O A)^-1).
  Defined.

End ConnectedTypes.

(** ** Modally truncated maps *)

(** A map is "in [O]" if each of its fibers is. *)

Class MapIn (O : Modality) {A B : Type} (f : A -> B)
  := inO_hfiber_ino_map : forall (b:B), In O (hfiber f b).

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
  Definition mapinO_homotopic {A B} (f : A -> B) {g : A -> B}
             (p : f == g) `{MapIn O _ _ f}
  : MapIn O g.
  Proof.
    intros b.
    refine (inO_equiv_inO (hfiber f b)
                          (equiv_hfiber_homotopic f g p b)).
  Defined.

  (** Being modal is an hprop *)
  Global Instance ishprop_mapinO `{Funext} {A B} (f : A -> B)
  : IsHProp (MapIn O f).
  Proof.
    apply trunc_forall.
  Defined.

  (** The composite of modal maps is modal *)
  Global Instance mapinO_compose {A B C} (f : A -> B) (g : B -> C)
         `{MapIn O _ _ f} `{MapIn O _ _ g}
  : MapIn O (g o f).
  Proof.
    intros c.
    refine (inO_equiv_inO _ (hfiber_compose f g c)^-1).
  Defined.

End ModalMaps.

(** ** Modally connected maps *)

(** Connectedness of a map can again be defined in two equivalent ways: by connectedness of its fibers (as types), or by the lifting property/elimination principle against truncated types.  We use the former; the equivalence with the latter is given below in [conn_map_elim], [conn_map_comp], and [conn_map_from_extension_elim]. *)

Class IsConnMap (O : Modality) {A B : Type} (f : A -> B)
  := isconnected_hfiber_conn_map : forall b:B, IsConnected O (hfiber f b).

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
  Global Instance ishprop_isconnmap `{Funext} {A B} (f : A -> B)
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

  Definition isequiv_conn_ino_map {A B} (f : A -> B)
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

  (** Conversely, if a map satisfies this elimination principle (expressed via extensions), then it is connected.  This completes the proof of Lemma 7.5.7 from the book.

Conceptually, this proof can be seen as an instance of the fact that a left adjoint (here, pullback) preserves a left class of maps if the right adjoint (here, dependent product) preserves the right class. *)
  Lemma conn_map_from_extension_elim {A B : Type} (f : A -> B)
  : (forall (P : B -> Type) {P_inO : forall b:B, In O (P b)}
            (d : forall a:A, P (f a)),
       ExtensionAlong f P d)
    -> IsConnMap O f.
  Proof.
    intros Hf b. apply isconnected_from_elim. intros X ? d.
    set (P := fun (b':B) => (b' = b) -> X).
    assert (forall b', In O (P b')).
    { intros. apply inO_arrow; exact _. }
    set (dP := (fun (a:A) (p:f a = b) => (d (a;p)))
               : forall a:A, P (f a)).
    set (e := Hf P _ dP).
    exists (e .1 b 1).
    intros [a p]. symmetry. transitivity (e .1 (f a) p).
    2: exact (ap10 (e.2 a) p).
    refine (ap011D e.1 p^ _).
    refine (transport_paths_l _ _ @ _). hott_simpl.
  Defined.

  (** Corollary 7.5.8: It follows that the unit maps [to O A] are connected. *)
  Global Instance conn_map_to_O (A : Type) : IsConnMap O (to O A).
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (O_ind P d); intros a.
    apply O_ind_beta.
  Defined.

  (** Lemma 7.5.6: Connected maps compose and cancel on the right. *)
  Global Instance conn_map_compose {A B C} (f : A -> B) (g : B -> C)
         `{IsConnMap O _ _ f} `{IsConnMap O _ _ g}
  : IsConnMap O (g o f).
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (conn_map_elim g P (conn_map_elim f (P o g) d)); intros a.
    exact (conn_map_comp g P _ _ @ conn_map_comp f (P o g) d a).
  Defined.      

  Definition cancelR_conn_map {A B C} (f : A -> B) (g : B -> C)
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

    Context {A B} {P : A -> Type} {Q : B -> Type}
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
             {A} {P Q : A -> Type} (f : forall a, P a -> Q a)
             `{IsConnMap O _ _ (functor_sigma idmap f)}
  : forall a, IsConnMap O (f a).
  Proof.
    intros a q.
    refine (isconnected_equiv' O (hfiber (functor_sigma idmap f) (a;q)) _ _).
    exact (hfiber_functor_sigma_idmap P Q f a q).
  Defined.

  (** Lemma 7.5.14: Connected maps are inverted by [O]. *)
  Global Instance O_inverts_conn_map {A B} (f : A -> B)
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
      unfold compose; refine (O_rec_beta _ _ @ _).
      transitivity (O_functor O pr1 (to O (hfiber f (f a)) (a;1))).
      + apply ap, contr.
      + apply to_O_natural.
  Defined.

End ConnectedMaps.

(** ** The modal factorization system *)

Section ModalFact.
  Context `{fs : Funext} (O : Modality).

  (** Lemma 7.6.4 *)
  Definition image {A B} (f : A -> B)
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
  Lemma O_hfiber_O_fact {A B} {f : A -> B}
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

  (** TODO: Put this somewhere else or do without it. *)
  Definition ev_equiv_compose {A B C} (f : A <~> B) (g : B <~> C) (a : A)
  : (equiv_compose' g f) a = g (f a)
    := 1.

  (** This is the corresponding first three of the displayed "mapsto"s in proof of Lemma 7.6.5, and also the last three in reverse order, generalized to an arbitrary path [p].  Note that it is much harder to prove than in the book, because we are working in the extra generality of a modality where [O_ind_beta] is only propositional. *)
  Lemma O_hfiber_O_fact_inverse_beta {A B} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f)
        (a : A) (b : B) (p : factor2 fact (factor1 fact a) = b)
  : equiv_inverse (O_hfiber_O_fact fact b)
      (factor1 fact a ; p) = to O _ (a ; p).
  Proof.
    set (g := factor1 fact); set (h := factor2 fact).
    apply moveR_equiv_V.
    unfold O_hfiber_O_fact.
    repeat rewrite ev_equiv_compose.
    apply moveL_equiv_M.
    transitivity (existT (fun (w : hfiber h b) => O (hfiber g w.1))
                         (g a; p) (to O (hfiber g (g a)) (a ; 1))).
    - apply moveR_equiv_V; reflexivity.
    - apply moveL_equiv_V.
      transitivity (to O _ (existT (fun (w : hfiber h b) => (hfiber g w.1))
                         (g a; p) (a ; 1))).
      + simpl; unfold compose.
        repeat (rewrite O_ind_beta; simpl); reflexivity.
      + simpl rewrite O_ind_beta; reflexivity.
  Qed.

  (** And a re-typing of that. *)
  Definition O_hfiber_O_fact_inverse_beta' {A B} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f)
        (a : A) (b : B) (p : factor2 fact (factor1 fact a) = b)
  : (O_hfiber_O_fact fact b)^-1
      (factor1 fact a ; p) = to O _ (a ; p)
    := O_hfiber_O_fact_inverse_beta fact a b p.

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
      rewrite !ev_equiv_compose.
      rewrite O_hfiber_O_fact_inverse_beta.
      apply moveR_equiv_M.
      rewrite O_hfiber_O_fact_inverse_beta'.
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
      match goal with |- ((?pp)^ @ ?qq)^ = (?qq')^ @ ?pp' =>
          pose (p := pp); pose (q := qq); change ((p^ @ q)^ = q^ @ p)
      end.
      refine (inv_pp p^ q @ (1 @@ inv_V p)).
  Defined.

End ModalFact.

(** ** Examples *)

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
