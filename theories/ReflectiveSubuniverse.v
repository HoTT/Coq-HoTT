Require Import Overture PathGroupoids HProp Equivalences EquivalenceVarieties.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe types.ObjectClassifier.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Reflective Subuniverses *)

Section Reflective_Subuniverse.
  Context {ua : Univalence}.
  Context {fs : Funext}.

  (** A reflective subuniverse is the data of : *)

  Record ReflectiveSubuniverse :=
    { 
      (** a predicate [U -> Prop] *)
      in_subuniverse : Type -> hProp ;
      (** we define the type of modal types *)
      SubuniverseType := {T : Type & (in_subuniverse) T} ;
      (** for every type [T], a type [O T] such that [in_subuniverse (O T)] *)
      to_O : Type -> SubuniverseType ; 
      (** for every type [T], a map [A -> O T] *)
      O_unit : forall T, T -> (to_O T).1; 
      (** an equivalence [((O P)->Q) <~> (P -> Q)] *)
      O_isequiv : forall (P : Type) (Q : SubuniverseType), 
                  IsEquiv (fun f : (to_O P).1 -> Q.1 => f o (@O_unit P)) 
    }.

  Local Notation O := to_O.

  Coercion SubuniverseType_pr1 subU (T:SubuniverseType subU) := @pr1 Type subU.(in_subuniverse) T.

  (** The equivalence arising from [O_isequiv] *)
  Definition O_equiv {subU} (P : Type) (Q : SubuniverseType subU)
    : (subU.(O) P -> Q) <~> (P -> Q)
    := BuildEquiv _ _ (fun f => f o (O_unit subU P)) (O_isequiv subU P Q).

  (** Some shortcuts to manipulate the above equivalence.  Here is a "recursor" for [O]. *)
  Definition O_rec {subU} (P : Type) (Q : SubuniverseType subU)
    : (P -> Q) -> (subU.(O) P) -> Q
    := (O_equiv P Q)^-1.

  (** Here is its "computation rule" *)
  Definition O_rec_retr {subU} (P : Type) (Q : SubuniverseType subU) f
    : O_rec _ _ f o subU.(O_unit) _ = f
    := @eisretr _ _ _ (subU.(O_isequiv) P Q) f.

  (** Versions of [O_rec_retr] with [compose] unfolded and that are
     further pre- or post-composed with another function.  This
     enables [rewrite] to recognize them. *)
  Definition O_rec_retr' {subU} (P : Type) (Q : SubuniverseType subU) f
    : (fun x => O_rec _ _ f (subU.(O_unit) _ x)) = f
    := O_rec_retr P Q f.
  Definition O_rec_retr'_pre {subU} (P A : Type) (Q : SubuniverseType subU) f (g : A -> P)
    : (fun x => O_rec _ _ f (subU.(O_unit) _ (g x))) = f o g
    := ap (fun k => k o g) (O_rec_retr P Q f).
  Definition O_rec_retr'_post {subU} (P B : Type) (Q : SubuniverseType subU) f (h : Q -> B)
    : (fun x => h (O_rec _ _ f (subU.(O_unit) _ x))) = h o f
    := ap (fun k => h o k) (O_rec_retr P Q f).
  Definition O_rec_retr'_prepost {subU} (P A B : Type) (Q : SubuniverseType subU) f (g : A -> P) (h : Q -> B)
    : (fun x => h (O_rec _ _ f (subU.(O_unit) _ (g x)))) = h o f o g
    := ap (fun k => h o k o g) (O_rec_retr P Q f).

  (** And a tactic that tries them all *)
  Ltac rewrite_O_rec_retr :=
    repeat first
      [ unfold compose; rewrite O_rec_retr'
        | unfold compose; rewrite O_rec_retr'_post
        | unfold compose; rewrite O_rec_retr'_pre
        | unfold compose; rewrite O_rec_retr'_prepost
      ].

  (** Here is the "uniqueness rule" for the "recursor" *)
  Definition O_rec_sect {subU} (P : Type) (Q : SubuniverseType subU) f
    : O_rec _ _ (f o subU.(O_unit) _) = f
    := @eissect _ _ _ (subU.(O_isequiv) P Q) f.

  Section Basic_facts.

    Variable subU : ReflectiveSubuniverse.

    (** The second component of [subuniverse_Type] is unique *)
    Definition path_SubuniverseType
    : forall (T T' : SubuniverseType subU), T.1 = T'.1 -> T = T'.
    Proof.
      intros [T h] [T' h'] X.
      apply (path_sigma _ _ _ X).
      apply allpath_hprop.
    Defined.

    (** The subuniverse structure is transportable *)
    Definition ReflectiveSubuniverse_transport T U (f : T <~> U)
    : (subU.(in_subuniverse) T) -> (subU.(in_subuniverse) U)
    := transport (in_subuniverse subU) (path_universe_uncurried f).
    
    (** Unit maps are equivalences iff they admit a retraction *)
    Definition O_unit_retract_isequiv (T:Type) (mu : (subU.(O) T) -> T) (eta := subU.(O_unit) T)
    : Sect eta mu -> IsEquiv eta.
    Proof.
      unfold Sect; intros H. apply isequiv_adjointify with (g:=mu).
      - assert (X : eta o mu o eta = idmap o eta).
        apply (ap (fun g => eta o g)).
        exact (path_forall _ _ H).
        apply ap10.
        apply ((ap (O_equiv T (O subU T)))^-1); simpl.
        exact X.
      - exact H.
    Defined.

    (** A type is modal if and only if its unit map is an equivalence : *)

    Instance isequiv_O_unit (P : SubuniverseType subU)
    : IsEquiv (subU.(O_unit) P).
    Proof.
      apply O_unit_retract_isequiv with (mu := (O_rec P P idmap)).
      exact (ap10 (O_rec_retr P P idmap)).
    Defined.

    Definition equiv_O_unit (P : SubuniverseType subU)
      : P <~> subU.(O) P
      := (BuildEquiv _ _ (subU.(O_unit) P) (isequiv_O_unit _)).

    Definition O_modal (T:SubuniverseType subU)
    : T = subU.(O) T.
    Proof.
      apply path_SubuniverseType. 
      apply path_universe_uncurried.
      apply equiv_O_unit.
    Defined.

    Definition O_unit_isequiv_iff_modal (T:Type)
    : IsEquiv (subU.(O_unit) T) <-> (subU.(in_subuniverse) T).
    Proof.
      split.
      - intros e.
        apply (ReflectiveSubuniverse_transport (O subU T)).
        * apply equiv_inverse.
          eexists; exact e.
        * exact ((O subU T).2).
      - intros X; exact (isequiv_O_unit (T;X)).
    Defined.

    (* Hence, a type is modal if its unit admits a retraction. *)
    Definition O_unit_retract_modal (T:Type) (mu : (subU.(O) T) -> T) (eta := subU.(O_unit) T) (iss : Sect eta mu)
    : subU.(in_subuniverse) T
    := fst (O_unit_isequiv_iff_modal T) (O_unit_retract_isequiv T mu iss).

    (** The modality is idempotent *)
    Definition O_idempotent
    : forall T, (O subU) (((O subU) T)) = O subU T.
    Proof.
      intro T; symmetry; apply O_modal.
    Defined.

    (** A little commutation property between [O_rec] and [eta] *)
    
    Definition O_rec_O_unit (A : SubuniverseType subU) (B : Type)
               (f : B -> A) (x : (O subU B))
    : O_unit subU A (O_rec B A f x) = O_rec B (O subU A) ((O_unit subU A) o f) x
      :=  (((fun U => (ap10 (O_rec_sect B (O subU A) U) x))
              (O_unit subU A o O_rec B A f))^)
            @ ((ap (fun u => O_rec B (O subU A)
                                   (O_unit subU A o u) x)
                   (inverse (O_rec_retr B A f)))^).

    (** The universal property commutes with [eta] *)
    
    Definition path_arrow_modal (A:Type) (B:SubuniverseType subU)
      (f g:(O subU A) -> B) (eta := O_unit subU A)
      : ((f o eta = g o eta) -> (f=g))
      := @equiv_inj _ _ _ (O_isequiv subU A B) _ _.
    
    Definition ap10_path_arrow_modal (A:Type) (B:SubuniverseType subU) (f g:(O subU A) -> B)
               (eta := O_unit subU A) (pi : (f o eta = g o eta))
    : forall a, ap10 (path_arrow_modal A B _ _ pi) (eta a) = ap10 pi a.
    Proof.
      intros a.
      refine ((ap_ap10_L _ _ eta (path_arrow_modal A B f g pi) a) ^ @ _).
      apply (ap (fun h => ap10 h a)).
      unfold path_arrow_modal, equiv_inj.
      apply eisretr.
    Qed.

  End Basic_facts.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)
    Variable subU : ReflectiveSubuniverse.
    
    Definition O_functor (A B : Type) (f : A -> B)
    : (subU.(O) A) -> (subU.(O) B).
    Proof.
      apply O_rec; intro x; apply subU.(O_unit); apply f; exact x.
    Defined.

    (* What is this for? *)
    Definition O_functor_modal_square (A : Type) (B : SubuniverseType subU) (f : A -> B)
    : ((equiv_O_unit _ B) ^-1)  o  (O_functor A B f)  o  (subU.(O_unit) A)
      =  f.
    Proof.
      apply path_arrow; intro x; unfold compose, O_functor; simpl.
      pose ((ap10 ((O_rec_retr A (subU.(O) B)) ((O_unit subU B) o f)) x)^).
      exact (transport (fun U => O_rec B B (fun x : B => x) U = f x)
                       ((ap10 ((O_rec_retr A (subU.(O) B)) ((O_unit subU B) o f)) x)^)
                       (ap10 (O_rec_retr B B idmap) (f x))).
    Defined.

    (** Functoriality on composition *)
    Definition O_functor_compose (A B C : Type) ( f : A -> B) (g : B -> C)
    : (O_functor A C (g o f)) = (O_functor B C g) o (O_functor A B f).
    Proof.
      apply path_arrow_modal; unfold O_functor.
      rewrite_O_rec_retr.
      reflexivity.
    Defined.

    (** Hence functoriality on commutative squares *)
    Definition O_functor_square (A B C X : Type) (pi1 : X -> A) (pi2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o pi1) = (g o pi2))
    : ( (O_functor A C f) o (O_functor X A pi1) )
      = ( (O_functor B C g) o (O_functor X B pi2) ).
    Proof.
      transitivity (O_functor X C (f o pi1)).
      - symmetry; apply O_functor_compose.
      - transitivity (O_functor X C (g o pi2)).
        * apply ap; exact comm.
        * apply O_functor_compose.
    Defined.

  End Functor.

  Section Types.

    Variable subU : ReflectiveSubuniverse.

    (** ** The [Unit] type *)
    Lemma in_subuniverse_unit : (subU.(in_subuniverse) Unit).
    Proof.
      apply O_unit_retract_modal with (mu := fun x:(subU.(O) Unit) => tt).
      exact (@contr Unit _).
    Defined.
    
    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Definition in_subuniverse_forall (A:Type) (B:A -> Type) 
    : (forall x, (subU.(in_subuniverse) (B x)))
      -> ((subU.(in_subuniverse)) (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rec _ (B x; H x) (ev x)).
      apply O_unit_retract_modal with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      pose (foo := O_rec_retr _ (B x; H x) (fun f : forall x0, (B x0) => f x)).
      exact (ap10 foo phi).
    Qed.

    Definition in_subuniverse_arrow (A : Type) (B : SubuniverseType subU)
    : (in_subuniverse subU (A -> B)).
    Proof.
      apply in_subuniverse_forall.
      intro a. exact B.2.
    Qed.

    (** ** Product *)
    Definition in_subuniverse_prod (A B : SubuniverseType subU)
    : (in_subuniverse subU (A*B)).
    Proof.
      apply O_unit_retract_modal with
        (mu := fun X => (O_rec (A * B) A fst X , O_rec (A * B) B snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (ap10 (O_rec_retr (A * B) A fst) (a,b)). 
      - exact (ap10 (O_rec_retr (A * B) B snd) (a,b)). 
    Qed.

    (** We show that [OA*OB] has the same universal property as [O(A*B)] *)
    Lemma equiv_O_prod_rect (A B : Type) (C : SubuniverseType subU)
    : ((O subU A)*(O subU B) -> C) <~> (A * B -> C).
    Proof.
      apply (equiv_compose' (equiv_uncurry A B C)).
      refine (equiv_compose' _ (equiv_inverse (equiv_uncurry (O subU A) (O subU B) C))).
      apply (equiv_compose' (O_equiv A (B -> C ; in_subuniverse_arrow B C))); simpl.
      apply equiv_postcompose'.
      exact (O_equiv B C).
    Qed.

    (** TODO : [O(A*B) = OA * OB] *)

    (** ** Dependent sums *)
    (** Theorem 7.7.4 *)
    Definition in_subuniverse_sigma_iff
    : (forall (A:SubuniverseType subU) (B:A -> SubuniverseType subU),
         (in_subuniverse subU ({x:A & B x})))
      <->
      (forall (A:Type) (B: (O subU A) -> SubuniverseType subU)
              (g : forall (a:A), (B (O_unit subU A a))),
         {f : forall (z:(O subU A)), (B z) & forall a:A, f (O_unit subU A a) = g a}).
    Proof.
      split.
      - intro H. intros A B g.
        pose (Z := (sigT B ; H (O subU A) B) : SubuniverseType subU).
        pose (g' := (fun a:A => (O_unit subU A a ; g a)) : A -> Z).
        pose (f' := O_rec _ _ g').
        pose (eqf := (O_rec_retr _ _ g')  : f' o O_unit subU A = g').
        pose (eqid := path_arrow_modal subU A (O subU A) (pr1 o f') idmap
                        (ap (fun k => pr1 o k) eqf)).
        exists (fun z => transport B (ap10 eqid z) ((f' z).2)); intros a.
        unfold eqid. rewrite ap10_path_arrow_modal.
        refine (_ @ pr2_path (ap10 (O_rec_retr A Z g') a)).
        apply (ap (fun p => transport B p _)).
        exact ((ap_ap10 (f' o O_unit subU A) g' pr1 eqf a)^).
      - intros H A B.
        pose (h := fun x => O_rec ({x:A & B x}) A pr1 x).
        pose (p := (fun z => ap10 (O_rec_retr ({x : A & B x}) A pr1) z)
                : h o (O_unit _ _) == pr1).
        pose (g := fun z => (transport B ((p z)^) z.2)).
        simpl in *.
        specialize (H ({x:A & B x}) (B o h) g).
        destruct H as [f q].
        apply O_unit_retract_modal with (mu := fun w => (h w; f w)).
        intros [x1 x2].
        refine (path_sigma B _ _ _ _); simpl.
        * apply p.
        * rewrite (q (x1;x2)).
          unfold g; simpl. exact (transport_pV B _ _).
    Qed.

    (** ** Paths *)

    Definition in_subuniverse_paths (S:SubuniverseType subU) (x y:S)
    : (in_subuniverse subU (x=y)).
    Proof.
      refine (O_unit_retract_modal subU _ _ _); intro u.
      - assert (p : (fun _:(O subU (x=y)) => x) = (fun _=> y)). 
        { apply ((ap (O_equiv (x=y) S))^-1).
          apply path_arrow; intro v. exact v. }
        exact (ap10 p u).
      - hnf.
        rewrite <- ap_ap10_L.
        rewrite eisretr. 
        rewrite ap10_path_arrow; reflexivity.
    Qed.
    
  End Types.
End Reflective_Subuniverse.