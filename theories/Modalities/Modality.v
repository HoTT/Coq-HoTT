(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Extensions Factorization NullHomotopy Pullback.
Require Export ReflectiveSubuniverse. (* [Export] because many of the lemmas and facts about reflective subuniverses are equally important for modalities. *)

Local Open Scope path_scope.

(** * Modalities *)

(** ** Dependent eliminators *)

(** A dependent version of the reflection universal property.  For later use we generalize it to refer to different subuniverses in the reflection and the elimination target. *)
Class ReflectsD@{i} (O' O : Subuniverse@{i}) (T : Type@{i})
      `{PreReflects@{i} O' T} :=
{
  extendable_to_OO :
    forall (Q : O_reflector O' T -> Type@{i}) {Q_inO : forall x, In O (Q x)},
      ooExtendableAlong (to O' T) Q
}.  

(** In particular, from this we get a dependent eliminator. *)
Definition OO_ind {O' : Subuniverse} (O : Subuniverse)
           {A : Type} `{ReflectsD O' O A}
           (B : O_reflector O' A -> Type) {B_inO : forall oa, In O (B oa)}
           (f : forall a, B (to O' A a)) (oa : O_reflector O' A)
  : B oa
  := (fst (extendable_to_OO B 1%nat) f).1 oa.

Definition OO_ind_beta {O' O : Subuniverse} {A : Type} `{ReflectsD O' O A}
           (B : O_reflector O' A -> Type) {B_inO : forall oa, In O (B oa)}
           (f : forall a, B (to O' A a)) (a : A)
  : OO_ind O B f (to O' A a) = f a
  := (fst (extendable_to_OO B 1%nat) f).2 a.

(** Conversely, if [O] is closed under path-types, a dependent eliminator suffices to prove the whole dependent universal property. *)
Definition reflectsD_from_OO_ind@{i} {O' O : Subuniverse@{i}}
           {A : Type@{i}} `{PreReflects O' A}
           (OO_ind' : forall (B : O_reflector O' A -> Type@{i})
                             (B_inO : forall oa, In O (B oa))
                             (f : forall a, B (to O' A a))
                             oa, B oa)
           (OO_ind_beta' : forall (B : O_reflector O' A -> Type@{i})
                             (B_inO : forall oa, In O (B oa))
                             (f : forall a, B (to O' A a))
                             a, OO_ind' B B_inO f (to O' A a) = f a)
           (inO_paths' : forall (B : Type@{i}) (B_inO : In O B)
                      (z z' : B), In O (z = z'))
  : ReflectsD O' O A.
Proof.
  constructor.
  intros Q Q_inO n.
  revert Q Q_inO. simple_induction n n IHn; intros Q Q_inO.
  1:exact tt.
  split.
  - intros g.
    exists (OO_ind' Q _ g).
    rapply OO_ind_beta'.
  - intros h k.
    rapply IHn.
Defined.

(** In particular, this is the case if [O] is a reflective subuniverse. *)
Definition reflectsD_from_RSU {O' : Subuniverse} {O : ReflectiveSubuniverse}
           {A : Type} `{PreReflects O' A}
           (OO_ind' : forall (B : O_reflector O' A -> Type)
                             (B_inO : forall oa, In O (B oa))
                             (f : forall a, B (to O' A a))
                             oa, B oa)
           (OO_ind_beta' : forall (B : O_reflector O' A -> Type)
                             (B_inO : forall oa, In O (B oa))
                             (f : forall a, B (to O' A a))
                             a, OO_ind' B B_inO f (to O' A a) = f a)
  : ReflectsD O' O A
  := reflectsD_from_OO_ind OO_ind' OO_ind_beta' _.

(** Of course, with funext this becomes an actual equivalence. *)
Definition isequiv_oD_to_O
           {fs : Funext} (O' O : Subuniverse) {A : Type} `{ReflectsD O' O A}
           (B : O_reflector O' A -> Type) `{forall a, In O (B a)}
  : IsEquiv (fun (h : forall oa, B oa) => h oD to O' A).
Proof.
  apply isequiv_ooextendable, extendable_to_OO; assumption.
Defined.


(** ** The strong order *)

(** Note the reversal of the order: [O1 << O2] means that [O2] has dependent eliminators into [O1]. *)
Class O_strong_leq (O1 O2 : ReflectiveSubuniverse)
  := reflectsD_strong_leq : forall A, ReflectsD O2 O1 A.
Global Existing Instance reflectsD_strong_leq.

Notation "O1 << O2" := (O_strong_leq O1 O2) (at level 70) : subuniverse_scope.
Open Scope subuniverse_scope.

(** The strong order implies the weak order. *)
Global Instance O_leq_strong_leq {O1 O2 : ReflectiveSubuniverse} `{O1 << O2}
  : O1 <= O2.
Proof.
  intros A A_inO1.
  srapply inO_to_O_retract.
  - exact (OO_ind O1 (fun _:O2 A => A) idmap).
  - intros a. srapply OO_ind_beta.
Defined.

(** The strong order is not obviously transitive, but it composes with the weak order on one side at least. *)
Definition O_strong_leq_trans_l (O1 O2 O3 : ReflectiveSubuniverse)
           `{O1 <= O2} `{O2 << O3}
  : O1 << O3.
Proof.
  intros A; constructor; intros B B_inO.
  apply (extendable_to_OO (O := O2)).
  intros x.
  srapply inO_leq; apply B_inO.
Defined.


(** ** Modalities  *)

(** A modality is a reflective subuniverse with a dependent universal property with respect to itself. *)
Notation IsModality O := (O << O).

(** However, it's not clear what the best bundled definition of modality is.  The obvious one [{ O : ReflectiveSubuniverse & IsModality O}] has the advantage that bundling a reflective subuniverse into a modality and then unbundling it is definitionally the identity; but it is redundant, since the dependent universal property implies the non-dependent one, and in practice most modalities are constructed directly with a dependent eliminator.  Thus, for now at least, we take the following definition, which in RSS is called a "uniquely eliminating modality".  *)
Record Modality@{i} := Build_Modality'
{
  modality_subuniv : Subuniverse@{i} ;
  modality_prereflects : forall (T : Type@{i}),
      PreReflects modality_subuniv T ;
  modality_reflectsD : forall (T : Type@{i}),
      ReflectsD modality_subuniv modality_subuniv T ;
}.

Global Existing Instance modality_reflectsD.
(** We don't declare [modality_subuniv] as a coercion or [modality_prereflects] as a global instance, because we want them only to be found by way of the following "unbundling" coercion to reflective subuniverses. *)

Definition modality_to_reflective_subuniverse (O : Modality@{i})
  : ReflectiveSubuniverse@{i}.
Proof.
  refine (Build_ReflectiveSubuniverse
            (modality_subuniv O) (modality_prereflects O) _).
  intros T; constructor.
  intros Q Q_inO.
  srapply extendable_to_OO.
Defined.

Coercion modality_to_reflective_subuniverse : Modality >-> ReflectiveSubuniverse.

(** Unfortunately, sometimes [modality_subuniv] pops up anyway.  The following hint helps typeclass inference look through it. *)
Hint Extern 0 (In (modality_subuniv _) _) => progress change modality_subuniv with (rsu_subuniv o modality_to_reflective_subuniverse) in * : typeclass_instances.

(** Modalities are precisely the reflective subuniverses that are [<<] themselves.  *)
Global Instance ismodality_modality (O : Modality) : IsModality O.
Proof.
  intros A; exact _.
Defined.

Definition modality_ismodality (O : ReflectiveSubuniverse) `{IsModality O} : Modality.
Proof.
  rapply Build_Modality'.
Defined.

(** Of course, modalities have dependent eliminators. *)
Definition O_ind {O : Subuniverse} {A : Type} `{ReflectsD O O A}
  := @OO_ind O O A _ _.
Arguments O_ind {O A _ _} B {B_inO} f oa.
Definition O_ind_beta {O : Subuniverse} {A : Type} `{ReflectsD O O A}
  := @OO_ind_beta O O A _ _.
Arguments O_ind_beta {O A _ _} B {B_inO} f a.

(** Conversely, as remarked above, we can build a modality from a dependent eliminator as long as we assume the modal types are closed under paths.  This is probably the most common way to define a modality, and one might argue that this would be a better definition of the bundled type [Modality].  For now we simply respect that by dignifying it with the unprimed constructor name [Build_Modality]. *)
Definition Build_Modality
           (In' : Type -> Type)
           (hprop_inO' : Funext -> forall T : Type, IsHProp (In' T))
           (inO_equiv_inO' : forall T U : Type,
               In' T -> forall f : T -> U, IsEquiv f -> In' U)
           (O_reflector' : Type -> Type)
           (O_inO' : forall T, In' (O_reflector' T))
           (to' : forall T, T -> O_reflector' T)
           (O_ind' : forall (A : Type) (B : O_reflector' A -> Type)
                            (B_inO : forall oa, In' (B oa))
                            (f : forall a, B (to' A a))
                            (z : O_reflector' A),
               B z)
           (O_ind_beta' : forall (A : Type) (B : O_reflector' A -> Type)
                                 (B_inO : forall oa, In' (B oa))
                                 (f : forall a, B (to' A a)) (a : A),
               O_ind' A B B_inO f (to' A a) = f a)
           (inO_paths' : forall (A : Type) (A_inO : In' A) (z z' : A),
               In' (z = z'))
  : Modality.
Proof.
  pose (O := Build_Subuniverse In' hprop_inO' inO_equiv_inO').
  simple refine (Build_Modality' O _ _); intros T.
  - exact (Build_PreReflects O T (O_reflector' T) (O_inO' T) (to' T)).
  - srapply reflectsD_from_OO_ind. 
    + rapply O_ind'.
    + rapply O_ind_beta'.
    + rapply inO_paths'.
Defined.

(** When combined with [isequiv_oD_to_O], this yields Theorem 7.7.7 in the book. *)
Definition isequiv_oD_to_O_modality
           `{Funext} (O : Modality) {A : Type}
           (B : O A -> Type) `{forall a, In O (B a)}
  : IsEquiv (fun (h : forall oa, B oa) => h oD to O A).
Proof.
  srapply (isequiv_oD_to_O O O).
Defined.


(** ** Dependent sums *)

(** A dependent elimination of a reflective subuniverse [O'] into [O] implies that the sum of a family of [O]-modal types over an [O']-modal type is [O']-modal.  More specifically, for a particular such sum it suffices for the [O']-reflection of that sum to dependently eliminate into [O]. *)
Global Instance inO_sigma_reflectsD
       {O' : ReflectiveSubuniverse} {O : Subuniverse}
       {A : Type} (B : A -> Type) `{!ReflectsD O' O (sig B)}
       `{In O' A} `{forall a, In O (B a)}
  : In O' {x:A & B x}.
Proof.
  pose (h := fun x => @O_rec O' ({x:A & B x}) A _ _ _ pr1 x).
  assert (p := (fun z => O_rec_beta pr1 z) : h o (to O' _) == pr1).
  pose (g := fun z => (transport B ((p z)^) z.2)).
  simpl in *.
  pose (f := OO_ind O (fun x:O' (sig B) => B (h x)) g).
  pose (q := OO_ind_beta (fun x:O' (sig B) => B (h x)) g).
  apply inO_to_O_retract with (mu := fun w => (h w; f w)).
  intros [x1 x2].
  simple refine (path_sigma B _ _ _ _); simpl.
  - apply p.
  - refine (ap _ (q (x1;x2)) @ _).
    unfold g; simpl. exact (transport_pV B _ _).
Defined.

(** Specialized to a modality, this yields the implication (ii) => (i) from Theorem 7.7.4 of the book, and also Corollary 7.7.8, part 2. *)
Global Instance inO_sigma (O : Modality)
           {A:Type} (B : A -> Type) `{In O A} `{forall a, In O (B a)}
  : In O {x:A & B x}
  := _.

(** This implies that the composite of modal maps is modal. *)
Global Instance mapinO_compose {O : Modality} {A B C : Type} (f : A -> B) (g : B -> C)
       `{MapIn O _ _ f} `{MapIn O _ _ g}
  : MapIn O (g o f).
Proof.
  intros c.
  refine (inO_equiv_inO' _ (hfiber_compose f g c)^-1).
Defined.

(** It also implies Corollary 7.3.10 from the book, generalized to modalities.  (Theorem 7.3.9 is true for any reflective subuniverse; we called it [equiv_O_sigma_O].) *)
Corollary equiv_sigma_inO_O {O : Modality} {A : Type} `{In O A} (P : A -> Type)
  : {x:A & O (P x)} <~> O {x:A & P x}.
Proof.
  transitivity (O {x:A & O (P x)}).
  - rapply equiv_to_O.
  - apply equiv_O_sigma_O.
Defined.

(** Conversely, if the sum of a particular family of [O]-modal types over an [O']-reflection is in [O'], then that family admits a dependent eliminator. *)
Definition extension_from_inO_sigma
           {O' : Subuniverse} (O : Subuniverse)
           {A:Type} `{Reflects O' A} (B: O_reflector O' A -> Type)
           {inO_sigma : In O' {z:O_reflector O' A & B z}}
           (g : forall x, B (to O' A x))
  : ExtensionAlong (to O' A) B g.
Proof.
  set (Z := sigT B) in *.
  pose (g' := (fun a:A => (to O' A a ; g a)) : A -> Z).
  pose (f' := O_rec (O := O') g').
  pose (eqf := (O_rec_beta g')  : f' o to O' A == g').
  pose (eqid := O_indpaths (pr1 o f') idmap (fun x => ap@{k i} pr1 (eqf x))).
  exists (fun z => transport B (eqid z) ((f' z).2)).
  intros a. unfold eqid.
  refine (_ @ pr2_path (O_rec_beta g' a)).
  refine (ap (fun p => transport B p (O_rec g' (to O' A a)).2) _).
  srapply O_indpaths_beta.
Defined.

(** And even a full equivalence of spaces of sections.  This is stated in CORS Proposition 2.8 (but our version avoids funext by using [ooExtendableAlong], as usual).  *)
Definition ooextendable_from_inO_sigma
           {O' : ReflectiveSubuniverse} (O : Subuniverse)
           {A : Type} (B: O_reflector O' A -> Type)
           {inO_sigma : In O' {z:O_reflector O' A & B z}}
  : ooExtendableAlong (to O' A) B.
Proof.
  intros n; generalize dependent A.
  induction n as [|n IHn]; intros; [ exact tt | cbn ].
  refine (extension_from_inO_sigma O B , _).
  intros h k; nrapply IHn.
  set (Z := sigT B) in *.
  pose (W := sigT (fun a => B a * B a)).
  nrefine (inO_equiv_inO' (Pullback (A := W) (fun a:O_reflector O' A => (a;(h a,k a)))
                                   (fun z:Z => (z.1;(z.2,z.2)))) _).
  { refine (inO_pullback O' _ _).
    exact (inO_equiv_inO' _ (equiv_sigprod_pullback B B)^-1). }
  unfold Pullback.
  (** The rest is just extracting paths from sigma- and product types and contracting a couple of based path spaces. *)
  apply equiv_functor_sigma_id; intros z; cbn. 
  refine (_ oE equiv_functor_sigma_id _).
  2:intros; symmetry; apply equiv_path_sigma.
  refine (_ oE equiv_functor_sigma_id (fun z => equiv_functor_sigma_id (fun p => _))).
  2:symmetry; apply equiv_path_prod.
  cbn. make_equiv_contr_basedpaths.
Defined.

(** Thus, if this holds for all sigma-types, we get the dependent universal property.  Making this an [Instance] causes typeclass search to spin.  Note the slightly different hypotheses, which mean that we can't just use the previous result: here we need only assume that the [O']-reflection of [A] exists rather than that [O'] is fully reflective, at the cost of assuming that [O] is fully reflective (although actually, closed under path-spaces would suffice). *)
Definition reflectsD_from_inO_sigma
           {O' : Subuniverse} (O : ReflectiveSubuniverse)
           {A : Type} `{Reflects O' A}
           (inO_sigma : forall (B: O_reflector O' A -> Type),
               (forall oa, In O (B oa)) -> In O' {z:O_reflector O' A & B z})
  : ReflectsD O' O A.
Proof.
  constructor; intros B B_inO.
  intros n; generalize dependent A.
  induction n as [|n IHn]; intros; [ exact tt | cbn ].
  refine (extension_from_inO_sigma O B , _).
  intros h k; rapply IHn.
Defined.

(** In particular, we get the converse implication (i) => (ii) from Theorem 7.7.4 of the book: a reflective subuniverse closed under sigmas is a modality. *)
Definition modality_from_inO_sigma (O : ReflectiveSubuniverse)
           (H : forall (A:Type) (B:A -> Type)
                       {A_inO : In O A} `{forall a, In O (B a)},
               (In O {x:A & B x}))
  : Modality.
Proof.
  refine (Build_Modality' O _ _).
  intros; srapply reflectsD_from_inO_sigma.
Defined.


(** ** Connectedness of the units *)

(** Dependent reflection can also be characterized by connectedness of the unit maps. *)
Global Instance conn_map_to_O_reflectsD {O' : Subuniverse} (O : ReflectiveSubuniverse)
       {A : Type} `{ReflectsD O' O A}
  : IsConnMap O (to O' A).
Proof.       
  apply conn_map_from_extension_elim.
  intros P P_inO f.
  exact (fst (extendable_to_OO (O := O) P 1%nat) f).
Defined.

Definition reflectsD_from_conn_map_to_O {O' : Subuniverse} (O : ReflectiveSubuniverse)
           {A : Type} `{PreReflects O' A} `{IsConnMap O _ _ (to O' A)}
  : ReflectsD O' O A.
Proof.
  constructor; rapply ooextendable_conn_map_inO.
Defined.

(** In particular, if [O1 << O2] then every [O2]-unit is [O1]-connected. *)
Global Instance conn_map_to_O_strong_leq
       {O1 O2 : ReflectiveSubuniverse} `{O1 << O2} (A : Type)
  : IsConnMap O1 (to O2 A)
  := _.

(** Thus, if [O] is a modality, then every [O]-unit is [O]-connected.  This is Corollary 7.5.8 in the book. *)
Global Instance conn_map_to_O {O : Modality} (A : Type)
  : IsConnMap O (to O A)
  := _.


(** ** Easy modalities *)

(** The book uses yet a different definition of modality, which requires an induction principle only into families of the form [fun oa => O (B oa)], and similarly only that path-spaces of types [O A] are "modal" in the sense that the unit is an equivalence.  As shown in section 1 of RSS, this is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].

Our definitions are more convenient in formalized applications because in some examples (such as [Trunc] and closed modalities), there is a naturally occurring [O_ind] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.  Thus, when we apply general theorems about modalities to a particular modality such as [Trunc], the proofs will reduce definitionally to "the way we would have proved them directly" if we didn't know about general modalities.

On the other hand, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. *)

Section EasyModalities.

  Context (O_reflector : Type@{i} -> Type@{i})
          (to : forall (T : Type@{i}), T -> O_reflector T)
          (O_indO
           : forall (A : Type@{i})
                    (B : O_reflector A -> Type@{i})
                    (f : forall a, O_reflector (B (to A a)))
                    (z : O_reflector A),
              O_reflector (B z))
          (O_indO_beta
           : forall (A : Type@{i})
                    (B : O_reflector A -> Type@{i})
                    (f : forall a, O_reflector (B (to A a))) (a : A),
              O_indO A B f (to A a) = f a)
          (inO_pathsO
           : forall (A : Type@{i}) (z z' : O_reflector A),
              IsEquiv (to (z = z'))).

  Local Definition In_easy : Type@{i} -> Type@{i}
    := fun A => IsEquiv (to A).

  Local Definition O_ind_easy
             (A : Type) (B : O_reflector A -> Type)
             (B_inO : forall oa, In_easy (B oa))
    : (forall a, B (to A a)) -> forall oa, B oa.
  Proof.
    simpl; intros f oa.
    pose (H := B_inO oa); unfold In_easy in H.
    apply ((to (B oa))^-1).
    apply O_indO.
    intros a; apply to, f.
  Defined.

  Local Definition O_ind_easy_beta
             (A : Type) (B : O_reflector A -> Type)
             (B_inO : forall oa, In_easy (B oa))
             (f : forall a : A, B (to A a)) (a:A)
  : O_ind_easy A B B_inO f (to A a) = f a.
  Proof.
    unfold O_ind_easy.
    apply moveR_equiv_V.
    apply @O_indO_beta with (f := fun x => to _ (f x)).
  Qed.

  Local Definition O_inO_easy (A : Type) : In_easy (O_reflector A).
  Proof.
    refine (isequiv_adjointify (to (O_reflector A))
             (O_indO (O_reflector A) (fun _ => A) idmap) _ _).
    - intros x; pattern x; apply O_ind_easy.
      + intros oa; apply inO_pathsO.
      + intros a; apply ap.
        exact (O_indO_beta (O_reflector A) (fun _ => A) idmap a).
    - intros a.
      exact (O_indO_beta (O_reflector A) (fun _ => A) idmap a).
  Defined.

  (** It seems to be surprisingly hard to show repleteness (without univalence).  We basically have to manually develop enough functoriality of [O] and naturality of [to O]. *)
  Local Definition inO_equiv_inO_easy (A B : Type)
        (A_inO : In_easy A) (f : A -> B) (feq : IsEquiv f)
    : In_easy B.
  Proof.
    simple refine (isequiv_commsq (to A) (to B) f
             (O_ind_easy A (fun _ => O_reflector B) _ (fun a => to B (f a))) _).
    - intros; apply O_inO_easy.
    - intros a; refine (O_ind_easy_beta A (fun _ => O_reflector B) _ _ a).
    - apply A_inO.
    - simple refine (isequiv_adjointify _
               (O_ind_easy B (fun _ => O_reflector A) _ (fun b => to A (f^-1 b))) _ _);
        intros x.
      + apply O_inO_easy.
      + pattern x; refine (O_ind_easy B _ _ _ x); intros.
        * apply inO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_easy_beta; apply ap, eisretr).
      + pattern x; refine (O_ind_easy A _ _ _ x); intros.
        * apply inO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_easy_beta; apply ap, eissect).
  Defined.

  Local Definition inO_paths_easy (A : Type) (A_inO : In_easy A) (a a' : A)
    : In_easy (a = a').
  Proof.
    simple refine (inO_equiv_inO_easy (to A a = to A a') _ _
                                      (@ap _ _ (to A) a a')^-1 _).
    - apply inO_pathsO.
    - refine (@isequiv_ap _ _ _ A_inO _ _).
    - apply isequiv_inverse.
  Defined.

  Definition easy_modality : Modality
    := Build_Modality In_easy _ inO_equiv_inO_easy O_reflector O_inO_easy to O_ind_easy O_ind_easy_beta inO_paths_easy.

End EasyModalities.


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
  Defined.

  Global Instance conn_map_factor1_image {A B : Type} (f : A -> B)
  : IsConnMap O (factor1 (image f))
    := inclass1 (image f).

  Global Instance inO_map_factor1_image {A B : Type} (f : A -> B)
  : MapIn O (factor2 (image f))
    := inclass2 (image f).

  (** This is the composite of the three displayed equivalences at the beginning of the proof of Lemma 7.6.5.  Note that it involves only a single factorization of [f]. *)
  Lemma O_hfiber_O_fact {A B : Type} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f) (b : B)
  : O (hfiber (factor2 fact o factor1 fact) b)
      <~> hfiber (factor2 fact) b.
  Proof.
    refine (_ oE
             (equiv_O_functor O
               (hfiber_compose (factor1 fact) (factor2 fact) b))).
    nrefine (equiv_sigma_contr (fun w => O (hfiber (factor1 fact) w.1)) oE _).
    - intros w; exact (inclass1 fact w.1).
    - nrefine ((equiv_sigma_inO_O (fun w => hfiber (factor1 fact) w.1))^-1)%equiv.
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
      + cbn; repeat rewrite O_rec_beta; reflexivity.
      + destruct p; symmetry; apply to_O_natural.
  Qed.

  Section TwoFactorizations.
    Context {A B : Type} (f : A -> B)
            (fact fact' : Factorization (@IsConnMap O) (@MapIn O) f).

    Let H := fun x => fact_factors fact x @ (fact_factors fact' x)^.

    (** Lemma 7.6.5, part 1. *)
    Definition equiv_O_factor_hfibers (b:B)
    : hfiber (factor2 fact) b <~> hfiber (factor2 fact') b.
    Proof.
      refine (O_hfiber_O_fact fact' b oE _).
      refine (_ oE (O_hfiber_O_fact fact b)^-1).
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
    simple refine (Build_PathFactorization fact fact' _ _ _ _).
    - refine (_ oE equiv_fibration_replacement (factor2 fact)).
      refine ((equiv_fibration_replacement (factor2 fact'))^-1 oE _).
      apply equiv_functor_sigma_id; intros b; simpl.
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
