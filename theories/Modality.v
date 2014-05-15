Require Import Overture PathGroupoids HProp Equivalences UnivalenceAxiom.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Forall types.Prod.

Local Open Scope path_scope.

(** * Reflexive Subuniverses *)
Section Reflexive_Subuniverse.
  Context {Fun : Funext}.

  (** A reflective subuniverse is the data of : *)

  Record subuniverse_struct :=
    Build_subuniverse_struct {
        (** a predicate U -> Prop *)
        subuniverse_HProp : forall (T:Type), {T:Type & IsHProp T} ;
        (** for every type A, a type (O A) such that (subuniverse_HProp (O A)) *)
        O : Type -> {T : Type & (subuniverse_HProp T).1} ;
        (** for every type A, a map A -> O A *)
        O_unit : forall T, T -> (O T).1;
        (** an equivalence ((O A)->B) <~> (A -> B) *)
        O_equiv : forall (P : Type) (Q :{T : Type & (subuniverse_HProp T).1}),
                    IsEquiv (fun f : (O P).1 -> Q.1 => f o (@O_unit P))
      }.

  (** We define the type of modal types :*)

  Definition subuniverse_Type subU :=
    {T : Type & (subU.(subuniverse_HProp) T).1}.

  (** Some shortcuts to manipulate the above equivalence *)
  Definition O_rec {subU} (P : Type) (Q : subuniverse_Type subU) :
    (P -> Q.1) -> (subU.(O) P).1 -> Q.1 :=
    (@equiv_inv _ _ _ (subU.(O_equiv) _ _)).

  Definition O_rec_retr {subU} (P : Type) (Q : subuniverse_Type subU) f
  : O_rec _ _ f o subU.(O_unit) _ = f :=
    @eisretr _ _ _ (subU.(O_equiv) P Q) f.

  Definition O_rec_sect {subU} (P : Type) (Q : subuniverse_Type subU) f :=
    @eissect _ _ _ (subU.(O_equiv) P Q) f.

  Section Basic_facts.

    Variable subU : subuniverse_struct.

    (** The second component of subunivere_Type is unique *)
    Definition unique_subuniverse
    : forall (T T' : subuniverse_Type subU), T.1 = T'.1 -> T = T'.
      intros. destruct T, T'. eapply (path_sigma _ _ _ X).
      simpl in X; destruct X.
      apply (allpath_hprop (H := (subuniverse_HProp subU x).2)).
    Defined.

    (** The subuniverse structure is transportable *)
    Definition subuniverse_struct_transport T U (f : (T <~> U)%equiv)
    : (subU.(subuniverse_HProp) T).1 -> (subU.(subuniverse_HProp) U).1.
      apply univalence_axiom in f. rewrite f.
      intro x; exact x.
    Defined.

    (** Unit maps are equivalences iff they admit a retraction *)
    Definition O_unit_retract_equiv (T:Type) (μ : (subU.(O) T).1 -> T) (η := subU.(O_unit) T)
    : Sect η μ -> IsEquiv η.
      unfold Sect; intros H. apply isequiv_adjointify with (g:=μ).
      - assert (η o μ o η = idmap o η).
        unfold compose at 3.
        apply (ap (fun g => η o g)).
        apply path_forall; intro y.
        exact (H y).
        apply ap10.
        apply (elim_E (f := (fun f : (O subU T) .1 -> (O subU T) .1 => f o O_unit subU T))).
        exact ((subU.(O_equiv) T (subU.(O) T))).
        exact X.
      - exact H.
    Defined.

    (** A type is modal if and only if its unit map is an equivalence : *)

    Instance O_modal_equiv (P : subuniverse_Type subU) : IsEquiv (subU.(O_unit) P.1).
    apply O_unit_retract_equiv with (μ := (O_rec P.1 P idmap)).
    pose (f := O_rec_retr P.1 P idmap).
    intro. eapply ap10 in f. exact (f x).
    Defined.


    Definition O_modal (T:subuniverse_Type subU) : T = subU.(O) T.1.
      apply unique_subuniverse.
      apply univalence_axiom.
      exact (BuildEquiv _ _ (subU.(O_unit) (T.1)) (O_modal_equiv _)).
    Defined.


    Definition subuniverse_iff_O (T:Type) :
      IsEquiv (subU.(O_unit) T) = (subU.(subuniverse_HProp) T).1.

      apply univalence_axiom.

      exact (@equiv_iff_hprop
               (IsEquiv (O_unit subU T))
               _
               (subuniverse_HProp subU T).1
               (subuniverse_HProp subU T).2
               (fun X => subuniverse_struct_transport _ _
                             (BuildEquiv _ _ _
                                         (isequiv_inverse (H:=X)))
                             ((subU.(O) T)).2)
               (fun X => O_modal_equiv (T;X))).
    Defined.

    (** The modality is involutive *)
    Definition O_invol : forall T, (O subU) (((O subU) T).1) = O subU T.
      intro T; symmetry; apply O_modal.
    Defined.

    (** A little commutation property between O_rec and eta *)

    Definition O_rec_O_unit (A : subuniverse_Type subU) (B : Type)
               (f : B -> A.1) (x : (O subU B).1)
    : O_unit subU A.1 (O_rec B A f x) = O_rec B (O subU A.1) ((O_unit subU A.1) o f) x
      :=  (((fun U => (ap10 (O_rec_sect B (O subU A.1) U) x))
              (O_unit subU A .1 o O_rec B A f))^)
            @ ((ap (fun u => O_rec B (O subU A.1)
                                   (O_unit subU A.1 o u) x)
                   (inverse (O_rec_retr B A f)))^).

    (** The universal property commutes with eta *)

    Definition equal_fun_modal (A:Type) (B:subuniverse_Type subU)
               (f g:(O subU A).1 -> B.1) (η := O_unit subU A)
    : ((f o η = g o η) -> (f=g))
      := fun H => (((eissect _ (IsEquiv := (O_equiv subU A B)) f)^)
                     @ (ap equiv_inv H))
                     @ (eissect _ (IsEquiv := (O_equiv subU A B)) g).

    Lemma universality_unit_lemma (oA A B: Type) (η : A -> oA) (f g : oA -> B)
          (inv : (A -> B) -> oA -> B) (π : f o η = g o η)
          (eisretr : forall x:A -> B, (inv x) o η = x)
          (eissect : forall x : oA -> B, inv (x o η) = x) a
    : ap10 (ap inv π) (η a)
      = (ap10 (eisretr (f o η)) a @ ap10 π a)
          @ (ap10 (eisretr (g o η)) a)^.
    Proof.
      destruct π. simpl. rewrite concat_p1. rewrite concat_pV. exact idpath.
    Qed.

    Definition universality_unit (A:Type) (B:subuniverse_Type subU) (f g:(O subU A).1 -> B.1)
               (η := O_unit subU A) (π : (f o η = g o η))
    : forall a, ap10 (equal_fun_modal A B _ _ π) (η a) = ap10 π a.
      intro a. unfold equal_fun_modal. destruct (O_equiv subU A B). simpl. unfold Sect in *.
      repeat rewrite ap10_pp. rewrite ap10_V. rewrite concat_pp_p.
      apply moveR_Mp. apply moveR_pM. rewrite inv_V.
      assert (ap10 (eisretr (g o η)) a = ap10 (eissect g) (η a)).
      fold η in eisadj; rewrite (eisadj g). apply ap_ap10_L.
      rewrite <- X; clear X.
      assert (ap10 (eisretr (f o η)) a =
              ap10 (eissect f) (η a)).
      fold η in eisadj; rewrite (eisadj f). apply ap_ap10_L.
      rewrite <- X. clear X.
      apply (universality_unit_lemma _ _ _ _ _ _ equiv_inv  π eisretr eissect a).
    Qed.

  End Basic_facts.

  Section Functions_lifts.

    (** In this section, we see how the ○ operator acts on maps *)
    Variable subU : subuniverse_struct.


    Definition function_lift (A B : Type) (f : A -> B)
    : (subU.(O) A).1 -> (subU.(O) B).1.
      apply O_rec; intro x; apply subU.(O_unit); apply f; exact x.
    Defined.

    Definition function_lift_modal (A:Type) (B:subuniverse_Type subU) (f : A -> B.1)
    : (O subU A).1 -> B.1.
      apply O_rec. exact f.
    Defined.

    (* Notation "'○' f" := (function_lift _ _ f) (at level 0). *)
    (* Notation "'○' f" := (function_lift_modal _ _ f) (at level 0). *)

    Definition function_lift_modal_square (A : Type) (B : subuniverse_Type subU) (f : A -> B.1)
    : (@equiv_inv _ _ (subU.(O_unit) B.1) (O_modal_equiv _ B))
        o (function_lift A B.1 f)
        o (subU.(O_unit) A)
      =  f.
      apply path_forall; intro x; unfold compose, function_lift; simpl.
      exact (transport (fun U => O_rec B .1 B (fun x : (B) .1 => x) U = f x)
                       ((ap10 ((O_rec_retr A (subU.(O) B.1)) ((O_unit subU B.1) o f)) x)^)
                       (ap10 (O_rec_retr B.1 B idmap) (f x))).
    Defined.

    (** Function lift is ok with composition *)
    Definition function_lift_compose (A B C : Type) ( f : A -> B) (g : B -> C) :
      (function_lift A C (g o f)) = (function_lift B C g) o (function_lift A B f).
      apply path_forall; intro x; simpl.
      unfold function_lift.
      fold ( (O_unit subU C) o g).
      fold ( (O_unit subU B) o f).

      assert (P1 : O_rec A (O subU C) (fun x0 : A => O_unit subU C ((g o f) x0)) x
                   = O_rec A (O subU C) (((O_unit subU C) o g) o f) x).
      exact idpath.

      assert (P2 : O_rec A (O subU C) (((O_unit subU C) o g) o f) x
                   = O_rec A (O subU C)
                           (((O_rec B (O subU C) (O_unit subU C o g) o O_unit subU B) o f)) x).
      apply ap10. apply ap. apply ap10. apply ap.
      exact (inverse (O_rec_retr B (O subU C) (O_unit subU C o g))).

      assert (P3 : O_rec A (O subU C)
                         (O_rec B (O subU C) (O_unit subU C o g) o O_unit subU B o f) x
                   = O_rec A (O subU C)
                           (O_rec B (O subU C) (O_unit subU C o g) o (O_unit subU B o f)) x).
      exact idpath.

      assert (P4 : O_rec A (O subU C)
                         (O_rec B (O subU C) (O_unit subU C o g) o (O_unit subU B o f)) x
                   = O_rec A (O subU C)
                           (O_rec B (O subU C) (O_unit subU C o g) o
                                  (O_rec A (O subU B) (O_unit subU B o f) o O_unit subU A)) x).
      apply ap10. repeat apply ap.
      exact (inverse (O_rec_retr A (O subU B) (O_unit subU B o f))).
      exact (P1 @ P2 @ P3 @ P4 @
                (ap10 (O_rec_sect A (O subU C)
                                  (O_rec B (O subU C)
                                         (O_unit subU C o g)
                                         o O_rec A (O subU B) (O_unit subU B o f))) x)).
    Defined.

    (** Hence function lift is ok with commutative squares *)

    Definition function_lift_square (A B C X : Type) (π1 : X -> A) (π2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o π1) = (g o π2))
    : ( (function_lift A C f) o (function_lift X A π1) )
      = ( (function_lift B C g) o (function_lift X B π2) ).
      apply path_forall; intro x; simpl.
      pose (foo1 := ap10 (function_lift_compose X A C π1 f) x).
      pose (foo2 := ap10 (function_lift_compose X B C π2 g) x).
      pose (foo3 := ap (fun u => O_rec X (O subU C) (fun x0 => O_unit subU C (u x0)) x) (x:=f o π1) (y:=g o π2) comm). simpl in foo3.
      exact (concat (concat (inverse foo1) foo3) foo2).
    Defined.

  End Functions_lifts.

  Section Types.

    Variable subU : subuniverse_struct.

    (** The Unit type *)
    Lemma unit_subuniverse : (subU.(subuniverse_HProp) Unit).1.
      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (μ := fun x:(subU.(O) Unit).1 => tt).
      intro u.
      destruct u; exact idpath.
    Defined.

    (** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Definition forall_subuniverse (A:Type) (B:A -> Type)
    : (forall x, (subU.(subuniverse_HProp) (B x)).1)
      -> ((subU.(subuniverse_HProp)) (forall x:A, (B x))).1.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (ζ := fun x:A => O_rec (forall x0 : A, (B x0) ) (B x; H x) (ev x)).
      pose (h := fun z => fun x => ζ x z).
      simpl in *.
      rewrite <- (subuniverse_iff_O).
      set (η := (O_unit subU (forall x : A, (B x)))).
      apply O_unit_retract_equiv with (μ := h).
      intro φ.
      unfold h, ζ, ev; clear h; clear ζ; clear ev.
      apply path_forall; intro x.
      pose (foo := @O_rec_retr subU (forall x0 : A, (B x0)) (B x; H x)
                               (fun f : forall x0 : A, (B x0) => f x)).
      exact (ap10 foo φ).
    Qed.

    Definition arrow_subuniverse (A : Type) (B : subuniverse_Type subU)
    : (subuniverse_HProp subU (A -> B.1)).1.
      apply forall_subuniverse.
      intro a. exact B.2.
    Qed.

    (** Product *)
    Definition product_subuniverse (A B : subuniverse_Type subU)
    : (subuniverse_HProp subU (A.1*B.1)).1.
      rewrite <- subuniverse_iff_O.

      pose (μ := fun (X : (O subU (A.1 * B.1)).1) =>
                   (O_rec (A.1 * B.1) (A)
                          (fun x : (A.1 * B.1) => (fst x)) X ,
                    O_rec (A.1 * B.1) (B)
                          (fun x : (A.1 * B.1) => (snd x)) X)).
      apply O_unit_retract_equiv with (μ := μ).
      intro x; destruct x as [a b].
      unfold μ; apply path_prod.
      - simpl.
        exact (ap10 (O_rec_retr (A.1 * B.1) A (fun x : (A.1 * B.1) => fst x)) (a,b)).
      - simpl.
        exact (ap10 (O_rec_retr (A.1 * B.1) B (fun x : (A.1 * B.1) => snd x)) (a,b)).
    Qed.

    (** We show that ○A*○B has the same universal property as ○(A*B) *)
    Lemma product_universal (A B : Type) (C : subuniverse_Type subU)
    : Equiv (A * B -> C.1) ((O subU A).1*(O subU B).1 -> C.1).
      apply (@equiv_compose' _ (A -> B -> C.1) _).
      Focus 2.
      exists (fun f => fun u v => f (u,v)).
      apply isequiv_adjointify with (g := fun u => fun x => u (fst x) (snd x)).
      intro x. apply path_forall; intro u; apply path_forall; intro v. exact idpath.
      intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.

      apply (@equiv_compose' _ ((O subU A).1 -> B -> C.1) _).
      Focus 2. apply equiv_inverse.
      exists (fun f : (((O subU A) ) .1
                       -> (existT (fun S => (subuniverse_HProp subU S).1)
                                  (B -> C.1)
                                  (arrow_subuniverse B C)).1)
              => f o O_unit subU A).
      exact (O_equiv subU A (( B -> C.1) ; arrow_subuniverse B C)).

      apply (@equiv_compose' _ ((O subU A).1 -> (O subU B).1 -> C.1) _).
      exists (fun f => fun u => f (fst u) (snd u)).
      apply isequiv_adjointify with (g := fun f => fun u v => f (u,v)).
      intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.
      intro x. apply path_forall; intro u. apply path_forall; intro v. exact idpath.

      apply equiv_postcompose'.
      apply equiv_inverse.
      exists (fun f : ((O subU B) ) .1 -> (C ) .1 => f o O_unit subU B).
      exact (O_equiv subU B C).
    Qed.

    (** TODO : ○(A*B) = ○A * ○B *)

    (** Dependent sums *)
    (** Theorem 7.7.4 *)
    Definition sigma_subuniverse
    : (forall (A:subuniverse_Type subU) (B:A.1 -> subuniverse_Type subU),
         (subuniverse_HProp subU ({x:A.1 & (B x).1})).1)
      <->
      (forall (A:Type) (B: (O subU A).1 -> subuniverse_Type subU)
              (g : forall (a:A), (B (O_unit subU A a)).1),
         {f : forall (z:(O subU A).1), (B z).1 & forall a:A, f (O_unit subU A a) = g a}).
      split.
      - intro H. intros A B g.
        pose (Z := existT (fun T => (subuniverse_HProp subU T).1)
                          ({z:(O subU A).1 & (B z).1})
                          (H (O subU A) B)).
        pose (g' := (fun a:A => (O_unit subU A a ; g a)) : A -> Z.1).
        pose (f' := O_rec _ _ g').
        pose (eqf :=fun a:A => (ap10 (O_rec_retr _ _ g') a)).
        pose (g'' := fun x => (f' x).1).
        pose (f'' := fun x:(O subU A).1 => x).
        pose (eq'' := path_forall _ _ (fun x => @ap _ _ pr1 _ _ (eqf x))).
        assert (g'' o (O_unit subU A) = f'' o (O_unit subU A)).
        exact eq''.
        pose (eq''' := ap10 (equal_fun_modal _ A (O subU A) (g'') (f'') (eq''))).
        pose (f := fun z => (f' z).2). simpl in f.
        set (η := O_unit subU A) in *.

        exists (fun z => transport (fun u => (B u).1) (eq''' z) (f z)).
        intro a.

        pose (p := projT1_path (eqf a)). simpl in p.
        pose (q := projT2_path (eqf a)). simpl in q.

        rewrite <- q.
        assert ( (eq''' (η a)) =  (eqf a) ..1).
        unfold eq''', projT1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, η in *;
          simpl in *.
        rewrite universality_unit.
        unfold path_forall. rewrite eisretr. exact idpath.
        exact (ap (fun v => transport (fun u => (B u) .1) v (f' (η a)) .2) X0).
      - intros H A B.
        pose (h := fun x => O_rec ({x:A.1 & (B x).1}) A pr1 x).
        pose (p := fun z => ap10 (O_rec_retr ({x : A.1 | (B x).1}) A pr1) z).
        pose (C := fun w => B(h w)).
        pose (g := fun z => (transport (fun u => (B u).1) (inverse (p z)) z.2)).
        simpl in *.
        specialize (H ({x:A.1 & (B x).1}) C g).
        destruct H as [f q]. simpl in q.
        pose (k := (fun w => (h w; f w))
                   : (O subU ({x:A.1 & (B x).1})).1 -> ({x:A.1 & (B x).1})); simpl in k.

        rewrite <- subuniverse_iff_O.
        apply O_unit_retract_equiv with (μ := k).

        intro x; destruct x as [x1 x2]. unfold k.
        apply (path_sigma _ (O_rec {x : A .1 | (B x) .1} A pr1
                                   (O_unit subU {x : A .1 | (B x) .1} (x1; x2));
                             f (O_unit subU {x : A .1 | (B x) .1} (x1; x2)))
                          (x1;x2) (p (x1;x2))).
        rewrite (q (x1;x2)). unfold g; simpl. rewrite <- transport_pp. rewrite concat_Vp.
        exact idpath.
    Qed.

    (** Pullbacks and paths *)

    Definition pullback {A B C : Type} (f : A -> C) (g : B -> C)
      := {a:A & {b: B & f a = g b}}.

    Lemma pullback_subuniverse (A B C : subuniverse_Type subU) (f : A.1 -> C.1) (g : B.1 -> C.1)
    : (subU.(subuniverse_HProp) (pullback f g)).1.
      rewrite <- subuniverse_iff_O.
      (* TODO *)
    Admitted.

    Lemma paths_subuniverse (S:subuniverse_Type subU) (x y:S.1)
    : (subuniverse_HProp subU (x=y)).1.
      assert (((x=y) <~> (@pullback Unit Unit S.1 (fun u => x) (fun u => y)))%equiv).
      unfold pullback.
      exists (fun X => existT (fun _ => {_ : Unit | x=y}) tt (existT (fun _ => x=y) tt X)).
      apply isequiv_adjointify with (g := fun X : {_ : Unit | {_ : Unit | x=y}} => X.2.2).
      - intro u. destruct u as [tt1 [tt2 u]]. simpl.
        destruct tt1; destruct tt2. exact idpath.
      - intro u. destruct u. exact idpath.
      - apply (subuniverse_struct_transport subU (pullback (unit_name x) (unit_name y))).
        apply equiv_inverse; exact X.
        apply (pullback_subuniverse (Unit;unit_subuniverse) (Unit;unit_subuniverse) S).
    Qed.

  End Types.
End Reflexive_Subuniverse.
Set Implicit Arguments.

(** * Modalities *)
(** Quoting the HoTT Book: *)
(** Definition 7.7.5. A _modality_ is an operation [○ : Type → Type] for which there are

    (i) functions [η^○_A : A → ○(A)] for every type [A]

    (ii) for every [A : Type] and every type family [B : ○(A) → Type], a function

         [ind_○ : (∀ a : A, ○(B(η^○_A(a)))) → (∀ z : ○(A), ○(B(z)))]

    (iii) A path [ind_○(f)(η^○_A(a)) = f(a)] for each [f : ∀ a : A, ○(B(η^○_A(a)))].

    (iv) For any [z z' : ○(A)], the function [η^○_{z = z'} : (z = z') → ○(z = z')] is an equivalence. *)

Class IsModality (mod : Type -> Type) :=
  { modality_eta : forall A, A -> mod A;
    modality_ind : forall A (B : mod A -> Type),
                     (forall a, mod (B (modality_eta a)))
                     -> forall z, mod (B z);
    modality_ind_compute : forall A B (f : forall a : A, mod (B _)) a,
                             modality_ind _ f (modality_eta a) = f a;
    modality_isequiv_eta_path :> forall A (z z' : mod A),
                                   IsEquiv (@modality_eta (z = z')) }.

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
