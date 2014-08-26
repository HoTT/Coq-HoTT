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
      (** a predicate U -> Prop *)
      subuniverse_HProp : Type -> hProp ;
      (** we define the type of modal types *)
      SubuniverseType := {T : Type & (subuniverse_HProp) T} ;
      (** for every type T, a type (O T) such that (subuniverse_HProp (O T)) *)
      to_O : Type -> SubuniverseType ; 
      (** for every type T, a map A -> O T *)
      O_unit : forall T, T -> (to_O T).1; 
      (** an equivalence ((O P)->Q) <~> (P -> Q) *)
      O_equiv : forall (P : Type) (Q : SubuniverseType), 
                  IsEquiv (fun f : (to_O P).1 -> Q.1 => f o (@O_unit P)) 
    }.

  Local Notation O := to_O.

  Coercion SubuniverseType_pr1 subU (T:SubuniverseType subU) := @proj1_sig Type subU.(subuniverse_HProp) T.

  (** Some shortcuts to manipulate the above equivalence *)
  Definition O_rec {subU} (P : Type) (Q : SubuniverseType subU) :
    (P -> Q) -> (subU.(O) P) -> Q := 
    (@equiv_inv _ _ _ (subU.(O_equiv) _ _)).

  Definition O_rec_retr {subU} (P : Type) (Q : SubuniverseType subU) f
  : O_rec _ _ f o subU.(O_unit) _ = f :=
    @eisretr _ _ _ (subU.(O_equiv) P Q) f.

  Definition O_rec_sect {subU} (P : Type) (Q : SubuniverseType subU) f :=
    @eissect _ _ _ (subU.(O_equiv) P Q) f.

  Section Basic_facts.

    Variable subU : ReflectiveSubuniverse.

    (** The second component of subunivere_Type is unique *)
    Definition unique_subuniverse
    : forall (T T' : SubuniverseType subU), T.1 = T'.1 -> T = T'.
    Proof.
      intros T T' X. destruct T as [T h], T' as [T' h'].
      eapply (path_sigma _ _ _ X).
      simpl in X; destruct X.
      apply (allpath_hprop (H := isp (subuniverse_HProp subU T))).
    Defined.

    (** The subuniverse structure is transportable *)
    Definition ReflectiveSubuniverse_transport T U (f : T <~> U)
    : (subU.(subuniverse_HProp) T) -> (subU.(subuniverse_HProp) U).
    Proof.
      apply path_universe_uncurried in f. rewrite f.
      intro x; exact x.
    Defined.
    
    (** Unit maps are equivalences iff they admit a retraction *)
    Definition O_unit_retract_equiv (T:Type) (mu : (subU.(O) T) -> T) (eta := subU.(O_unit) T)
    : Sect eta mu -> IsEquiv eta.
    Proof.
      unfold Sect; intros H. apply isequiv_adjointify with (g:=mu).
      - assert (X : eta o mu o eta = idmap o eta).
        unfold compose at 3.
        apply (ap (fun g => eta o g)).
        apply path_forall; intro y.
        exact (H y).
        apply ap10.
        apply ((equiv_inv (IsEquiv := isequiv_ap (H := O_equiv subU T (O subU T))
                                                 (eta o mu)
                                                 idmap ))).
        exact X.
      - exact H.
    Defined.

    (** A type is modal if and only if its unit map is an equivalence : *)

    Instance O_modal_equiv (P : SubuniverseType subU)
    : IsEquiv (subU.(O_unit) P).
    Proof.
      apply O_unit_retract_equiv with (mu := (O_rec P P idmap)).
      pose (f := O_rec_retr P P idmap). 
      intro. eapply ap10 in f. exact (f x).
    Defined.

    Definition O_modal (T:SubuniverseType subU)
    : T = subU.(O) T.
    Proof.
      apply unique_subuniverse. 
      apply path_universe_uncurried.
      exact (BuildEquiv _ _ (subU.(O_unit) T) (O_modal_equiv _)).
    Defined.

    Definition subuniverse_iff_O (T:Type)
    : IsEquiv (subU.(O_unit) T) = (subU.(subuniverse_HProp) T).
    Proof.
      apply path_universe_uncurried.
      exact (@equiv_iff_hprop
               (IsEquiv (O_unit subU T))
               _
               (subuniverse_HProp subU T)
               (isp (subuniverse_HProp subU T))
               (fun X => ReflectiveSubuniverse_transport _ _
                             (BuildEquiv _ _ _
                                         (isequiv_inverse (H:=X)))
                             ((subU.(O) T)).2)
               (fun X => O_modal_equiv (T;X))).
    Defined.

    (** The modality is involutive *)
    Definition O_invol
    : forall T, (O subU) (((O subU) T)) = O subU T.
    Proof.
      intro T; symmetry; apply O_modal.
    Defined.

    (** A little commutation property between O_rec and eta *)
    
    Definition O_rec_O_unit (A : SubuniverseType subU) (B : Type)
               (f : B -> A) (x : (O subU B))
    : O_unit subU A (O_rec B A f x) = O_rec B (O subU A) ((O_unit subU A) o f) x
      :=  (((fun U => (ap10 (O_rec_sect B (O subU A) U) x))
              (O_unit subU A o O_rec B A f))^)
            @ ((ap (fun u => O_rec B (O subU A)
                                   (O_unit subU A o u) x)
                   (inverse (O_rec_retr B A f)))^).

    (** The universal property commutes with eta *)
    
    Definition equal_fun_modal (A:Type) (B:SubuniverseType subU)
               (f g:(O subU A) -> B) (eta := O_unit subU A)
    : ((f o eta = g o eta) -> (f=g))
      := fun H => (((eissect _ (IsEquiv := (O_equiv subU A B)) f)^)
                     @ (ap equiv_inv H))
                     @ (eissect _ (IsEquiv := (O_equiv subU A B)) g).
    
    Lemma universality_unit_lemma (oA A B: Type) (eta : A -> oA) (f g : oA -> B)
          (inv : (A -> B) -> oA -> B) (pi : f o eta = g o eta)
          (eisretr : forall x:A -> B, (inv x) o eta = x)
          (eissect : forall x : oA -> B, inv (x o eta) = x) a
    : ap10 (ap inv pi) (eta a)
      = (ap10 (eisretr (f o eta)) a @ ap10 pi a)
          @ (ap10 (eisretr (g o eta)) a)^.
    Proof.
      destruct pi. simpl. rewrite concat_p1. rewrite concat_pV. exact idpath.
    Qed.
    
    Definition universality_unit (A:Type) (B:SubuniverseType subU) (f g:(O subU A) -> B)
               (eta := O_unit subU A) (pi : (f o eta = g o eta))
    : forall a, ap10 (equal_fun_modal A B _ _ pi) (eta a) = ap10 pi a.
    Proof.
      intro a. unfold equal_fun_modal. destruct (O_equiv subU A B). simpl. unfold Sect in *.
      repeat rewrite ap10_pp. rewrite ap10_V. rewrite concat_pp_p.
      apply moveR_Mp. apply moveR_pM. rewrite inv_V.
      assert (X : ap10 (eisretr (g o eta)) a = ap10 (eissect g) (eta a)).
      apply (transport (fun U => ap10 U a = ap10 (eissect g) (eta a)) (eisadj g)^).
      apply ap_ap10_L.
      apply (transport (fun U => _ = _ @ U^) X); clear X.
      assert (X : ap10 (eisretr (f o eta)) a =
              ap10 (eissect f) (eta a)).
      apply (transport (fun U => ap10 U a = ap10 (eissect f) (eta a)) (eisadj f)^).
      apply ap_ap10_L.
      apply (transport (fun U => _ = (U @ _) @ _) X); clear X.
      apply (universality_unit_lemma _ _ _ _ _ _ equiv_inv  pi eisretr eissect a).
    Qed.                                

  End Basic_facts.

  Section Functions_lifts.

    (** In this section, we see how the ○ operator acts on maps *)
    Variable subU : ReflectiveSubuniverse.
    
    Definition function_lift (A B : Type) (f : A -> B)
    : (subU.(O) A) -> (subU.(O) B).
    Proof.
      apply O_rec; intro x; apply subU.(O_unit); apply f; exact x.
    Defined.

    Definition function_lift_modal (A:Type) (B:SubuniverseType subU) (f : A -> B)
    : (O subU A) -> B.
    Proof.
      apply O_rec. exact f.
    Defined.

    Definition function_lift_modal_square (A : Type) (B : SubuniverseType subU) (f : A -> B)
    : (@equiv_inv _ _ (subU.(O_unit) B) (O_modal_equiv _ B))
        o (function_lift A B f)
        o (subU.(O_unit) A)
      =  f.
    Proof.
      apply path_forall; intro x; unfold compose, function_lift; simpl.
      exact (transport (fun U => O_rec B B (fun x : B => x) U = f x)
                       ((ap10 ((O_rec_retr A (subU.(O) B)) ((O_unit subU B) o f)) x)^)
                       (ap10 (O_rec_retr B B idmap) (f x))).
    Defined.

    (** Function lift is ok with composition *)
    Definition function_lift_compose (A B C : Type) ( f : A -> B) (g : B -> C)
    : (function_lift A C (g o f)) = (function_lift B C g) o (function_lift A B f).
    Proof.
      apply path_forall; intro x; simpl.
      unfold function_lift.
      fold ( (O_unit subU C) o g).
      fold ( (O_unit subU B) o f).

      assert (P1 : O_rec A (O subU C) (fun x0 : A => O_unit subU C ((g o f) x0)) x
                   = O_rec A (O subU C) (((O_unit subU C) o g) o f) x) by (exact idpath).

      assert (P2 : O_rec A (O subU C) (((O_unit subU C) o g) o f) x
                   = O_rec A (O subU C)
                           (((O_rec B (O subU C) (O_unit subU C o g) o O_unit subU B) o f)) x).
      apply ap10. apply ap. apply ap10. apply ap.
      exact (inverse (O_rec_retr B (O subU C) (O_unit subU C o g))).

      assert (P3 : O_rec A (O subU C)
                         (O_rec B (O subU C) (O_unit subU C o g) o O_unit subU B o f) x
                   = O_rec A (O subU C)
                           (O_rec B (O subU C) (O_unit subU C o g) o (O_unit subU B o f)) x)
        by (exact idpath).
      
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

    Definition function_lift_square (A B C X : Type) (pi1 : X -> A) (pi2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o pi1) = (g o pi2))
    : ( (function_lift A C f) o (function_lift X A pi1) )
      = ( (function_lift B C g) o (function_lift X B pi2) ).
    Proof.
      apply path_forall; intro x; simpl.
      pose (foo1 := ap10 (function_lift_compose X A C pi1 f) x).
      pose (foo2 := ap10 (function_lift_compose X B C pi2 g) x).
      pose (foo3 := ap (fun u => O_rec X (O subU C) (fun x0 => O_unit subU C (u x0)) x)
                       (x:=f o pi1) (y:=g o pi2) comm).
      exact (concat (concat (inverse foo1) foo3) foo2).
    Defined.

  End Functions_lifts.

  Section Types.

    Variable subU : ReflectiveSubuniverse.

    (** ** The Unit type *)
    Lemma unit_subuniverse : (subU.(subuniverse_HProp) Unit).
    Proof.
      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (mu := fun x:(subU.(O) Unit) => tt).
      intro u.
      destruct u; exact idpath.
    Defined.
    
    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Definition forall_subuniverse (A:Type) (B:A -> Type) 
    : (forall x, (subU.(subuniverse_HProp) (B x)))
      -> ((subU.(subuniverse_HProp)) (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rec (forall x0 : A, (B x0) ) (B x; H x) (ev x)).
      pose (h := fun z => fun x => zz x z).
      simpl in *.
      rewrite <- (subuniverse_iff_O).
      set (eta := (O_unit subU (forall x : A, (B x)))).
      apply O_unit_retract_equiv with (mu := h).
      intro phi.
      unfold h, zz, ev; clear h; clear zz; clear ev.
      apply path_forall; intro x.
      pose (foo := @O_rec_retr subU (forall x0 : A, (B x0)) (B x; H x)
                               (fun f : forall x0 : A, (B x0) => f x)).
      exact (ap10 foo phi).
    Qed.

    Definition arrow_subuniverse (A : Type) (B : SubuniverseType subU)
    : (subuniverse_HProp subU (A -> B)).
    Proof.
      apply forall_subuniverse.
      intro a. exact B.2.
    Qed.

    (** ** Product *)
    Definition product_subuniverse (A B : SubuniverseType subU)
    : (subuniverse_HProp subU (A*B)).
    Proof.
      rewrite <- subuniverse_iff_O.

      pose (mu := fun (X : (O subU (A * B))) =>
                   (O_rec (A * B) (A)
                          (fun x : (A * B) => (fst x)) X ,
                    O_rec (A * B) (B)
                          (fun x : (A * B) => (snd x)) X)).
      apply O_unit_retract_equiv with (mu := mu).
      intro x; destruct x as [a b].
      unfold mu; apply path_prod.
      - simpl.
        exact (ap10 (O_rec_retr (A * B) A (fun x : (A * B) => fst x)) (a,b)). 
      - simpl.
        exact (ap10 (O_rec_retr (A * B) B (fun x : (A * B) => snd x)) (a,b)). 
    Qed.

    (** We show that ○A*○B has the same universal property as ○(A*B) *)
    Lemma product_universal (A B : Type) (C : SubuniverseType subU)
    : ((O subU A)*(O subU B) -> C) <~> (A * B -> C).
    Proof.
      apply (@equiv_compose' _ (A -> B -> C) _).
      {
        exists (fun u => fun x => u (fst x) (snd x)).
        apply isequiv_adjointify with (g:= (fun f => fun u v => f (u,v))).
        - intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.
        - intro x. apply path_forall; intro u; apply path_forall; intro v. exact idpath.
      }
      
      apply (@equiv_compose' _ ((O subU A) -> B -> C) _).
      {
        exists ((fun f : (O subU A)  ->
                         (existT (fun T => subuniverse_HProp subU T)
                                 (B -> C)
                                 (arrow_subuniverse B C)) .1
                 => f o O_unit subU A)).
        exact (O_equiv subU A (( B -> C) ; arrow_subuniverse B C)).
      }
      
      apply (@equiv_compose' _ ((O subU A) -> (O subU B) -> C) _).
      {
        apply equiv_postcompose'.
        exists (fun f : ((O subU B) )  -> (C )  => f o O_unit subU B).
        exact (O_equiv subU B C).
      }

      {
        exists (fun f => fun u v => f (u,v)).
        apply isequiv_adjointify with (g := fun f => fun u => f (fst u) (snd u)).
        - intro x. apply path_forall; intro u. apply path_forall; intro v. exact idpath.
        - intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.
      }
    Qed.

    (** TODO : ○(A*B) = ○A * ○B *)

    (** ** Dependent sums *)
    (** Theorem 7.7.4 *)
    Definition sigma_subuniverse
    : (forall (A:SubuniverseType subU) (B:A -> SubuniverseType subU),
         (subuniverse_HProp subU ({x:A & B x})))
      <->
      (forall (A:Type) (B: (O subU A) -> SubuniverseType subU)
              (g : forall (a:A), (B (O_unit subU A a))),
         {f : forall (z:(O subU A)), (B z) & forall a:A, f (O_unit subU A a) = g a}).
    Proof.
      split.
      - intro H. intros A B g.
        pose (Z := (existT (fun T => (subuniverse_HProp subU T))
                          ({z:(O subU A).1 & (B z)})
                          (H (O subU A) B)) : SubuniverseType subU).
        pose (g' := (fun a:A => (O_unit subU A a ; g a)) : A -> Z).
        pose (f' := O_rec _ _ g').
        pose (eqf :=fun a:A => (ap10 (O_rec_retr _ _ g') a)).
        pose (g'' := fun x => (f' x).1).
        pose (f'' := fun x:(O subU A) => x).
        pose (eq'' := path_forall _ _ (fun x => @ap _ _ pr1 _ _ (eqf x))).
        assert (X : g'' o (O_unit subU A) = f'' o (O_unit subU A)) by (exact eq'').
        pose (eq''' := ap10 (equal_fun_modal _ A (O subU A) (g'') (f'') (eq''))).
        pose (f := fun z => (f' z).2). simpl in f.
        set (eta := O_unit subU A) in *.

        exists (fun z => transport (fun u => (B u)) (eq''' z) (f z)).
        intro a.

        pose (p := projT1_path (eqf a)). simpl in p.
        pose (q := projT2_path (eqf a)). simpl in q.

        rewrite <- q. 
        assert (X0 : (eq''' (eta a)) =  (eqf a) ..1).
        unfold eq''', projT1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, eta in *;
          simpl in *.
        rewrite universality_unit.
        unfold path_forall. rewrite eisretr. exact idpath.
        exact (ap (fun v => transport (fun u => B u) v (f' (eta a)) .2) X0).
      - intros H A B.
        pose (h := fun x => O_rec ({x:A & B x}) A pr1 x).
        pose (p := fun z => ap10 (O_rec_retr ({x : A & B x}) A pr1) z).
        pose (C := fun w => B(h w)).
        pose (g := fun z => (transport (fun u => B u) (inverse (p z)) z.2)).
        simpl in *.
        specialize (H ({x:A & B x}) C g).
        destruct H as [f q]. simpl in q.
        pose (k := (fun w => (h w; f w))
                   : (O subU ({x:A & B x})) -> ({x:A & B x})); simpl in k.

        rewrite <- subuniverse_iff_O.
        apply O_unit_retract_equiv with (mu := k).

        intro x; destruct x as [x1 x2]. unfold k.
        apply (path_sigma _ (O_rec {x : A & B x} A pr1
                                   (O_unit subU {x : A & B x} (x1; x2));
                             f (O_unit subU {x : A & B x} (x1; x2)))
                          (x1;x2) (p (x1;x2))).
        rewrite (q (x1;x2)). unfold g; simpl. rewrite <- transport_pp. rewrite concat_Vp.
        exact idpath.
    Qed.

    (** ** Paths *)

    Definition paths_subuniverse_fun (S:SubuniverseType subU) (x y:S)
    : (O subU (x=y)) -> x=y.
      intros u.
      assert (p : (fun _:(O subU (x=y)) => x) = (fun _=> y)). 
      apply (equiv_inv (IsEquiv := isequiv_ap (H:=O_equiv subU (x=y) S) (fun _ : (O subU (x = y))  => x) (fun _ : (O subU (x = y))  => y))).
      apply path_forall; intro v. exact v.
      exact (ap10 p u).
    Defined.

    Definition paths_subuniverse (S:SubuniverseType subU) (x y:S)
    : (subuniverse_HProp subU (x=y)).
      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (mu := paths_subuniverse_fun S x y).
      intro u.
      etransitivity.
      exact ((ap_ap10_L
                ((fun _ : (O subU (x = y))  => x))
                ((fun _ : (O subU (x = y))  => y))
                (O_unit subU (x = y))
                (equiv_inv (IsEquiv := isequiv_ap (H:=O_equiv subU (x=y) S)
                                                  (fun _ : (O subU (x = y))  => x)
                                                  (fun _ : (O subU (x = y))  => y))
                           (path_forall
                              ((fun _ : (O subU (x = y))  => x) o O_unit subU (x = y))
                              ((fun _ : (O subU (x = y))  => y) o O_unit subU (x = y))
                              idmap))
                u)^).
      rewrite eisretr.
      unfold path_forall, ap10.
      rewrite eisretr. exact idpath.
    Qed.
    
  End Types.
End Reflective_Subuniverse.