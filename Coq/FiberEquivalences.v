Require Export Fibrations Equivalences.

(** The map on total spaces induced by a map of fibrations *)

Definition total_map {A B : Type} {P : A -> Type} {Q : B -> Type}
  (f : A -> B) (g : forall x:A, P x -> Q (f x)) :
  sigT P -> sigT Q.
Proof.
  intros [x y].
  exists (f x).
  exact (g x y).
Defined.

(** We first consider maps between fibrations over the same base
   space.  The theorem is that such a map induces an equivalence on
   total spaces if and only if it is an equivalence on all fibers. *)

Section FiberMap.

  Variable A : Type.
  Variables P Q : A -> Type.
  Variable g : forall x, P x -> Q x.

  Let tg := total_map (idmap A) g.

  (* There is a subtlety here that is easy to get confused about.  The
     type [sigT P] is *inductively generated* by elements of the form
     [(x ; y)].  This does *not* mean that every element of [total
     P] is *definitionally* equal to one of that form.  In particular,
     although it appears that [total_map f g] "acts as [f] on the base
     space," we cannot assert that *definitionally* except for
     arguments of the form [(x ; y)].  Hence we need the following
     lemma.  *)

  Let tg_is_fiberwise (z : sigT P) : pr1 z ~~> pr1 (tg z).
    destruct z as [x y].
    auto.
  Defined.

  (* Similarly, the following lemma says that the fiber component of
     [tg z] is obtained by applying the fiberwise function [f] to the
     fiber component of [z], modulo the previously defined path in the
     base.  *)

  Let tg_isg_onfibers (z : sigT P) :
    g _ (transport (tg_is_fiberwise z) (pr2 z)) ~~> pr2 (tg z).
  Proof.
    destruct z as [x y].
    auto.
  Defined.

  (* And the following lemma tells us that the same is true for its
     action on paths. *)

  Let tg_isfib_onpaths (z w : sigT P) (p : z ~~> w) :
    (tg_is_fiberwise z @ base_path (map tg p) @ !tg_is_fiberwise w) ~~> base_path p.
  Proof.
    path_induction.
    destruct z. simpl. auto.
  Defined.

  (* Now let's suppose the total function is an equivalence. *)

  Section TotalIsEquiv.

    Hypothesis tot_iseqv : is_equiv tg.

    Let tot_eqv : (sigT P) <~> (sigT Q) := (tg ; tot_iseqv).

    (* We want to show that each function [g x] is an equivalence, so we
       start by defining its inverse. *)

    Let ginv (x:A) (y: Q x) : P x.
    Proof.
      (* The obvious thing to look at first is this. *)
      set (inv1 := pr2 ((tot_eqv^-1) (x ; y))).
      (* Unfortunately, this does not live in the fiber over [x], but
         rather in some other fiber.  We need to transport it along some
         path.  Our first guess at such a path might be this. *)
      apply (transport (base_path (inverse_is_section tot_eqv (x ; y)))).
      simpl.
      (* This type is not quite the type of [inv1] yet; it involves
         knowing something about the base component of an image under
         [tg].  This is what [tg_is_fiberwise] is for.   *)
      apply (transport (tg_is_fiberwise ((tot_eqv^-1) (x ; y)))).
      (* Now we are back to the type of [inv1]. *)
      assumption.
    Defined.

    (* Now we are ready to prove that [g x] is an equivalence. *)

    Theorem fiber_is_equiv (x:A) : is_equiv (g x).
    Proof.
      set (is_section := inverse_is_section tot_eqv).
      set (is_retraction := inverse_is_retraction tot_eqv).
      set (triangle := inverse_triangle tot_eqv).
      (* We have our putative inverse ready to hand. *)
      apply @hequiv_is_equiv with (g := ginv x).
      (* First we have to show it is a section of [f x]. *)
      intro y.
      path_via (transport (P := Q)
        (base_path (is_section (x ; y)))
        (pr2 (tot_eqv (tot_eqv^-1 (x ; y))))).
      path_via (transport
        (base_path (is_section (x ; y)))
        (g _ (transport (tg_is_fiberwise (tot_eqv^-1 (x ; y)))
          (pr2 (tot_eqv^-1 (x ; y)))))).
      apply trans_map.
      exact (fiber_path (is_section (existT _ x y))).
      (* And now that it is a retraction. *)
      intro y.
      path_via (transport (base_path (map tg (is_retraction (x ; y))))
      (transport (tg_is_fiberwise (tot_eqv^-1 (x ; (g x y))))
        (pr2 (tot_eqv^-1 (x ; (g x y)))))).
      unfold ginv.
      apply happly, map, map.
      apply opposite, triangle.
      path_via (transport
        (base_path (is_retraction (x ; y)))
        (pr2 (tot_eqv^-1 (x ; (g x y))))).
      path_via (transport
        ((tg_is_fiberwise (tot_eqv^-1 (x ; (g x y))))
          @ (base_path (map tg (is_retraction (x ; y)))))
        (pr2 ((tot_eqv^-1) (x ; (g x y))))).
      apply opposite, trans_concat.
      apply happly, map.
      (* Here is where we need [tg_isfib_onpaths], but it is easy to
         get confused because the second copy of [tg_is_fiberwise]
         appears to be missing.  The reason is that it would be
         instantiated at an element of the form [(x ; y)], in which
         case it happens to be an identity.  Thus, we can just add it
         back in. *)
      path_via (tg_is_fiberwise (tot_eqv^-1 (x ; (g x y))) @
        base_path (map tg (is_retraction (x ; y))) @
        !tg_is_fiberwise (x ; y)).
      exact (fiber_path (is_retraction (existT _ x y))).
    Defined.

    Definition fiber_equiv (x:A) : P x <~> Q x :=
      (g x ; fiber_is_equiv x).

  End TotalIsEquiv.

  (* Now let's suppose instead that the maps on fibers are equivalences. *)

  Section FiberIsEquiv.

    Hypothesis fiber_iseqv : forall x, is_equiv (g x).

    Let fiber_eqv x : P x <~> Q x := (g x ; fiber_iseqv x).

    Let total_inv : sigT Q -> sigT P.
    Proof.
      intros [x y].
      exists x.
      apply ((fiber_eqv x)^-1).
      assumption.
    Defined.

    Theorem total_is_equiv : is_equiv tg.
    Proof.
      eapply hequiv_is_equiv.
      instantiate (1 := total_inv).
      intros [x y].
      eapply total_path.
      instantiate (1 := idpath x).
      path_via (fiber_eqv x ((fiber_eqv x ^-1) y)).
      apply inverse_is_section.
      intros [x y].
      eapply total_path.
      instantiate (1 := idpath x).
      path_via (fiber_eqv x ^-1 (fiber_eqv x y)).
      apply inverse_is_retraction.
    Defined.

    Definition total_equiv : sigT P <~> sigT Q :=
      (tg ; total_is_equiv).

  End FiberIsEquiv.

End FiberMap.

Implicit Arguments fiber_equiv [A].
Implicit Arguments fiber_is_equiv [A].
Implicit Arguments total_equiv [A].
Implicit Arguments total_is_equiv [A].

(** Next we consider a fibration over one space and its pullback along
   a map from another base space.  The theorem is that if the map we
   pull back along is an equivalence, so is the induced map on total
   spaces. *)

Section PullbackMap.

  Variables A B : Type.
  Variable Q : B -> Type.
  Variable f : A <~> B.

  Let pbQ : A -> Type := Q o f.

  Let g (x:A) : pbQ x -> Q (f x) := idmap (Q (f x)).

  Let tg := total_map f g.

  Let tginv : sigT Q -> sigT pbQ.
  Proof.
    intros [x z].
    exists (f^-1 x).
    apply (transport (! inverse_is_section f x)).
    assumption.
  Defined.
    
  Theorem pullback_total_is_equiv : is_equiv tg.
  Proof.
    apply @hequiv_is_equiv with (g := tginv).
    intros [x z].
    apply total_path with (p := inverse_is_section f x).
    simpl.
    path_via (transport (! inverse_is_section f x @ inverse_is_section f x) z).
    apply opposite, trans_concat.
    path_via (transport (idpath x) z).
    apply @map with (f := fun p => transport p z).
    cancel_opposites.
    intros [x z].
    apply total_path with (p := inverse_is_retraction f x).
    simpl.
    path_via (transport (map f (inverse_is_retraction f x))
     (transport (!inverse_is_section f (f x)) z)).
    apply map_trans.
    path_via (transport (!inverse_is_section f (f x) @ map f (inverse_is_retraction f x)) z).
    apply opposite, trans_concat.
    path_via (transport (idpath (f x)) z).
    assert (p : (!inverse_is_section f (f x) @ map f (inverse_is_retraction f x)) ~~> idpath (f x)).
    moveright_onleft.
    cancel_units.
    apply inverse_triangle.
    exact (@map _ _ (!inverse_is_section f (f x) @ map f (inverse_is_retraction f x))
      (idpath (f x))
      (fun p => transport p z) p).
  Defined.

  Definition pullback_total_equiv : sigT pbQ <~> sigT Q :=
    existT _ tg pullback_total_is_equiv.

End PullbackMap.

Implicit Arguments pullback_total_is_equiv [A B].
Implicit Arguments pullback_total_equiv [A B].

(** Finally, we can put these together to prove that given a map of
   fibrations lying over an equivalence of base spaces, the induced
   map on total spaces is an equivalence if and only if the map on
   each fiber is an equivalence. *)

Section FibrationMap.

  Variables A B : Type.
  Variable P : A -> Type.
  Variable Q : B -> Type.

  Variable f : A <~> B.
  Variable g : forall x:A, P x -> Q (f x).

  Let tg := total_map f g.

  Let pbQ := Q o f.

  Let pbg (x : A) : P x -> pbQ x := g x.

  Theorem fibseq_fiber_is_equiv :
    is_equiv tg -> forall x, is_equiv (g x).
  Proof.
    intro H.
    set (pbmap_equiv := pullback_total_is_equiv Q f).
    apply fiber_is_equiv.
    apply @equiv_cancel_left with (C := sigT Q) (g := pullback_total_equiv Q f).
    apply @equiv_homotopic with (g := tg).
    intros [x y].
    auto.
    assumption.
  Defined.

  Definition fibseq_fiber_equiv :
    is_equiv tg -> forall x, P x <~> Q (f x) :=
      fun H x => (g x ; fibseq_fiber_is_equiv H x).

  (* Instead of proving directly that [tg] is an equivalence, we'll
  prove first that a different map from [sigT P] to [sigT Q] is an
  equivalence, then that [tg] is homotopic to that map. *)

  Let fibseq_a_totalequiv :
    (forall x, is_equiv (g x)) -> (sigT P <~> sigT Q).
  Proof.
    intro H.
    apply @equiv_compose with (B := sigT pbQ).
    exists (total_map (idmap A) pbg).
    apply @total_is_equiv.
    apply H.
    apply pullback_total_equiv.
  Defined.

  Theorem fibseq_total_is_equiv :
    (forall x, is_equiv (g x)) -> is_equiv tg.
  Proof.
    intro H.
    apply @equiv_homotopic with (g := fibseq_a_totalequiv H).
    intros [x y].
    auto.
    exact (pr2 (fibseq_a_totalequiv H)).
  Defined.

  Definition fibseq_total_equiv :
    (forall x, is_equiv (g x)) -> (sigT P <~> sigT Q) :=
    fun H => (tg ; fibseq_total_is_equiv H).

End FibrationMap.

Implicit Arguments fibseq_fiber_is_equiv [A B].
Implicit Arguments fibseq_fiber_equiv [A B].
Implicit Arguments fibseq_total_is_equiv [A B].
Implicit Arguments fibseq_total_equiv [A B].
