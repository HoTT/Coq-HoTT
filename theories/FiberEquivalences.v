Require Export Fibrations Equivalences.

(** We first consider maps between fibrations over the same base
   space.  The theorem is that such a map induces an equivalence on
   total spaces if and only if it is an equivalence on all fibers. *)

Section FiberMap.

  Variable A : Type.
  Variables P Q : fibration A.

  Section TotalIsEquiv.

    (** Suppose we have a fiberwise map [g]. *)

    Variable g : forall x, P x -> Q x.

    (** Then it induces a map of total spaces. *)

    Let tg (u : total P) : total Q := (pr1 u; g (pr1 u) (pr2 u)).

    (** Suppose the total map is an equivalence. *)

    Hypothesis tg_is_equiv : is_equiv tg.

    Let ge : (total P) <~> (total Q) :=
      {| 
        equiv_map := tg ;
        equiv_is_equiv := tg_is_equiv
      |}.

    (* We want to show that each function [g x] is an equivalence, so we
       start by defining its inverse. *)

    Let ginv (x : A) (y : Q x) : P x.
    Proof.
      (* Unfortunately, the obvious inverse does not live in the fiber over [x], but
         rather in some other fiber. We need to transport it along some path. Our first
         guess at such a path might be this. *)
      apply (transport (base_path (inverse_is_section ge (x ; y)))).
      (* And it works. *)
      apply (pr2 (inverse ge (x ; y))).
    Defined.

    (** Fiddly lemmas to make the proof go through. *)

    Let tg_is_fiberwise (z : total P) : pr1 z = pr1 (tg z).
      apply idpath.
    Defined.

    Lemma replace_fiberwise {x y : total P} (p : x = y) : 
      base_path (map ge p) = (! tg_is_fiberwise x @ base_path p @ tg_is_fiberwise y).
    Proof.
      path_induction.
    Defined.

    (* Now we are ready to prove that [g x] is an equivalence. *)

    Theorem fiber_equiv (x : A) : P x <~> Q x.
    Proof.
      apply (equiv_from_hequiv (g x) (ginv x)). 
      (* We have to show [ginv x] is a section of [g x], which
         mostly involves unfolding of definitions and basic lemmas. *)
        intro v.
        unfold base_path, inverse_is_section, inverse, ge in ginv; simpl in ginv.
        unfold ginv.
        destruct (tg_is_equiv (x;v)) as [[[x' u'] p] h].
        rewrite trans_map.
        exact (fiber_path p).
      (* And now that it is a retraction. *)
      intro u.
      unfold ginv.
      (* A bit of annoying rewriting to get triangle in the correct form
         for rewriting. *)
      (* assia : this is because of the matching strategy of the std rewrite tactic :
         head constant modulo conversion, no conversion to identify arguments. The 
         ssr rewrite matching does the converse : rigid on the head constant and 
         modulo full conversion for the arguments which is often more convenient and
         avoids this kind of pain. We can however be slightly lazier by forcing the
         conversion between the two terms to be matched *)
      generalize (inverse_triangle ge (x;u)).
      set (pat1 := inverse_is_section _ _).
      (* assia : why do we need the ge argument this time? *)
      set (pat2 := inverse_is_section ge _).
      change pat2 with pat1.
      intro triangle; rewrite <- triangle; clear triangle pat1 pat2.
      (* We have to do again silly unfolding and folding to make r applicable.
         How do we avoid this? *)
      generalize (replace_fiberwise (inverse_is_retraction ge (x; u))).
      (* why do we need (map ge _) again?*)
      set (pat1 := base_path (map ge _)).
      (* weird behaviour of set prevents us from using the same trick *)
      change (base_path (map ge (inverse_is_retraction ge (x; u)))) with pat1.
      intro r; rewrite r; clear r pat1.
      hott_simpl.
      apply (fiber_path (inverse_is_retraction ge (x; u))).
    Defined.

  End TotalIsEquiv.

  (* An auxiliary lemma useful for showing that a map is fiber-wise an equivalence
     without constructing the equivalence itself. *)
  Lemma fiber_is_equiv (g : forall x, P x -> Q x) :
    is_equiv (fun u : total P => (pr1 u; g (pr1 u) (pr2 u))) -> forall x, is_equiv (g x).
  Proof.
    intros H x.
    exact (equiv_is_equiv (fiber_equiv g H x)).
  Defined.

  Section FiberIsEquiv.

    (* Now let's suppose instead that the maps on fibers are equivalences. *)

    Variable g : forall x, P x <~> Q x.

    (* And we prove that the total map is an equivalence. *)

    Let tg (u : total P) : total Q := existT Q (pr1 u) (g (pr1 u) (pr2 u)).

    Let tg_inv (u : total Q) : total P := existT P (pr1 u) (inverse (g (pr1 u)) (pr2 u)).

    Theorem total_equiv : total P <~> total Q.
    Proof.
      apply (equiv_from_hequiv tg tg_inv).
      intros [x v].
      unfold tg, tg_inv; simpl.
      apply @total_path with (p := idpath x).
      apply inverse_is_section.
      intros [x u].
      unfold tg, tg_inv; simpl.
      apply @total_path with (p := idpath x).
      apply inverse_is_retraction.
    Defined.

  End FiberIsEquiv.

End FiberMap.

Implicit Arguments fiber_equiv [A].
Implicit Arguments fiber_is_equiv [A P Q].
Implicit Arguments total_equiv [A].

(** Next we consider a fibration over one space and its pullback along
   a map from another base space.  The theorem is that if the map we
   pull back along is an equivalence, so is the induced map on total
   spaces. *)

Section PullbackMap.

  (** Two base spaces. *)
  Variables A B : Type.

  (** And a fibration over one of them. *)
  Variable Q : fibration B.
  
  (** Assume an equivalence between the base spaces. *)
  Variable e : A <~> B.

  (** The induced map between total spaces. *)
  Let g : total Q -> total (Q o e).
  Proof.
    intros [x v].
    exists (inverse e x).
    exact (! inverse_is_section e x # v).
  Defined.

  Let f : total (Q o e) -> total Q := fun u => (e (pr1 u) ; pr2 u).

  Theorem pullback_total_equiv : total (Q o e) <~> total Q.
  Proof.
    apply (equiv_from_hequiv f g).
    (* one inverse identity *)
    intros [x v].
    unfold f, g; simpl.
    apply @total_path with (p := inverse_is_section e x).
    simpl; hott_simpl.
    (* and the other *)
    intros [x u].
    unfold f, g; simpl.
    apply @total_path with (p := inverse_is_retraction e x).
    simpl; hott_simpl.
    rewrite <- inverse_triangle.
    generalize (inverse_is_retraction e x).
    generalize (inverse e (e x)).
    path_induction.
  Defined.

End PullbackMap.

Implicit Arguments pullback_total_equiv [A B].

(** Finally, we can put these together to prove that given a map of
   fibrations lying over an equivalence of base spaces, the induced
   map on total spaces is an equivalence if and only if the map on
   each fiber is an equivalence. *)

Section FibrationMap.

  (* Two fibrations over two base spaces. *)

  Variables A B : Type.
  Variable P : fibration A.
  Variable Q : fibration B.

  (* Suppose the base spaces are equivalent. *)

  Variable e : A <~> B.

  (* And there is a map [g] above the equivalence. *)

  Variable g : forall x, P x -> Q (e x).

  (* There is an induced map on the total spaces. *)

  Let eg : total P -> total Q := fun u => (e (pr1 u); g (pr1 u) (pr2 u)).

  (* Which factors through [total (Q o e)] as [h] followed by [k]. *)

  Let h :=  (fun u : total P => existT (Q o e) (pr1 u) (g (pr1 u) (pr2 u))).

  Let k := (fun u : total (Q o e) => existT Q (e (pr1 u)) (pr2 u)).

  (* Moreover, [k] is an equivalence. *)

  Let kinv : total Q -> total (Q o e).
  Proof.
    intros [x u].
    exists (inverse e x).
    unfold compose.
    exact (!inverse_is_section e x # u).
  Defined.

  Let ke : total (Q o e) <~> total Q.
  Proof.
    apply (equiv_from_hequiv k kinv).
    intros [x u].
    unfold k, kinv.
    apply @total_path with (p := inverse_is_section e x).
    simpl; hott_simpl.
    intros [x v].
    unfold k, kinv; simpl.
    apply @total_path with (p := inverse_is_retraction e x).
    simpl.
    rewrite (! inverse_triangle e x).
    generalize (inverse_is_retraction e x).
    generalize (inverse e (e x)).
    intros a p.
    induction p.
    apply idpath.
  Defined.

  Section FibseqFiber.
    (* Suppose the induced map is an equivalence. *)

    Hypothesis eg_is_equiv : is_equiv eg.

    (* Then [h] is an equivalence. *)
    Let he : total P <~> total (Q o e).
    Proof.
      apply @equiv_cancel_left with (f := h) (g := ke).
      apply eg_is_equiv.
    Defined.
   
    (* And so [h x] is an equivalence, but that is just [g x]. *)

    Theorem fibseq_fiber_equiv x : P x <~> Q (e x).
    Proof.
      apply fiber_equiv with (g := g).
      apply (equiv_is_equiv he).
    Defined.

    (* So we showed that [g] is a fiber-wise equivalence. *)
  End FibseqFiber.

  Section FiberFibseq.
    (* Now we assume that [g] is fiber-wise equivalence and show that the
       induced map [eg] is one as well. *)
    
    Hypothesis is_equiv_g : forall x, is_equiv (g x).

    (* Then [h] is an equivalence. *)
    Let he : total P <~> total (Q o e).
    Proof.
      apply total_equiv.
      intro x.
      exact {| equiv_map := g x; equiv_is_equiv := is_equiv_g x |}.
    Defined.

    (* And now by a two-out-of-three property, [eg] is an equivalence. *)
    Theorem fibseq_total_equiv : total P <~> total Q.
    Proof.
      refine {| equiv_map := eg |}.
      apply (equiv_is_equiv (equiv_compose he ke)).
    Defined.
  End FiberFibseq.
End FibrationMap.

Implicit Arguments fibseq_fiber_equiv [A B].
Implicit Arguments fibseq_total_equiv [A B].
