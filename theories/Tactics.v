(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Overture types.Prod types.Forall PathGroupoids.

(** * Extra tactics for homotopy type theory. *)

(** ** Tactics for dealing with [Funext] *)
(** *** Tactics about [transport]ing with [path_forall] *)

(** Given using the variable names from [transport : forall {A : Type} (P : A -> Type) {x y : A}, x = y -> P x -> P y] and [path_forall : {Funext} -> forall {A B} (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g]:

The high-level idea is that we don't really need functional extensionality if we end up just applying the functions to arguments anyway.  That is, if we have that [forall x, f x = g x], and we only talk about [f y] and [f z], then we don't actually need to transport across [f = g], just [f y = g y] and [f z = g z].

In a bit more detail, if we are transporting across [path_forall f g H], and in the function [P], all instances of [f] are applied to some expressions, say we only see [f x], [f y], ..., [f z], then we can eliminate the [path_forall] by explicitly transporting across [H x], [H y], ..., [H z].  The lemma [path_forall_1_beta] expresses this fact in the case that we see [f] applied to only a single argument in [P], and the tactic [transport_path_forall_hammer] is some fancy Ltac to auto-infer what [P] is and what the argument to [f] is.

The way the tactic does this is by creating an evar for [P] and an evar for the argument to [f], and then using a combination of [assert], [pattern], etc to figure out what each should be.  If you want to see how it works, you can step through each step of [transport_path_forall_hammer] when trying to prove [path_forall_2_beta]. *)

(** First, we prove some helpful lemmas about [path_forall] and [transport] *)
Local Ltac path_forall_beta_t :=
  lazymatch goal with
    | [ |- appcontext[@path_forall ?H ?A ?B ?f ?g ?e] ]
      => let X := fresh in
         pose proof (eissect (@path_forall H A B f g) e) as X;
           case X;
           generalize (@path_forall H A B f g e);
           clear X; clear e;
           intro X; destruct X;
           simpl;
           unfold apD10;
           rewrite !(path_forall_1 f)
  end;
  reflexivity.

(** The basic idea is expressed in the type of this lemma. *)
Lemma path_forall_1_beta `{Funext} A B x P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x) P (f x) (g x) (e x) Px.
Proof.
  path_forall_beta_t.
Defined.

(** The powerful recursive case *)
Lemma path_forall_recr_beta `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport ((forall a, B a) * B x0)%type
               (fun x => P (fst x) (snd x))
               (f, f x0)
               (g, g x0)
               (path_prod' (@path_forall _ _ _ _ _ e) (e x0))
               Px.
Proof.
  path_forall_beta_t.
Defined.

(** Two lemmas about [transport]ing across [path_prod'], used for cleanup *)
Definition transport_path_prod'_beta A B P (x x' : A) (y y' : B) (HA : x = x') (HB : y = y') (Px : P (x, y))
: @transport (A * B) P (x, y) (x', y') (@path_prod' A B x x' y y' HA HB) Px
  = @transport A (fun x => P (x, y')) x x' HA
               (@transport B (fun y => P (x, y)) y y' HB Px).
Proof.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod'_beta' A B P (x x' : A) (y y' : B) (HA : x = x') (HB : y = y') (Px : P x y)
: @transport (A * B) (fun xy => P (fst xy) (snd xy)) (x, y) (x', y') (@path_prod' A B x x' y y' HA HB) Px
  = @transport A (fun x => P x y') x x' HA
               (@transport B (fun y => P x y) y y' HB Px).
Proof.
  path_induction.
  reflexivity.
Defined.

(** The sledge-hammer for computing with [transport]ing across a [path_forall].  Note that it uses [rewrite], and so should only be used in opaque proofs. *)
Ltac transport_path_forall_hammer :=
  progress
    repeat (
      (* pull out the parts of the goal to use [path_forall_recr_beta] *)
      let F := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(F) end in
      let H := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(H) end in
      let X := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(X) end in
      let T := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(T) end in
      let t0 := fresh "t0" in
      let t1 := fresh "t1" in
      let T1 := lazymatch type of F with (?T -> _) -> _ => constr:(T) end in
      evar (t1 : T1);
      let T0 := lazymatch type of F with (forall a : ?A, @?B a) -> ?C => constr:((forall a : A, B a) -> B t1 -> C) end in
      evar (t0 : T0);
      (* make a dummy goal to figure out the functional form of [P] in [@transport _ P] *)
      let dummy := fresh in
      assert (dummy : forall x0, F x0 = t0 x0 (x0 t1));
      [ let x0 := fresh in
        intro x0;
          simpl in *;
          let GL0 := lazymatch goal with |- ?GL0 = _ => constr:(GL0) end in
          let GL0' := fresh in
          let GL1' := fresh in
          set (GL0' := GL0);
            (* find [x0] applied to some argument, and note the argument *)
            let arg := match GL0 with appcontext[x0 ?arg] => constr:(arg) end in
            assert (t1 = arg) by (subst t1; reflexivity); subst t1;
            pattern (x0 arg) in GL0';
            match goal with
              | [ GL0'' := ?GR _ |- _ ] => constr_eq GL0' GL0'';
                                          pose GR as GL1'
            end;
            (* remove the other instances of [x0], and figure out the shape *)
            pattern x0 in GL1';
            match goal with
              | [ GL1'' := ?GR _ |- _ ] => constr_eq GL1' GL1'';
                                          assert (t0 = GR)
            end;
            subst t0; [ reflexivity | reflexivity ]
      | clear dummy ];
      let p := fresh in
      pose (@path_forall_recr_beta H X T t1 t0) as p;
      simpl in *;
        rewrite p;
      subst t0 t1 p;
      rewrite ?transport_path_prod'_beta', ?transport_const
    ).

(** An example showing that it works *)
Lemma path_forall_2_beta `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x0 * B x1)%type (fun x => P (fst x) (snd x)) (f x0, f x1) (g x0, g x1) (path_prod' (e x0) (e x1)) Px.
Proof.
  transport_path_forall_hammer.
  repeat match goal with
           | [ |- appcontext[e ?x] ] => induction (e x)
         end;
    simpl.
  reflexivity.
Qed.
