(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics Types.Prod Types.Forall Types.Paths.
Require Export Tactics.BinderApply.

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
    | [ |- context[@path_forall ?H ?A ?B ?f ?g ?e] ]
      => let X := fresh in
         pose proof (eissect (@path_forall H A B f g) e) as X;
           case X;
           generalize (@path_forall H A B f g e);
           clear X; clear e;
           intro X; destruct X;
           cbn;
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
Lemma path_forall_recr_beta' `{Funext} A B x0 P f g e Px
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

(** Rewrite the recursive case after clean-up *)
Lemma path_forall_recr_beta `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport (forall x : A, B x)
               (fun x => P x (g x0))
               f
               g
               (@path_forall H A B f g e)
               (@transport (B x0)
                           (fun y => P f y)
                           (f x0)
                           (g x0)
                           (e x0)
                           Px).
Proof.
  etransitivity.
  - apply path_forall_recr_beta'.
  - refine (transport_path_prod' _ _ _ _).
Defined.


(** The sledge-hammer for computing with [transport]ing across a [path_forall].  Note that it uses [rewrite], and so should only be used in opaque proofs. *)

(** This helper tactic takes a [term] and a function [f], finds [f x] in [term] and patterns that, returning a pair [(x, term')] such that [term' (f x) ≡ term]. *)
Ltac pull_app term f :=
  let term' := (eval cbv beta in term) in
  match term' with
    | context[f ?x]
      => match eval pattern (f x) in term' with
           | ?term' (f x) => constr:((x, term'))
         end
  end.

Ltac infer_path_forall_recr_beta term :=
  let path_forall_recr_beta' :=
      match term with
        | @transport _ (fun x => @?P0 x) _ _ (@path_forall ?H ?A ?B ?f ?g ?e) _
          => constr:(fun x0 P Px => @path_forall_recr_beta H A B x0 P f g e Px)
      end in
  let Px := match term with @transport _ _ _ _ _ ?Px => constr:(Px) end in
  let P0 := match term with @transport _ (fun f => @?P0 f) _ _ _ _ => constr:(P0) end in
  (** pattern some [f x0] in [P0] *)
  (** Hopefully, no goal will have a variable called [WORKAROUND_FOR_BUG_3458] in the context.  At least not until bug #3458 is fixed. *)
  let P0f := constr:(fun WORKAROUND_FOR_BUG_3458 => ltac:(
                                                      let ret := pull_app (P0 WORKAROUND_FOR_BUG_3458) WORKAROUND_FOR_BUG_3458 in
                                                      exact ret)) in
  let x0 := match P0f with fun f => (?x0, @?P f) => constr:(x0) end in
  let P := match P0f with fun f => (?x0, @?P f) => constr:(P) end in
  let ret := constr:(path_forall_recr_beta' x0 P Px) in
  let retT := type of ret in
  let ret' := (eval cbv beta in ret) in
  let retT' := (eval cbv beta in retT) in
  constr:(ret' : retT').


Ltac transport_path_forall_hammer_helper :=
  let term := match goal with
                | |- context[@transport ?At (fun x => @?Bt x) ?ft ?gt (@path_forall ?H ?A ?B ?f ?g ?e) ?Px]
                  => constr:(@transport At Bt ft gt (@path_forall H A B f g e) Px)
              end in
  let lem := infer_path_forall_recr_beta term in
  pattern term;
    refine (transport _ lem^ _);
    cbv beta.

Ltac transport_path_forall_hammer :=
  transport_path_forall_hammer_helper;
  rewrite ?transport_const;
  repeat (
      transport_path_forall_hammer_helper;
      rewrite ?transport_const
    ).

(** An example showing that it works *)
Lemma path_forall_2_beta' `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x0 * B x1)%type (fun x => P (fst x) (snd x)) (f x0, f x1) (g x0, g x1) (path_prod' (e x0) (e x1)) Px.
Proof.
  transport_path_forall_hammer.
  repeat match goal with
           | [ |- context[e ?x] ] => induction (e x)
         end;
    cbn.
  reflexivity.
Qed.

Lemma path_forall_2_beta `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = transport (fun y : B x1 => P (g x0) y) (e x1)
     (transport (fun y : B x0 => P y (f x1)) (e x0) Px).
Proof.
  transport_path_forall_hammer.
  reflexivity.
Qed.

(** ** A more powerful variant of [path_induction] *)
(** We first define some helper tactics, and then define [path_induction_hammer], which has poor computational behavior, but is vastly more powerful than [path_induction], and removes paths which are discoverably contractible, and paths which only appear in the goal, etc. *)

(** A variant of [induction] which also tries [destruct] and [case], and may be extended to using other [destruct]-like tactics. *)
Ltac induction_hammer H :=
  destruct H || induction H || (case H; clear H).

(** Takes a term of type [_ = _], and tries to replace it by [idpath] by trying to prove that it's an hProp.  The ordering of attempts is tuned for speed. *)
Ltac clear_contr_path p :=
  let H := fresh in
  let T := type of p in
  progress (
      first [ assert (H : idpath = p) by exact (center _)
            | assert (H : idpath = p)
              by (
                  let a := match goal with |- @paths (?x = ?y) ?a ?b => constr:(a) end in
                  let b := match goal with |- @paths (?x = ?y) ?a ?b => constr:(b) end in
                  let x := match goal with |- @paths (?x = ?y) ?a ?b => constr:(x) end in
                  let y := match goal with |- @paths (?x = ?y) ?a ?b => constr:(y) end in
                  apply (@equiv_inv _ _ _ (@equiv_ap _ _ _ (@isequiv_apD10 _ _ _ x y) a b));
                  exact (center _)
                )
            | pose proof (@path_contr T _ idpath p) as H ];
      destruct H;
      (* now reduce any matches on [idpath] (and on other things too) *)
      cbv iota in *
    ).

(** Use both [induction_hammer] and [clear_contr_path] on a path, to try to get rid of it *)
Ltac clear_path_no_check p :=
  induction_hammer p || clear_contr_path p.
Ltac clear_path p :=
  let t := type of p in
  lazymatch eval hnf in t with
    | @paths _ _ _ => clear_path_no_check p || fail 1 "cannot clear path" p
    | _ => fail 0 "clear_path only works on paths;" p "is not a path"
  end.

(** Run [clear_path] on hypotheses *)
(** We don't match only on things of type [_ = _], because maybe that's the head normal form, but it's hiding behind something else; [clear_path] will make sure it's of the right type.  We include some redundant cases at the top, for speed; it is faster to try to destruct everything first, and then do the full battery of tactics, than to just run the hammer. *)
Ltac step_clear_paths :=
  idtac;
  match goal with
    | [ p : _ = _ |- _ ] => destruct p
    | [ p : _ = _ |- _ ] => clear_path_no_check p
    | [ p : _ |- _ ] => clear_path p
  end.
Ltac clear_paths := progress repeat step_clear_paths.

(** Run [clear_path] on anything inside a [match] *)
Ltac step_clear_paths_in_match :=
  idtac;
  match goal with
    | [ |- context[match ?p with idpath => _ end] ] => progress destruct p
    | [ |- context[match ?p with idpath => _ end] ] => clear_path_no_check p
  end.
Ltac clear_paths_in_match := progress repeat step_clear_paths_in_match.

(** Now some lemmas about trivial [match]es *)
Definition match_eta {T} {x y : T} (H0 : x = y)
: (H0 = match H0 in (_ = y) return (x = y) with
          | idpath => idpath
        end)
  := match H0 with idpath => idpath end.

Definition match_eta1 {T} {x : T} (E : x = x)
: (match E in (_ = y) return (x = y) with
     | idpath => idpath
   end = idpath)
  -> idpath = E
  := fun H => ((H # match_eta E) ^)%path.

Definition match_eta2 {T} {x : T} (E : x = x)
: (idpath
   = match E in (_ = y) return (x = y) with
       | idpath => idpath
     end)
  -> idpath = E
  := fun H => match_eta1 E (H ^)%path.

(** And now the actual tactic.  Note that the order of the cases in the [match goal with ... end] is somewhat finely tuned for speed. *)
Ltac step_path_induction_hammer :=
  idtac;
  match goal with
    | _ => reflexivity
    | _ => intro
    | _ => progress cbn in *
    | _ => exact (contr _)
    | [ p : _ = _ |- _ ]
      => progress destruct p (* placed up here for speed *)
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta1 _ H); destruct H'
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta2 _ H); destruct H'
    | _ => step_clear_paths
    | _ => expand; step_clear_paths_in_match
    | _ => progress auto with path_hints
    | _ => done
    | _ => exact (center _)
  end.

Ltac path_induction_hammer := progress repeat step_path_induction_hammer.

(** * Miscellaneous tactics *)

(** Substitute all hypotheses with bodies, i.e., of the form [H := _]. *)
Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

(** Some tactics to do things with some arbitrary hypothesis in the context.  These tactics are similar to, e.g., [assumption]. *)

Ltac do_with_hyp tac :=
  idtac;
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(** Run [simpl] on a hypothesis before rewriting with it. *)
Ltac simpl_do_clear tac term :=
  let H := fresh in
  assert (H := term);
    cbn in H |- *;
    tac H;
    clear H.

(** The behavior of [simpl rewrite] with respect to implicit arguments is slightly different from that of [rewrite].  In some ways, it is a little more like [erewrite], but in fact both [rewrite] and [erewrite] use magic that we are unable to exactly duplicate with a user-defined tactic.

The point is that for a user-defined tactic, Coq has to resolve the meaning of the term passed to it in some way before the tactic begins executing.  In particular, if that term involves maximally inserted implicit arguments, then it will have to fill them in; but often there will be no way to do that.  If we declared the argument of [simpl rewrite] as a [constr], then this would cause it to fail.  Instead, we declare it as an [open_constr], which allows Coq to fill in those implicit arguments with existential variables, which can then be instantiated later during the rewriting. *)

Tactic Notation "simpl" "rewrite"      open_constr(term) := simpl_do_clear ltac:(fun H => rewrite    H) term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite -> H) term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite <- H) term.

Tactic Notation "simpl" "rewrite"      open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- H in hyp) term.

Tactic Notation "simpl" "rewrite"      open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    H in * ) term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- H in * ) term.

Tactic Notation "simpl" "rewrite"      open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- H in * |- ) term.


Tactic Notation "simpl" "rewrite"      "!" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite    !H) term.
Tactic Notation "simpl" "rewrite" "->" "!" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite -> !H) term.
Tactic Notation "simpl" "rewrite" "<-" "!" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite <- !H) term.

Tactic Notation "simpl" "rewrite"      "!" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    !H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" "!" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> !H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" "!" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- !H in hyp) term.

Tactic Notation "simpl" "rewrite"      "!" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    !H in * ) term.
Tactic Notation "simpl" "rewrite" "->" "!" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> !H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- !H in * ) term.

Tactic Notation "simpl" "rewrite"      "!" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    !H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" "!" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> !H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- !H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      "!" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    !H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" "!" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> !H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" "!" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- !H in * |- ) term.


Tactic Notation "simpl" "rewrite"      "?" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite    ?H) term.
Tactic Notation "simpl" "rewrite" "->" "?" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite -> ?H) term.
Tactic Notation "simpl" "rewrite" "<-" "?" open_constr(term) := simpl_do_clear ltac:(fun H => rewrite <- ?H) term.

Tactic Notation "simpl" "rewrite"      "?" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite    ?H in hyp) term.
Tactic Notation "simpl" "rewrite" "->" "?" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite -> ?H in hyp) term.
Tactic Notation "simpl" "rewrite" "<-" "?" open_constr(term) "in" hyp(hyp) := simpl_do_clear ltac:(fun H => rewrite <- ?H in hyp) term.

Tactic Notation "simpl" "rewrite"      "?" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite    ?H in * ) term.
Tactic Notation "simpl" "rewrite" "->" "?" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite -> ?H in * ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" open_constr(term) "in" "*" := simpl_do_clear ltac:(fun H => rewrite <- ?H in * ) term.

Tactic Notation "simpl" "rewrite"      "?" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite    ?H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "->" "?" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite -> ?H in hyp |- * ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" open_constr(term) "in" hyp(hyp) "|-" "*" := simpl_do_clear ltac:(fun H => rewrite <- ?H in hyp |- * ) term.

Tactic Notation "simpl" "rewrite"      "?" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite    ?H in * |- ) term.
Tactic Notation "simpl" "rewrite" "->" "?" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite -> ?H in * |- ) term.
Tactic Notation "simpl" "rewrite" "<-" "?" open_constr(term) "in" "*" "|-" := simpl_do_clear ltac:(fun H => rewrite <- ?H in * |- ) term.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(* given a [matcher] that succeeds on some hypotheses and fails on
   others, destruct any matching hypotheses, and then execute [tac]
   after each [destruct].

   The [tac] part exists so that you can, e.g., [simpl in *], to
   speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(** matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

(** Turns a context object, obtained via, e.g., [match goal with |- context G[...] => ... end], into a lambda / gallina function. *)
Ltac context_to_lambda G :=
  let ret := constr:(fun x => let k := x in
                              ltac:(
                                let ret := context G[k] in
                                exact ret)) in
  (eval cbv zeta in ret).
