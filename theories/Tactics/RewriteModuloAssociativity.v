(** * Tactics for rewriting modulo assciativity *)
Require Import Overture PathGroupoids.
Require Import Tactics.BinderApply.

Local Open Scope path_scope.

(** Throughout this file, we prefix with [idtac; ] all imperative tactics (those not returning constrs) which would otherwise start with [let] or [match].  This prevents them from being evaluated at the call site.  See https://coq.inria.fr/bugs/show_bug.cgi?id=3498 for more details on this difference between tactics and tactic expressions. *)

(** rewrite [lem] modulo associativity using:

    - [assoc_tac : unit] to associate the goal (in place)
    - [assoc_in_tac : hyp -> unit] to associate the hypothesis (in place)
    - [prepostcompose_any_tac : constr -> constr] to pre/post compose an arbitrary morphism onto the lemma
    - [rew_tac : hyp -> unit] to do the actual rewriting (in place).  This tactic is called first with the non-associated version of  the lemma, then with the associated version.
 *)
Ltac rewriteA_using_helper rew_tac lem prepostcompose_any_tac assoc_tac assoc_in_tac :=
  idtac;
  let lem' := prepostcompose_any_tac lem in
  let H := fresh in
  pose proof lem' as H;
    assoc_tac;
    match goal with
      | _ => rew_tac H
      | _ => assoc_in_tac H;
            rew_tac H
    end;
    clear H.

(** This tactic is similar to the above, except that it passes both the unassociated lemma and the associated lemma to [repeat_rew_tac], which may then contain optimizations over a manual [repeat] such as being [rewrite ?lem, ?lem']. *)
Ltac repeat_rewriteA_using_helper repeat_rew_tac lem prepostcompose_any_tac assoc_tac assoc_in_tac :=
  idtac;
  let lem' := prepostcompose_any_tac lem in
  let H := fresh in
  pose proof lem' as H;
    assoc_in_tac H;
    assoc_tac;
    repeat_rew_tac lem' H;
    clear H.

Module Export Compose.
  (** ** Rewriting modulo associativity of composition ([o]) *)
  (** Since [f o g] is just a notation, we need to define a constant
      that isn't reduced by [cbv beta]. *)
  Local Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  Ltac to_compose T :=
    match T with
      | context G[?g o ?f] => let T' := context G[compose g f] in
                              to_compose T'
      | ?T' => constr:T'
    end.

  (** Turns a lemma of type [f = g] into [forall h, h o f = h o g] *)
  Ltac precompose_any H :=
    let ret := make_tac_under_binders_using_in ltac:(fun H => (let H' := fresh in
                                                               rename H into H';
                                                               let T := type of H' in
                                                               let T' := to_compose T in
                                                               pose proof (fun src (g : _ -> src) => @ap _ _ (fun f => compose g f) _ _ (H' : T')) as H))
                                                      ltac:idtac H in
    let T := type of ret in
    let T' := (eval cbv beta in T) in
    constr:(ret : T').

  (** Associates a type fully to the left *)
  Ltac left_associate_compose_type T :=
    let rec_tac := left_associate_compose_type in
    match to_compose T with
      | forall a : ?A, @?P a => let ret := constr:(forall a : A, let T' := P a in
                                                                 ltac:(
                                                                   let T'' := (eval unfold T' in T') in
                                                                   let ret := rec_tac T'' in
                                                                   exact ret)) in
                                eval cbv beta zeta in ret
      | context T'[compose ?a (compose ?b ?c)]
        => let T'' := context T'[compose (compose a b) c] in
           rec_tac T''
      | ?T' => constr:(T')
    end.

  Ltac left_associate_compose_in_type_of H :=
    let T := type of H in
    let T' := left_associate_compose_type T in
    constr:(H : T').

  Ltac left_associate_compose :=
    idtac;
    (lazymatch goal with
    | [ |- ?G ] => let G' := left_associate_compose_type G in change G'
     end).

  Ltac left_associate_compose_in H :=
    idtac;
    (lazymatch type of H with
    | ?T => let T' := left_associate_compose_type T in change T' in H
     end).

  Ltac after_rewrite :=
    repeat match goal with
             | [ |- context G[compose ?g ?f] ] => let G' := context G[g o f] in change G'
             | _ =>
               match goal with
                 | [ |- context G[@compose ?A ?B ?C ?g] ] => let G' := context G[fun f : A -> B => g o f] in change G'
                 | [ |- context G[@compose ?A ?B ?C] ] => let G' := context G[fun (g : B -> C) (f : A -> B) => g o f] in change G'
                 | _ => progress cbv delta [compose]
               end;
                 idtac "Warning: could not fully restore pre-rewrite state."
                       "Try introducing more things or removing binders."
           end.

  Tactic Notation "rewriteoA" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "->" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite -> lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "<-" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite <- lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite ?lem', ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite ?lem', ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "->" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite -> ?lem', -> ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "<-" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite <- ?lem', <- ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "->" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite -> ?lem', -> ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "rewriteoA" "<-" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite <- ?lem', <- ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.



  Tactic Notation "erewriteoA" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "->" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite -> lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "<-" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite <- lem') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite ?lem', ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite ?lem', ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "->" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite -> ?lem', -> ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "<-" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite <- ?lem', <- ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "->" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite -> ?lem', -> ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.
  Tactic Notation "erewriteoA" "<-" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite <- ?lem', <- ?lem'') lem ltac:precompose_any ltac:left_associate_compose ltac:left_associate_compose_in; after_rewrite.


  Tactic Notation "rewrite∘A" constr(lem) := rewriteoA lem.
  Tactic Notation "rewrite∘A" "->" constr(lem) := rewriteoA -> lem.
  Tactic Notation "rewrite∘A" "<-" constr(lem) := rewriteoA <- lem.
  Tactic Notation "rewrite∘A" "!" constr(lem) := rewriteoA !lem.
  Tactic Notation "rewrite∘A" "?" constr(lem) := rewriteoA ? lem.
  Tactic Notation "rewrite∘A" "->" "!" constr(lem) := rewriteoA -> !lem.
  Tactic Notation "rewrite∘A" "<-" "!" constr(lem) := rewriteoA <- !lem.
  Tactic Notation "rewrite∘A" "->" "?" constr(lem) := rewriteoA -> ? lem.
  Tactic Notation "rewrite∘A" "<-" "?" constr(lem) := rewriteoA <- ? lem.


  Tactic Notation "erewrite∘A" open_constr(lem) := erewriteoA lem.
  Tactic Notation "erewrite∘A" "->" open_constr(lem) := erewriteoA -> lem.
  Tactic Notation "erewrite∘A" "<-" open_constr(lem) := erewriteoA <- lem.
  Tactic Notation "erewrite∘A" "!" open_constr(lem) := erewriteoA !lem.
  Tactic Notation "erewrite∘A" "?" open_constr(lem) := erewriteoA ? lem.
  Tactic Notation "erewrite∘A" "->" "!" open_constr(lem) := erewriteoA -> !lem.
  Tactic Notation "erewrite∘A" "<-" "!" open_constr(lem) := erewriteoA <- !lem.
  Tactic Notation "erewrite∘A" "->" "?" open_constr(lem) := erewriteoA -> ? lem.
  Tactic Notation "erewrite∘A" "<-" "?" open_constr(lem) := erewriteoA <- ? lem.
End Compose.

Module Export Concat.
  (** ** Rewriting modulo associativity of concatenation ([@]) *)
  (** Turns a lemma of type [f = g] into [forall h, h @ f = h @ g] *)
  Ltac preconcat_any H :=
    let ret := make_tac_under_binders_using_in ltac:(fun H => (let H' := fresh in
                                                               rename H into H';
                                                               pose proof (fun dst (g : dst = _) => @ap _ _ (fun f => g @ f) _ _ H') as H))
                                                      ltac:idtac H in
    let T := type of ret in
    let T' := (eval cbv beta in T) in
    constr:(ret : T').

  (** Associates a path fully to the left *)
  Ltac left_associate_concat_in H :=
    let rec_tac := left_associate_concat_in in
    let T := type of H in
    let T' := (eval cbv beta in T) in
    match T' with
      | forall a : ?A, @?P a => let ret := constr:(fun a : A => let H' := H a in
                                                                ltac:(
                                                                  let H'' := (eval unfold H' in H') in
                                                                  let ret := rec_tac H'' in
                                                                  exact ret)) in
                                let T := type of ret in
                                let T' := (eval cbv beta zeta in T) in
                                let ret' := (eval cbv beta zeta in ret) in
                                constr:(ret' : T')
      | context[@concat ?A1 ?x1 ?y1 ?z1 ?a (@concat ?A2 ?x2 ?y2 ?z2 ?b ?c)] =>
        (lazymatch eval pattern (@concat A1 x1 y1 z1 a (@concat A2 x2 y2 z2 b c)) in T' with
        | ?P _ => let H' := constr:(transport P (concat_p_pp a b c) H) in
                  rec_tac H'
         end)
      | ?T' => constr:(H : T')
    end.

  (** We really should just use [setoid_rewrite -> !concat_p_pp] here, to take care of binders, but we threw away Setoids. *)
  Ltac left_associate_concat :=
    repeat match goal with
             | _ => rewrite -> !concat_p_pp
             | [ |- forall a : ?A, _ ] => let H := fresh in
                                          intro H;
                                            left_associate_concat;
                                            revert H
           end.

  Ltac left_associate_concat_in_hyp H :=
    let H' := fresh in
    rename H into H';
      let H_rep := left_associate_concat_in H' in
      pose proof H_rep as H;
        clear H'.

  Tactic Notation "rewrite@A" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "->" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite -> lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "<-" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => rewrite <- lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite ?lem', ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite ?lem', ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "->" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite -> ?lem', -> ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "<-" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress rewrite <- ?lem', <- ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "->" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite -> ?lem', -> ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "rewrite@A" "<-" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => rewrite <- ?lem', <- ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.



  Tactic Notation "erewrite@A" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "->" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite -> lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "<-" constr(lem) :=
    rewriteA_using_helper ltac:(fun lem' => erewrite <- lem') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite ?lem', ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite ?lem', ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "->" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite -> ?lem', -> ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "<-" "!" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => progress erewrite <- ?lem', <- ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "->" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite -> ?lem', -> ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.
  Tactic Notation "erewrite@A" "<-" "?" constr(lem) :=
    repeat_rewriteA_using_helper ltac:(fun lem' lem'' => erewrite <- ?lem', <- ?lem'') lem ltac:preconcat_any ltac:left_associate_concat ltac:left_associate_concat_in_hyp.

  Tactic Notation "rewrite•A" constr(lem) := rewrite@A lem.
  Tactic Notation "rewrite•A" "->" constr(lem) := rewrite@A -> lem.
  Tactic Notation "rewrite•A" "<-" constr(lem) := rewrite@A <- lem.
  Tactic Notation "rewrite•A" "!" constr(lem) := rewrite@A !lem.
  Tactic Notation "rewrite•A" "?" constr(lem) := rewrite@A ? lem.
  Tactic Notation "rewrite•A" "->" "!" constr(lem) := rewrite@A -> !lem.
  Tactic Notation "rewrite•A" "<-" "!" constr(lem) := rewrite@A <- !lem.
  Tactic Notation "rewrite•A" "->" "?" constr(lem) := rewrite@A -> ? lem.
  Tactic Notation "rewrite•A" "<-" "?" constr(lem) := rewrite@A <- ? lem.


  Tactic Notation "erewrite•A" open_constr(lem) := erewrite@A lem.
  Tactic Notation "erewrite•A" "->" open_constr(lem) := erewrite@A -> lem.
  Tactic Notation "erewrite•A" "<-" open_constr(lem) := erewrite@A <- lem.
  Tactic Notation "erewrite•A" "!" open_constr(lem) := erewrite@A !lem.
  Tactic Notation "erewrite•A" "?" open_constr(lem) := erewrite@A ? lem.
  Tactic Notation "erewrite•A" "->" "!" open_constr(lem) := erewrite@A -> !lem.
  Tactic Notation "erewrite•A" "<-" "!" open_constr(lem) := erewrite@A <- !lem.
  Tactic Notation "erewrite•A" "->" "?" open_constr(lem) := erewrite@A -> ? lem.
  Tactic Notation "erewrite•A" "<-" "?" open_constr(lem) := erewrite@A <- ? lem.
End Concat.

Section examples.
  Section compose.
    Example simple_01 {A} (f g h i j : A -> A) : f o g = h -> (i o f) o (g o j) = i o h o j.
    Proof.
      intro H.
      rewrite∘A H.
      reflexivity.
    Abort.

    Example simple_02 {A} (f g h i j : A -> A) : f o g = h -> (i o f) o (g o f o g o j) = i o h o h o j.
    Proof.
      intro H.
      rewrite∘A !H.
      reflexivity.
    Abort.
  End compose.

  Section concat.
    Example simple_01 {A} {a : A} (f g h i j : a = a) : f @ g = h -> (i @ f) @ (g @ j) = i @ h @ j.
    Proof.
      intro H.
      rewrite@A H.
      reflexivity.
    Abort.

    Example simple_02 {A} {a : A} (f g h i j : A = A) : f @ g = h -> (i @ f) @ (g @ f @ g @ j) = i @ h @ h @ j.
    Proof.
      intro H.
      rewrite@A !H.
      reflexivity.
    Abort.
  End concat.
End examples.
