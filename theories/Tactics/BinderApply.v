(** * Apply a lemma under binders *)

Ltac make_tac_under_binders_in tac H :=
  let rec_tac := make_tac_under_binders_in tac in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              $(let ret' := rec_tac Hx in
                                exact ret')$) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    | _ => let ret := constr:($(let H' := fresh in
                                pose H as H';
                                tac H';
                                exact H')$) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
  end.

Ltac do_tac_under_binders_in tac H :=
  let H' := make_tac_under_binders_in tac H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.

Tactic Notation "constrbinder" "apply" constr(lem) "in" constr(H) := make_tac_under_binders_in ltac:(fun H' => apply lem in H') H.
Tactic Notation "constrbinder" "eapply" open_constr(lem) "in" constr(H) := constrbinder apply lem in H.

Tactic Notation "binder" "apply" constr(lem) "in" constr(H) := do_tac_under_binders_in ltac:(fun H' => apply lem in H') H.
Tactic Notation "binder" "eapply" open_constr(lem) "in" constr(H) := binder apply lem in H.
