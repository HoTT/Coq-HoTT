(** * Miscellaneous helper tactics for proving exponential laws *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import HoTT.Tactics Basics.PathGroupoids Types.Forall Types.Prod.

(** These are probably more general than just exponential laws, but I haven't tried them more widely, yet. *)

(** Miscellaneous tactics to try *)
Ltac exp_laws_misc_t' :=
  idtac;
  match goal with
    | _ => reflexivity
    | _ => progress intros
    | _ => progress simpl in *
    | _ => apply (@path_forall _); intro
    | _ => rewrite !identity_of
    | _ => progress autorewrite with morphism
  end.

(** Safe transformations to simplify complex types in the hypotheses or goal *)
Ltac exp_laws_simplify_types' :=
  idtac;
  match goal with
    | [ H : (_ + _)%type |- _ ] => destruct H
    | [ H : Unit |- _ ] => destruct H
    | [ H : Empty |- _ ] => destruct H
    | [ H : (_ * _)%type |- _ ] => destruct H
    | [ |- _ = _ :> Functor _ _ ] => progress path_functor
    | [ |- _ = _ :> NaturalTransformation _ _ ] => progress path_natural_transformation
    | [ |- _ = _ :> prod _ _ ] => apply path_prod
  end.

(** Do some simplifications of contractible types *)
Ltac exp_laws_handle_contr' :=
  idtac;
  match goal with
    | [ H : Contr ?T, x : ?T |- _ ] => progress destruct (contr x)
    | [ H : forall a, Contr (?T a), x : ?T _ |- _ ] => progress destruct (contr x)
    | [ H : forall a b, Contr (?T a b), x : ?T _ _ |- _ ] => progress destruct (contr x)
    | [ |- context[contr (center ?x)] ]
      => progress let H := fresh in
                  assert (H : idpath = contr (center x)) by exact (center _);
                    destruct H
  end.

(** Try to simplify [transport] with some heuristics *)
Ltac exp_laws_handle_transport' :=
  idtac;
  match goal with
    | _ => progress rewrite ?transport_forall_constant, ?path_forall_2_beta, ?transport_const, ?transport_path_prod
    | [ |- context [path_functor_uncurried ?F ?G (?x; ?y)] ] (* https://coq.inria.fr/bugs/show_bug.cgi?id=3768 *)
      => rewrite (@path_functor_uncurried_fst _ _ _ F G x y)
    | [ |- context[transport (fun y : Functor ?C ?D => ?f (y _0 ?x)%object)] ]
      => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x)) (@object_of C D))
    | [ |- context[transport (fun y : Functor ?C ?D => ?f (y _0 ?x)%object ?z)] ]
      => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x) z) (@object_of C D))
    | [ |- context[transport (fun y : Functor ?C ?D => ?f (y _0 ?x)%object ?z)] ]
      => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x) z) (@object_of C D))
    | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (y _0 ?x)%object))] ]
      => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x))) (@object_of C D))
    | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (y _0 ?x)%object) ?z)] ]
      => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x)) z) (@object_of C D))
    | _ => progress transport_path_forall_hammer
    | [ |- context[components_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => components_of) z)
    | [ |- context[object_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => object_of) z)
    | [ |- context[morphism_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => morphism_of) z)
    | [ |- context[fst (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => fst) z)
    | [ |- context[snd (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => snd) z)
    | [ |- context[pr1 (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => pr1) z)
  end.

Ltac exp_laws_t' :=
  first [ exp_laws_misc_t'
        | exp_laws_simplify_types'
        | exp_laws_handle_contr'
        | exp_laws_handle_transport' ].

Ltac exp_laws_t := repeat exp_laws_t'.
