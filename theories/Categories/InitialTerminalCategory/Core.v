(** * Initial and terminal category definitions *)
Require Import HoTT.Basics HoTT.Types.
Require Import Category.Core.
Require Import NatCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Local Unset Primitive Projections. (* suppress a warning about [IsTerminalCategory] *)

Notation initial_category := (nat_category 0) (only parsing).
Notation terminal_category := (nat_category 1) (only parsing).

(** ** Terminal categories *)
(** A precategory is terminal if its objects and morphisms are contractible types. *)
Class IsTerminalCategory (C : PreCategory)
      `{Contr (object C)}
      `{forall s d, Contr (morphism C s d)}
  : Type0 := {}.

(** ** Initial categories *)
(** An initial precategory is one whose objects have the recursion principle of the empty type *)
Class IsInitialCategory (C : PreCategory)
  := initial_category_ind : forall P : Type, C -> P.

Instance trunc_initial_category `{IsInitialCategory C}
: IsHProp C
  := istrunc_S _ (fun x y => initial_category_ind _ x).
Instance trunc_initial_category_mor `{IsInitialCategory C} x y
: Contr (morphism C x y)
  := initial_category_ind _ x.

(** ** Default initial ([0]) and terminal ([1]) precategories. *)
Instance is_initial_category_0 : IsInitialCategory 0 := (fun T => @Empty_ind (fun _ => T)).
Instance: IsTerminalCategory 1 | 0 := {}.
Instance: Contr (object 1) | 0 := _.
Instance : `{Contr (morphism 1 x y)} | 0 := fun x y => _.
Instance default_terminal C {H H1} : @IsTerminalCategory C H H1 | 10 := {}.

Arguments initial_category_ind / .
Arguments is_initial_category_0 / .
