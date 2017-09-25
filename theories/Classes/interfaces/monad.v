Require Export
  HoTT.Classes.interfaces.canonical_names.

Class Monad (M : Type -> Type) {Mret : Return M} {Mbind : Bind M} :=
  { monad_ret_bind : forall {A B} a (f : A -> M B), bind (ret a) f = f a
  ; monad_bind_ret : forall {A} (x : M A), bind x ret = x
  ; monad_bind_assoc : forall {A B C} x (f : A -> M B) (g : B -> M C),
    bind (bind x f) g = bind x (fun a => bind (f a) g) }.

