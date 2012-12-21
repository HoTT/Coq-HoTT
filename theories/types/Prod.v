(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about cartesian products *)

Require Import Common Paths Contractible Equivalences Funext.
Open Scope path_scope.
Open Scope equiv_scope.

(* What is this for? *)
Definition prod_unpack {A B : Type} {P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u
  :=
  let (x, y) as u return (P (fst u, snd u) -> P u) := u in idmap.

(** *** Eta conversion *)

Definition eta_prod {A B : Type} (z : A * B) : (fst z, snd z) = z
  := match z with (x,y) => 1 end.

(** *** Universal mapping property *)

(* Doing this sort of thing without adjointifying will require very careful use of funext. *)
Instance isequiv_prod_rect {A B : Type} (P : A * B -> Type)
  : IsEquiv (prod_rect P)
  := isequiv_adjointify _
  (fun f x y => f (x,y))
  (fun f => funext
    (fun z => prod_rect P (fun x y => f (x,y)) z)
    f (fun z => match z with (a,b) => 1 end))
  (fun f => funext2
    (fun x y => prod_rect P f (x,y))
    f (fun a b => 1)).

(** *** Paths *)

(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z')
  := match pq with (p,q) => 
       match z, z' return
         (fst z = fst z') -> (snd z = snd z') -> (z = z') with
         | (a,b), (a',b') => fun p q =>
           match p, q with
             idpath, idpath => 1
           end
       end p q
     end.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of product types.  But it has the advantage that the components of those pairs can more often be inferred. *)
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.

(** Now we show how these things compute. *)

Definition ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p.
Proof.
  revert p q; destruct z, z'; simpl; intros [] []; reflexivity.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  revert p q; destruct z, z'; simpl; intros [] []; reflexivity.
Defined.

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
Proof.
  destruct p. destruct z. reflexivity.
Defined.

(** This lets us identify the path space of a product type, up to equivalence. *)

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
  : IsEquiv (path_prod_uncurried z z').
  refine (BuildIsEquiv _ _ _
    (fun r => (ap fst r, ap snd r))
    eta_path_prod
    (fun pq => match pq with
                 | (p,q) => path_prod' 
                   (ap_fst_path_prod p q) (ap_snd_path_prod p q)
               end) _).
  destruct z as [x y], z' as [x' y'].
  intros [p q]; simpl in p, q.
  destruct p, q; reflexivity.
Defined.

Definition equiv_path_prod {A B : Type} {z z' : A * B}
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := BuildEquiv _ _ (path_prod_uncurried z z') _.

(** *** Transport *)

Definition trans_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (x : P a) (y : Q a)
  : transport (fun a => P a * Q a) p (x,y)
  = (transport P p x, transport Q p y)
  := match p with idpath => 1 end.

(** *** HLevel *)

Generalizable Variables A B f g.

Instance contr_prod `{Contr A} `{Contr B} : Contr (A * B)
  := BuildContr (A * B) (center A, center B)
  (fun z:A*B => path_prod (center A, center B) _
    (contr (fst z)) (contr (snd z))).

(** *** Functorial action *)

Definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  : A * B -> A' * B'
  := fun z => (f (fst z), g (snd z)).

Definition ap_functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  (z z' : A * B) (p : fst z = fst z') (q : snd z = snd z')
  : ap (functor_prod f g) (path_prod _ _ p q)
  = path_prod (functor_prod f g z) (functor_prod f g z') (ap f p) (ap g q).
Proof.
  destruct z as [a b]; destruct z' as [a' b'].
  simpl in p, q. destruct p, q. reflexivity.
Defined.

(** *** Equivalences *)

Instance isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : IsEquiv (functor_prod f g).
  refine (BuildIsEquiv _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
    (fun z => path_prod' (eisretr f (fst z)) (eisretr g (snd z)) @ eta_prod z)
    (fun w => path_prod' (eissect f (fst w)) (eissect g (snd w)) @ eta_prod w)
    _).
  intros [a b]; simpl. repeat rewrite concat_p1.
  unfold path_prod'; rewrite ap_functor_prod.
  repeat rewrite eisadj; reflexivity.
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'
  (* Why can't it find the instance [isequiv_functor_prod]? *)
  := BuildEquiv _ _ (functor_prod f g) isequiv_functor_prod.
