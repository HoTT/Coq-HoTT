(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about disjoint unions *)

Require Import Overture PathGroupoids Equivalences Trunc types.Empty.
(** The following are only required for the equivalence between [sum] and a sigma type *)
Require Import types.Bool types.Forall types.Sigma.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.
Set Implicit Arguments.

(** ** CoUnpacking *)

(** Sums are coproducts, so there should be a dual to [unpack_prod].  I'm not sure what it is, though. *)

(** ** Eta conversion *)

Definition eta_sum `(z : A + B) : match z with
                                    | inl z' => inl z'
                                    | inr z' => inr z'
                                  end = z
  := match z with inl _ => 1 | inr _ => 1 end.

(** ** Paths *)

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.
  destruct z, z', pq; exact idpath.
Defined.

Definition path_sum_inv {A B : Type} (z z' : A + B)
           (pq : z = z')
: match z, z' with
    | inl z0, inl z'0 => z0 = z'0
    | inr z0, inr z'0 => z0 = z'0
    | _, _ => Empty
  end
  := match pq with
       | 1 => match z with
                | inl _ => 1
                | inr _ => 1
              end
     end.

(** This version produces only paths between closed terms, as opposed to paths between arbitrary inhabitants of sum types. *)
Definition path_sum_inl {A B : Type} {x x' : A}
: inl x = inl x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

Definition path_sum_inr {A B : Type} {x x' : B}
: inr x = inr x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

(** This lets us identify the path space of a sum type, up to equivalence. *)

Definition eisretr_path_sum {A B} {z z' : A + B}
: Sect (@path_sum_inv _ _ z z') (path_sum z z')
  := fun p => match p as p in (_ = z') return
                    path_sum z z' (path_sum_inv p) = p
              with
                | 1 => match z as z return
                             path_sum z z (path_sum_inv 1) = 1
                       with
                         | inl _ => 1
                         | inr _ => 1
                       end
              end.

Definition eissect_path_sum {A B} {z z' : A + B}
: Sect (path_sum z z') (@path_sum_inv _ _ z z').
Proof.
  intro p.
  destruct z, z', p; exact idpath.
Defined.

Instance isequiv_path_sum {A B : Type} {z z' : A + B}
: IsEquiv (path_sum z z') | 0.
Proof.
  refine (BuildIsEquiv _ _
                       (path_sum z z')
                       (@path_sum_inv _ _ z z')
                       (@eisretr_path_sum A B z z')
                       (@eissect_path_sum A B z z')
                       _).
  destruct z, z';
    intros [];
    exact idpath.
Defined.

Definition equiv_path_sum {A B : Type} (z z' : A + B)
  := BuildEquiv _ _ _ (@isequiv_path_sum A B z z').

(** ** Transport *)

Definition transport_sum {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
           (z : P a + Q a)
: transport (fun a => P a + Q a) p z = match z with
                                         | inl z' => inl (p # z')
                                         | inr z' => inr (p # z')
                                       end
  := match p with idpath => match z with inl _ => 1 | inr _ => 1 end end.

(** ** Functorial action *)

Definition functor_sum {A A' B B' : Type} (f : A -> A') (g : B -> B')
: A + B -> A' + B'
  := fun z => match z with inl z' => inl (f z') | inr z' => inr (g z') end.

(** ** Equivalences *)

Instance isequiv_functor_sum `{IsEquiv A A' f} `{IsEquiv B B' g}
: IsEquiv (functor_sum f g) | 1000.
Proof.
  apply (isequiv_adjointify
           (functor_sum f g)
           (functor_sum f^-1 g^-1));
  [ intros [?|?]; simpl; apply ap; apply eisretr
  | intros [?|?]; simpl; apply ap; apply eissect ].
Defined.

Definition equiv_functor_sum `{IsEquiv A A' f} `{IsEquiv B B' g}
: A + B <~> A' + B'
  := BuildEquiv _ _ _ isequiv_functor_sum.

Definition equiv_functor_sum' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
: A + B <~> A' + B'
  := equiv_functor_sum (f := f) (g := g).

Definition equiv_functor_sum_l {A B B' : Type} (g : B <~> B')
: A + B <~> A + B'
  := equiv_functor_sum (f := idmap) (g := g).

Definition equiv_functor_sum_r {A A' B : Type} (f : A <~> A')
: A + B <~> A' + B
  := equiv_functor_sum (f := f) (g := idmap).

(** ** Symmetry *)

(* This is a special property of [sum], of course, not an instance of a general family of facts about types. *)

Definition equiv_sum_symm (A B : Type) : A + B <~> B + A.
Proof.
  apply (equiv_adjointify
           (fun ab => match ab with inl a => inr a | inr b => inl b end)
           (fun ab => match ab with inl a => inr a | inr b => inl b end));
  intros [?|?]; exact idpath.
Defined.

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions. *)

Definition sum_rect_uncurried A B (P : A + B -> Type)
           (fg : (forall a, P (inl a)) * (forall b, P (inr b)))
: forall s, P s
  := @sum_rect A B P (fst fg) (snd fg).

(* First the positive universal property.
   Doing this sort of thing without adjointifying will require very careful use of funext. *)
Instance isequiv_sum_rect `{Funext} `(P : A + B -> Type)
: IsEquiv (sum_rect_uncurried P) | 0.
Proof.
  apply (isequiv_adjointify
           (sum_rect_uncurried P)
           (fun f => (fun a => f (inl a), fun b => f (inr b))));
  repeat ((exact idpath)
            || intros []
            || intro
            || apply path_forall).
Defined.

Definition equiv_sum_rect `{Funext} `(P : A + B -> Type)
  := BuildEquiv _ _ _ (isequiv_sum_rect P).

(* The non-dependent version, which is a special case, is the sum-distributive equivalence. *)
Definition equiv_sum_distributive `{Funext} (A B C : Type)
: (A -> C) * (B -> C) <~> (A + B -> C)
  := equiv_sum_rect (fun _ => C).

(** ** Sums preserve most truncation *)

Instance trunc_sum n' (n := trunc_S (trunc_S n'))
         `{IsTrunc n A, IsTrunc n B}
: IsTrunc n (A + B) | 100.
Proof.
  intros a b.
  eapply trunc_equiv';
    [ exact (equiv_path_sum _ _) | ].
  destruct a, b; simpl in *;
  try typeclasses eauto;
  intros [].
Defined.

Instance hset_sum `{HA : IsHSet A, HB : IsHSet B} : IsHSet (A + B) | 100
  := @trunc_sum minus_two A HA B HB.

(** ** Binary coproducts are equivalent to dependent sigmas where the first component is a bool. *)

Definition sigT_of_sum A B (x : A + B)
: { b : Bool & if b then A else B }
  := (_;
      match
        x as s
        return
        (if match s with
              | inl _ => true
              | inr _ => false
            end then A else B)
      with
        | inl a => a
        | inr b => b
      end).

Definition sum_of_sigT A B (x : { b : Bool & if b then A else B })
: A + B
  := match x with
       | (true; a) => inl a
       | (false; b) => inr b
     end.

Instance isequiv_sigT_of_sum A B : IsEquiv (@sigT_of_sum A B) | 0.
Proof.
  apply (isequiv_adjointify (@sigT_of_sum A B)
                            (@sum_of_sigT A B));
  repeat (intros [[]] || intros [] || intro); apply idpath.
Defined.

Instance isequiv_sum_of_sigT A B : IsEquiv (sum_of_sigT A B)
  := isequiv_inverse.

(** An alternative way of proving the truncation property of [sum]. *)
Definition trunc_sum' n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B}
: (IsTrunc n (A + B)).
Proof.
  eapply trunc_equiv'; [ esplit;
                         exact (@isequiv_sum_of_sigT _ _)
                       | ].
  typeclasses eauto.
Defined.
