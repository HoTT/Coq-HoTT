(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about cartesian products *)

Require Import Overture PathGroupoids Equivalences Trunc.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : A * B] by writing [u] as a pair [(fst u ; snd u)]. This is accomplished by [unpack_prod]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_prod `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u
  := idmap.

Arguments unpack_prod / .

(** Now we write down the reverse. *)
Definition pack_prod `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u)
  := idmap.

Arguments pack_prod / .

(** ** Eta conversion *)

Definition eta_prod `(z : A * B) : (fst z, snd z) = z
  := 1.

Arguments eta_prod / .

(** ** Paths *)

(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z')
  := match fst pq in (_ = z'1), snd pq in (_ = z'2) return z = (z'1, z'2) with
       | 1, 1 => 1
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
  destruct p. reflexivity.
Defined.

(** Now we show how these compute with transport. *)

Lemma transport_path_prod_uncurried A B (P : A * B -> Type) (x y : A * B)
      (H : (fst x = fst y) * (snd x = snd y))
      Px
: transport P (path_prod_uncurried _ _ H) Px
  = unpack_prod
      y
      (transport (fun x => P (x, snd y))
                 (fst H)
                 (transport (fun y => P (fst x, y))
                            (snd H)
                            (pack_prod x Px))).
Proof.
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod A B (P : A * B -> Type) (x y : A * B)
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           Px
: transport P (path_prod _ _ HA HB) Px
  = unpack_prod
      y
      (transport (fun x => P (x, snd y))
                 HA
                 (transport (fun y => P (fst x, y))
                            HB
                            (pack_prod x Px)))
  := transport_path_prod_uncurried _ _ P x y (HA, HB) Px.

Definition transport_path_prod'
           A B (P : A * B -> Type)
           (x y : A)
           (x' y' : B)
           (HA : x = y)
           (HB : x' = y')
           Px
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px)
  := transport_path_prod _ _ P (x, x') (y, y') HA HB Px.

(** This lets us identify the path space of a product type, up to equivalence. *)

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
  : IsEquiv (path_prod_uncurried z z') | 0.
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

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := BuildEquiv _ _ (path_prod_uncurried z z') _.

(** ** Transport *)

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (p # (fst z), p # (snd z))
  := match p with idpath => 1 end.

(** ** Functorial action *)

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

(** ** Equivalences *)

Instance isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : IsEquiv (functor_prod f g) | 1000.
  refine (BuildIsEquiv _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
    (fun z => path_prod' (eisretr f (fst z)) (eisretr g (snd z)) @ eta_prod z)
    (fun w => path_prod' (eissect f (fst w)) (eissect g (snd w)) @ eta_prod w)
    _).
  intros [a b]; simpl.
  unfold path_prod'.
  repeat rewrite concat_p1.
  rewrite ap_functor_prod.
  repeat rewrite eisadj.
  reflexivity.
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod_l {A B B' : Type} (g : B <~> B')
  : A * B <~> A * B'.
Proof.
  exists (functor_prod idmap g).
  exact _.    (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod_r {A A' B : Type} (f : A <~> A')
  : A * B <~> A' * B.
Proof.
  exists (functor_prod f idmap).
  exact _.    (* i.e., search the context for instances *)
Defined.

(** ** Symmetry *)

(** This is a special property of [prod], of course, not an instance of a general family of facts about types. *)

Definition equiv_prod_symm (A B : Type) : A * B <~> B * A.
Proof.
  refine (BuildEquiv (A*B) (B*A)
    (fun ab => let (a,b) := ab in (b,a))
    (BuildIsEquiv (A*B) (B*A) _
      (fun ba => let (b,a) := ba in (a,b))
      (fun ba => let (b,a) as ba return
            ((let (a,b) := (let (b,a) := ba in (a,b)) in (b,a)) = ba)
                 := ba in 1)
    (fun ab => let (a,b) as ab return
            ((let (b,a) := (let (a,b) := ab in (b,a)) in (a,b)) = ab)
                 := ab in 1)
    _)).
  intros [a b]. reflexivity.
Defined.

(** ** Associativity *)

(** This, too, is a special property of [prod], of course, not an instance of a general family of facts about types. *)
Definition equiv_prod_assoc (A B C : Type) : A * (B * C) <~> (A * B) * C.
Proof.
  refine (BuildEquiv
            _ _ _
            (BuildIsEquiv
               (A * (B * C)) ((A * B) * C)
               (fun abc => ((fst abc, fst (snd abc)), snd (snd abc)))
               (fun abc => (fst (fst abc), (snd (fst abc), snd abc)))
               _ _ _)).
  { intros [[a b] c]; reflexivity. }
  { intros [a [b c]]; reflexivity. }
  { intros [a [b c]]; reflexivity. }
Defined.

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions.  Moreover, because the product type can expressed both positively and negatively, it has both a left universal property and a right one. *)

(* First the positive universal property.
   Doing this sort of thing without adjointifying will require very careful use of funext. *)
Instance isequiv_prod_rect `{Funext} `(P : A * B -> Type)
  : IsEquiv (prod_rect P) | 0
  := isequiv_adjointify _
  (fun f x y => f (x,y))
  (fun f => path_forall
    (fun z => prod_rect P (fun x y => f (x,y)) z)
    f (fun z => match z with (a,b) => 1 end))
  (fun f => path_forall2
    (fun x y => prod_rect P f (x,y))
    f (fun a b => 1)).

Definition equiv_prod_rect `{Funext} `(P : A * B -> Type)
  : (forall (a : A) (b : B), P (a, b)) <~> (forall p : A * B, P p)
  := BuildEquiv _ _ (prod_rect P) _.

(* The non-dependent version, which is a special case, is the currying equivalence. *)
Definition equiv_uncurry `{Funext} (A B C : Type)
  : (A -> B -> C) <~> (A * B -> C)
  := equiv_prod_rect (fun _ => C).

(* Now the negative universal property. *)
Definition prod_corect_uncurried `{A : X -> Type} `{B : X -> Type}
  : (forall x, A x) * (forall x, B x) -> (forall x, A x * B x)
  := fun fg x => let (f,g):=fg in (f x, g x).

Definition prod_corect `(f : forall x:X, A x) `(g : forall x:X, B x)
  : forall x, A x * B x
  := prod_corect_uncurried (f,g).

Instance isequiv_prod_corect `{Funext} `(A : X -> Type) (B : X -> Type)
  : IsEquiv (@prod_corect_uncurried X A B) | 0
  := isequiv_adjointify _
  (fun h => (fun x => fst (h x), fun x => snd (h x)))
  _ _.
Proof.
  - intros h.
    apply path_forall; intros x.
    apply path_prod; simpl; reflexivity.
  - intros [f g].
    apply path_prod; simpl; reflexivity.
Defined.

Definition equiv_prod_corect `{Funext} `(A : X -> Type) (B : X -> Type)
  : ((forall x, A x) * (forall x, B x)) <~> (forall x, A x * B x)
  := BuildEquiv _ _ (@prod_corect_uncurried X A B) _.

(** ** Products preserve truncation *)

Instance trunc_prod `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B ?.
  exists (center A, center B).
    intros z; apply path_prod; apply contr.
  intros x y.
    exact (trunc_equiv (equiv_path_prod x y)).
Defined.

Instance contr_prod `{CA : Contr A} `{CB : Contr B} : Contr (A * B) | 100
  := @trunc_prod minus_two A CA B CB.
