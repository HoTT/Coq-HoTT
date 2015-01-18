(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about disjoint unions *)

Require Import HoTT.Basics.
Require Import Types.Empty Types.Prod Types.Sigma.
(** The following are only required for the equivalence between [sum] and a sigma type *)
Require Import Types.Bool Types.Forall.
Local Open Scope trunc_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

Scheme sum_ind := Induction for sum Sort Type.
Arguments sum_ind {A B} P f g s : rename.

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

Definition path_sum_inv {A B : Type} {z z' : A + B}
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

Definition inl_ne_inr {A B : Type} (a : A) (b : B)
: inl a <> inr b
:= path_sum_inv.

Definition inr_ne_inl {A B : Type} (b : B) (a : A)
: inr b <> inl a
:= path_sum_inv.

(** This version produces only paths between closed terms, as opposed to paths between arbitrary inhabitants of sum types. *)
Definition path_sum_inl {A : Type} (B : Type) {x x' : A}
: inl x = inl x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

Definition path_sum_inr (A : Type) {B : Type} {x x' : B}
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

Global Instance isequiv_path_sum {A B : Type} {z z' : A + B}
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

(** ** Fibers of [inl] and [inr] *)

(** It follows that the fibers of [inl] and [inr] are decidable hprops. *)

Global Instance ishprop_hfiber_inl {A B : Type} (z : A + B)
: IsHProp (hfiber inl z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (trunc_equiv' _
              (equiv_functor_sigma' (equiv_idmap A)
                 (fun x => equiv_path_sum (inl x) (inl a)))).
  - refine (trunc_equiv _
              (fun xp => inl_ne_inr (xp.1) b xp.2)^-1).
Defined.

Global Instance decidable_hfiber_inl {A B : Type} (z : A + B)
: Decidable (hfiber inl z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (decidable_equiv' _
              (equiv_functor_sigma' (equiv_idmap A)
                 (fun x => equiv_path_sum (inl x) (inl a))) _).
  - refine (decidable_equiv _
              (fun xp => inl_ne_inr (xp.1) b xp.2)^-1 _).
Defined.

Global Instance ishprop_hfiber_inr {A B : Type} (z : A + B)
: IsHProp (hfiber inr z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (trunc_equiv _
              (fun xp => inr_ne_inl (xp.1) a xp.2)^-1).
  - refine (trunc_equiv' _
              (equiv_functor_sigma' (equiv_idmap B)
                 (fun x => equiv_path_sum (inr x) (inr b)))).
Defined.

Global Instance decidable_hfiber_inr {A B : Type} (z : A + B)
: Decidable (hfiber inr z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (decidable_equiv _
              (fun xp => inr_ne_inl (xp.1) a xp.2)^-1 _).
  - refine (decidable_equiv' _
              (equiv_functor_sigma' (equiv_idmap B)
                 (fun x => equiv_path_sum (inr x) (inr b))) _).
Defined.

(** ** Transport *)

Definition transport_sum {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
           (z : P a + Q a)
: transport (fun a => P a + Q a) p z = match z with
                                         | inl z' => inl (p # z')
                                         | inr z' => inr (p # z')
                                       end
  := match p with idpath => match z with inl _ => 1 | inr _ => 1 end end.

(** ** Detecting the summands *)

Definition is_inl_and {A B} (P : A -> Type) : A + B -> Type
  := fun x => match x with inl a => P a | inr _ => Empty end.

Definition is_inr_and {A B} (P : B -> Type) : A + B -> Type
  := fun x => match x with inl _ => Empty | inr b => P b end.

Definition is_inl {A B} : A + B -> Type
  := is_inl_and (fun _ => Unit).

Definition is_inr {A B} : A + B -> Type
  := is_inr_and (fun _ => Unit).

Definition un_inl {A B} (z : A + B)
: is_inl z -> A.
Proof.
  destruct z as [a|b].
  - intros; exact a.
  - intros e; elim e.
Defined.

Definition un_inr {A B} (z : A + B)
: is_inr z -> B.
Proof.
  destruct z as [a|b].
  - intros e; elim e.
  - intros; exact b.
Defined.

Definition un_inl_inl {A B : Type} (a : A) (w : is_inl (inl a))
: un_inl (@inl A B a) w = a
  := 1.

Definition un_inr_inr {A B : Type} (b : B) (w : is_inr (inr b))
: un_inr (@inr A B b) w = b
  := 1.

Definition inl_un_inl {A B : Type} (z : A + B) (w : is_inl z)
: inl (un_inl z w) = z.
Proof.
  destruct z as [a|b]; simpl.
  - reflexivity.
  - elim w.
Defined.

Definition inr_un_inr {A B : Type} (z : A + B) (w : is_inr z)
: inr (un_inr z w) = z.
Proof.
  destruct z as [a|b]; simpl.
  - elim w.
  - reflexivity.
Defined.

Definition not_is_inl_and_inr {A B} (P : A -> Type) (Q : B -> Type)
           (x : A + B)
: is_inl_and P x -> is_inr_and Q x -> Empty.
Proof.
  destruct x as [a|b]; simpl.
  - exact (fun _ e => e).
  - exact (fun e _ => e).
Defined.

Definition not_is_inl_and_inr' {A B} (x : A + B)
: is_inl x -> is_inr x -> Empty
  := not_is_inl_and_inr (fun _ => Unit) (fun _ => Unit) x.

Definition is_inl_or_is_inr {A B} (x : A + B)
: (is_inl x) + (is_inr x)
  := match x return (is_inl x) + (is_inr x) with
       | inl _ => inl tt
       | inr _ => inr tt
     end.

Definition is_inl_ind {A B : Type} (P : A + B -> Type)
           (f : forall a:A, P (inl a))
: forall (x:A+B), is_inl x -> P x.
Proof.
  intros [a|b] H; [ exact (f a) | elim H ].
Defined.

Definition is_inr_ind {A B : Type} (P : A + B -> Type)
           (f : forall b:B, P (inr b))
: forall (x:A+B), is_inr x -> P x.
Proof.
  intros [a|b] H; [ elim H | exact (f b) ].
Defined.

(** ** Functorial action *)

Definition functor_sum {A A' B B' : Type} (f : A -> A') (g : B -> B')
: A + B -> A' + B'
  := fun z => match z with inl z' => inl (f z') | inr z' => inr (g z') end.

(** ** Unfunctorial action *)

Definition unfunctor_sum_l {A A' B B' : Type} (h : A + B -> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
: A -> A'
  := fun a => un_inl (h (inl a)) (Ha a).

Definition unfunctor_sum_r {A A' B B' : Type} (h : A + B -> A' + B')
           (Hb : forall b:B, is_inr (h (inr b)))
: B -> B'
  := fun b => un_inr (h (inr b)) (Hb b).

Definition unfunctor_sum_eta {A A' B B' : Type} (h : A + B -> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: functor_sum (unfunctor_sum_l h Ha) (unfunctor_sum_r h Hb) == h.
Proof.
  intros [a|b]; simpl.
  - unfold unfunctor_sum_l; apply inl_un_inl.
  - unfold unfunctor_sum_r; apply inr_un_inr.
Defined.

Definition unfunctor_sum_l_beta {A A' B B' : Type} (h : A + B -> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
: inl o unfunctor_sum_l h Ha == h o inl.
Proof.
  intros a; unfold unfunctor_sum_l; apply inl_un_inl.
Defined.

Definition unfunctor_sum_r_beta {A A' B B' : Type} (h : A + B -> A' + B')
           (Hb : forall b:B, is_inr (h (inr b)))
: inr o unfunctor_sum_r h Hb == h o inr.
Proof.
  intros b; unfold unfunctor_sum_r; apply inr_un_inr.
Defined.

Definition unfunctor_sum_l_compose {A A' A'' B B' B'' : Type}
           (h : A + B -> A' + B') (k : A' + B' -> A'' + B'')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Ha' : forall a':A', is_inl (k (inl a')))
: unfunctor_sum_l k Ha' o unfunctor_sum_l h Ha
  == unfunctor_sum_l (k o h)
     (fun a => is_inl_ind (fun x' => is_inl (k x')) Ha' (h (inl a)) (Ha a)).
Proof.
  intros a.
  refine (path_sum_inl B'' _).
  refine (unfunctor_sum_l_beta _ _ _ @ _).
  refine (ap k (unfunctor_sum_l_beta _ _ _) @ _).
  refine ((unfunctor_sum_l_beta _ _ _)^).
Defined.

Definition unfunctor_sum_r_compose {A A' A'' B B' B'' : Type}
           (h : A + B -> A' + B') (k : A' + B' -> A'' + B'')
           (Hb : forall b:B, is_inr (h (inr b)))
           (Hb' : forall b':B', is_inr (k (inr b')))
: unfunctor_sum_r k Hb' o unfunctor_sum_r h Hb
  == unfunctor_sum_r (k o h)
     (fun b => is_inr_ind (fun x' => is_inr (k x')) Hb' (h (inr b)) (Hb b)).
Proof.
  intros b.
  refine (path_sum_inr A'' _).
  refine (unfunctor_sum_r_beta _ _ _ @ _).
  refine (ap k (unfunctor_sum_r_beta _ _ _) @ _).
  refine ((unfunctor_sum_r_beta _ _ _)^).
Defined.

(** ** Functoriality on equivalences *)

Global Instance isequiv_functor_sum `{IsEquiv A A' f} `{IsEquiv B B' g}
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
  := BuildEquiv _ _ (functor_sum f g) _.

Definition equiv_functor_sum' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
: A + B <~> A' + B'
  := equiv_functor_sum (f := f) (g := g).

Definition equiv_functor_sum_l {A B B' : Type} (g : B <~> B')
: A + B <~> A + B'
  := equiv_functor_sum (f := idmap) (g := g).

Definition equiv_functor_sum_r {A A' B : Type} (f : A <~> A')
: A + B <~> A' + B
  := equiv_functor_sum (f := f) (g := idmap).

(** ** Unfunctoriality on equivalences *)

Definition isequiv_unfunctor_sum_l {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: IsEquiv (unfunctor_sum_l h Ha).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  - refine (unfunctor_sum_l h^-1 _); intros a'.
    remember (h^-1 (inl a')) as x eqn:p.
    destruct x as [a|b].
    + exact tt.
    + apply moveL_equiv_M in p.
      elim (p^ # (Hb b)).
  - intros a'.
    refine (unfunctor_sum_l_compose _ _ _ _ _ @ _).
    refine (path_sum_inl B' _).
    refine (unfunctor_sum_l_beta _ _ _ @ _).
    apply eisretr.
  - intros a.
    refine (unfunctor_sum_l_compose _ _ _ _ _ @ _).
    refine (path_sum_inl B _).
    refine (unfunctor_sum_l_beta (h^-1 o h) _ a @ _).
    apply eissect.
Defined.

Definition equiv_unfunctor_sum_l {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: A <~> A'
  := BuildEquiv _ _ (unfunctor_sum_l h Ha)
                (isequiv_unfunctor_sum_l h Ha Hb).

Definition isequiv_unfunctor_sum_r {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: IsEquiv (unfunctor_sum_r h Hb).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  - refine (unfunctor_sum_r h^-1 _); intros b'.
    remember (h^-1 (inr b')) as x eqn:p.
    destruct x as [a|b].
    + apply moveL_equiv_M in p.
      elim (p^ # (Ha a)).
    + exact tt.
  - intros b'.
    refine (unfunctor_sum_r_compose _ _ _ _ _ @ _).
    refine (path_sum_inr A' _).
    refine (unfunctor_sum_r_beta _ _ _ @ _).
    apply eisretr.
  - intros b.
    refine (unfunctor_sum_r_compose _ _ _ _ _ @ _).
    refine (path_sum_inr A _).
    refine (unfunctor_sum_r_beta (h^-1 o h) _ b @ _).
    apply eissect.
Defined.

Definition equiv_unfunctor_sum_r {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: B <~> B'
  := BuildEquiv _ _ (unfunctor_sum_r h Hb)
                (isequiv_unfunctor_sum_r h Ha Hb).

(** ** Symmetry *)

(* This is a special property of [sum], of course, not an instance of a general family of facts about types. *)

Definition equiv_sum_symm (A B : Type) : A + B <~> B + A.
Proof.
  apply (equiv_adjointify
           (fun ab => match ab with inl a => inr a | inr b => inl b end)
           (fun ab => match ab with inl a => inr a | inr b => inl b end));
  intros [?|?]; exact idpath.
Defined.

(** ** Associativity *)

Definition equiv_sum_assoc (A B C : Type) : (A + B) + C <~> A + (B + C).
Proof.
  refine (equiv_adjointify _ _ _ _).
  - intros [[a|b]|c];
    [ exact (inl a) | exact (inr (inl b)) | exact (inr (inr c)) ].
  - intros [a|[b|c]];
    [ exact (inl (inl a)) | exact (inl (inr b)) | exact (inr c) ].
  - intros [a|[b|c]]; reflexivity.
  - intros [[a|b]|c]; reflexivity.
Defined.

(** ** Identity *)

Definition sum_empty_l (A : Type) : Empty + A <~> A.
Proof.
  refine (equiv_adjointify
       (fun z => match z:Empty+A with
                   | inl e => match e with end
                   | inr a => a
                 end)
       inr (fun a => 1) _).
  intros [e|z]; [ elim e | reflexivity ].
Defined.

Definition sum_empty_r (A : Type) : A + Empty <~> A.
Proof.
  refine (equiv_adjointify
       (fun z => match z:A+Empty with
                   | inr e => match e with end
                   | inl a => a
                 end)
       inl (fun a => 1) _).
  intros [z|e]; [ reflexivity | elim e ].
Defined.

(** ** Distributivity *)

Definition sum_distrib_l A B C
: A * (B + C) <~> (A * B) + (A * C).
Proof.
  refine (BuildEquiv (A * (B + C)) ((A * B) + (A * C))
            (fun abc => let (a,bc) := abc in
                        match bc with
                          | inl b => inl (a,b)
                          | inr c => inr (a,c)
                        end) _).
  refine (BuildIsEquiv (A * (B + C)) ((A * B) + (A * C)) _
            (fun ax => match ax with
                         | inl (a,b) => (a,inl b)
                         | inr (a,c) => (a,inr c)
                       end) _ _ _).
  - intros [[a b]|[a c]]; reflexivity.
  - intros [a [b|c]]; reflexivity.
  - intros [a [b|c]]; reflexivity.
Defined.

Definition sum_distrib_r A B C
: (B + C) * A <~> (B * A) + (C * A).
Proof.
  refine (BuildEquiv ((B + C) * A) ((B * A) + (C * A))
            (fun abc => let (bc,a) := abc in
                        match bc with
                          | inl b => inl (b,a)
                          | inr c => inr (c,a)
                        end) _).
  refine (BuildIsEquiv ((B + C) * A) ((B * A) + (C * A)) _
            (fun ax => match ax with
                         | inl (b,a) => (inl b,a)
                         | inr (c,a) => (inr c,a)
                       end) _ _ _).
  - intros [[b a]|[c a]]; reflexivity.
  - intros [[b|c] a]; reflexivity.
  - intros [[b|c] a]; reflexivity.
Defined.

(** ** Sigmas over sums (extensivity) *)

Definition equiv_sigma_sum A B (C : A + B -> Type)
: { x : A+B & C x } <~>
  { a : A & C (inl a) } + { b : B & C (inr b) }.
Proof.
  refine (BuildEquiv { x : A+B & C x }
                     ({ a : A & C (inl a) } + { b : B & C (inr b) })
           (fun xc => let (x,c) := xc in
                      match x return
                            C x -> ({ a : A & C (inl a) } + { b : B & C (inr b) })
                      with
                        | inl a => fun c => inl (a;c)
                        | inr b => fun c => inr (b;c)
                      end c) _).
  refine (BuildIsEquiv { x : A+B & C x }
                       ({ a : A & C (inl a) } + { b : B & C (inr b) }) _
           (fun abc => match abc with
                         | inl (a;c) => (inl a ; c)
                         | inr (b;c) => (inr b ; c)
                       end) _ _ _).
  - intros [[a c]|[b c]]; reflexivity.
  - intros [[a|b] c]; reflexivity.
  - intros [[a|b] c]; reflexivity.
Defined.

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions. *)

Definition sum_ind_uncurried {A B} (P : A + B -> Type)
           (fg : (forall a, P (inl a)) * (forall b, P (inr b)))
: forall s, P s
  := @sum_ind A B P (fst fg) (snd fg).

(* First the positive universal property.
   Doing this sort of thing without adjointifying will require very careful use of funext. *)
Global Instance isequiv_sum_ind `{Funext} `(P : A + B -> Type)
: IsEquiv (sum_ind_uncurried P) | 0.
Proof.
  apply (isequiv_adjointify
           (sum_ind_uncurried P)
           (fun f => (fun a => f (inl a), fun b => f (inr b))));
  repeat ((exact idpath)
            || intros []
            || intro
            || apply path_forall).
Defined.

Definition equiv_sum_ind `{Funext} `(P : A + B -> Type)
  := BuildEquiv _ _ _ (isequiv_sum_ind P).

(* The non-dependent version, which is a special case, is the sum-distributive equivalence. *)
Definition equiv_sum_distributive `{Funext} (A B C : Type)
: (A -> C) * (B -> C) <~> (A + B -> C)
  := equiv_sum_ind (fun _ => C).

(** ** Sums preserve most truncation *)

Global Instance trunc_sum n' (n := n'.+2)
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

Global Instance hset_sum `{HA : IsHSet A, HB : IsHSet B} : IsHSet (A + B) | 100
  := @trunc_sum -2 A HA B HB.

(** Sums don't preserve hprops in general, but they do for disjoint sums. *)

Definition ishprop_sum A B `{IsHProp A} `{IsHProp B}
: (A -> B -> Empty) -> IsHProp (A + B).
Proof.
  intros H.
  apply hprop_allpath; intros [a1|b1] [a2|b2].
  - apply ap, path_ishprop.
  - case (H a1 b2).
  - case (H a2 b1).
  - apply ap, path_ishprop.
Defined.

(** ** Decidability *)

(** Sums preserve decidability *)
Global Instance decidable_sum {A B : Type}
       `{Decidable A} `{Decidable B}
: Decidable (A + B).
Proof.
  destruct (dec A) as [x1|y1].
  - exact (inl (inl x1)).
  - destruct (dec B) as [x2|y2].
    + exact (inl (inr x2)).
    + apply inr; intros z.
      destruct z as [x1|x2].
      * exact (y1 x1).
      * exact (y2 x2).
Defined.

(** Sums preserve decidable paths *)
Global Instance decidablepaths_sum {A B}
       `{DecidablePaths A} `{DecidablePaths B}
: DecidablePaths (A + B).
Proof.
  intros [a1|b1] [a2|b2].
  - destruct (dec_paths a1 a2) as [p|np].
    + exact (inl (ap inl p)).
    + apply inr; intros p.
      exact (np ((path_sum _ _)^-1 p)).
  - exact (inr (path_sum _ _)^-1).
  - exact (inr (path_sum _ _)^-1).
  - destruct (dec_paths b1 b2) as [p|np].
    + exact (inl (ap inr p)).
    + apply inr; intros p.
      exact (np ((path_sum _ _)^-1 p)).
Defined.

(** Because of [ishprop_sum], decidability of an hprop is again an hprop. *)
Global Instance ishprop_decidable_hprop `{Funext} A `{IsHProp A}
: IsHProp (Decidable A).
Proof.
  unfold Decidable; refine (ishprop_sum _ _ _).
  intros a na; exact (na a).
Defined.

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

Global Instance isequiv_sigT_of_sum A B : IsEquiv (@sigT_of_sum A B) | 0.
Proof.
  apply (isequiv_adjointify (@sigT_of_sum A B)
                            (@sum_of_sigT A B));
  repeat (intros [] || intro); exact idpath.
Defined.

Global Instance isequiv_sum_of_sigT A B : IsEquiv (sum_of_sigT A B)
  := isequiv_inverse (@sigT_of_sum A B).

(** An alternative way of proving the truncation property of [sum]. *)
Definition trunc_sum' n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B}
: (IsTrunc n (A + B)).
Proof.
  eapply trunc_equiv'; [ esplit;
                         exact (@isequiv_sum_of_sigT _ _)
                       | ].
  typeclasses eauto.
Defined.
