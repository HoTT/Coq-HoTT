(** * Theorems about disjoint unions *)

Require Import HoTT.Basics.
Require Import Types.Empty Types.Unit Types.Prod Types.Sigma.
(** The following are only required for the equivalence between [sum] and a sigma type *)
Require Import Types.Bool.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

Local Set Universe Minimization ToSet.

Generalizable Variables X A B f g n.

Scheme sum_ind := Induction for sum Sort Type.
Arguments sum_ind {A B} P f g s : rename.

Scheme sum_rec := Minimality for sum Sort Type.
Arguments sum_rec {A B} P f g s : rename.

(** ** CoUnpacking *)

(** Sums are coproducts, so there should be a dual to [unpack_prod].  I'm not sure what it is, though. *)

(** ** Eta conversion *)

Definition eta_sum `(z : A + B) : match z with
                                    | inl z' => inl z'
                                    | inr z' => inr z'
                                  end = z
  := match z with inl _ => 1 | inr _ => 1 end.

(** ** Paths *)

Definition code_sum {A B} (z z' : A + B) : Type
  := match z, z' with
    | inl a, inl a' => a = a'
    | inr b, inr b' => b = b'
    | _, _ => Empty end.

Definition path_sum {A B : Type} {z z' : A + B} (c : code_sum z z') : z = z'.
Proof.
  destruct z, z'.
  - apply ap, c.
  - elim c.
  - elim c.
  - apply ap, c.
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
  : path_sum o (@path_sum_inv _ _ z z') == idmap
  := fun p => match p as p in (_ = z') return
                    path_sum (path_sum_inv p) = p
              with
                | 1 => match z as z return
                             (@path_sum _ _ z z) (path_sum_inv 1) = 1
                       with
                         | inl _ => 1
                         | inr _ => 1
                       end
              end.

Definition eissect_path_sum {A B} {z z' : A + B}
  : path_sum_inv o (@path_sum _ _ z z') == idmap.
Proof.
  intro p.
  destruct z, z', p; exact idpath.
Defined.

Global Instance isequiv_path_sum {A B : Type} {z z' : A + B}
: IsEquiv (@path_sum _ _ z z') | 0.
Proof.
  refine (Build_IsEquiv _ _ path_sum path_sum_inv
    eisretr_path_sum eissect_path_sum _).
  destruct z, z';
  intros [];
  exact idpath.
Defined.

Definition equiv_path_sum {A B : Type} (z z' : A + B)
  := Build_Equiv _ _ _ (@isequiv_path_sum A B z z').

(** ** Fibers of [inl] and [inr] *)

(** It follows that the fibers of [inl] and [inr] are decidable hprops. *)

Global Instance ishprop_hfiber_inl {A B : Type} (z : A + B)
: IsHProp (hfiber inl z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (istrunc_equiv_istrunc _
              (equiv_functor_sigma_id
                 (fun x => equiv_path_sum (inl x) (inl a)))).
  - refine (istrunc_isequiv_istrunc _
              (fun xp => inl_ne_inr (xp.1) b xp.2)^-1).
Defined.

Global Instance decidable_hfiber_inl {A B : Type} (z : A + B)
: Decidable (hfiber inl z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (decidable_equiv' _
              (equiv_functor_sigma_id
                 (fun x => equiv_path_sum (inl x) (inl a))) _).
  - refine (decidable_equiv _
              (fun xp => inl_ne_inr (xp.1) b xp.2)^-1 _).
Defined.

Global Instance ishprop_hfiber_inr {A B : Type} (z : A + B)
: IsHProp (hfiber inr z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (istrunc_isequiv_istrunc _
              (fun xp => inr_ne_inl (xp.1) a xp.2)^-1).
  - refine (istrunc_equiv_istrunc _
              (equiv_functor_sigma_id
                 (fun x => equiv_path_sum (inr x) (inr b)))).
Defined.

Global Instance decidable_hfiber_inr {A B : Type} (z : A + B)
: Decidable (hfiber inr z).
Proof.
  destruct z as [a|b]; unfold hfiber.
  - refine (decidable_equiv _
              (fun xp => inr_ne_inl (xp.1) a xp.2)^-1 _).
  - refine (decidable_equiv' _
              (equiv_functor_sigma_id
                 (fun x => equiv_path_sum (inr x) (inr b))) _).
Defined.

(** ** Decomposition *)

(** Conversely, a decidable predicate decomposes a type as a sum. *)

Section DecidableSum.
  Context `{Funext} {A : Type} (P : A -> Type)
          `{forall a, IsHProp (P a)} `{forall a, Decidable (P a)}.

  Definition equiv_decidable_sum
    : A <~> {x:A & P x} + {x:A & ~(P x)}.
  Proof.
    transparent assert (f : (A -> {x:A & P x} + {x:A & ~(P x)})).
    { intros x.
      destruct (dec (P x)) as [p|np].
      - exact (inl (x;p)).
      - exact (inr (x;np)). }
    refine (Build_Equiv _ _ f _).
    refine (isequiv_adjointify
              _ (fun z => match z with
                          | inl (x;p) => x
                          | inr (x;np) => x
                          end) _ _).
    - intros [[x p]|[x np]]; unfold f;
        destruct (dec (P x)) as [p'|np'].
      + apply ap, ap, path_ishprop.
      + elim (np' p).
      + elim (np p').
      + apply ap, ap, path_ishprop.
    - intros x; unfold f.
      destruct (dec (P x)); cbn; reflexivity.
  Defined.

  Definition equiv_decidable_sum_l (a : A) (p : P a)
    : equiv_decidable_sum a = inl (a;p).
  Proof.
    unfold equiv_decidable_sum; cbn.
    destruct (dec (P a)) as [p'|np'].
    - apply ap, path_sigma_hprop; reflexivity.
    - elim (np' p).
  Defined.

  Definition equiv_decidable_sum_r (a : A) (np : ~ (P a))
    : equiv_decidable_sum a = inr (a;np).
  Proof.
    unfold equiv_decidable_sum; cbn.
    destruct (dec (P a)) as [p'|np'].
    - elim (np p').
    - apply ap, path_sigma_hprop; reflexivity.
  Defined.

End DecidableSum.

(** ** Transport *)

Definition transport_sum {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
           (z : P a + Q a)
: transport (fun a => P a + Q a) p z = match z with
                                         | inl z' => inl (p # z')
                                         | inr z' => inr (p # z')
                                       end
  := match p with idpath => match z with inl _ => 1 | inr _ => 1 end end.

(** ** Detecting the summands *)

Definition is_inl_and {A B} (P : A -> Type@{p}) : A + B -> Type@{p}
  := fun x => match x with inl a => P a | inr _ => Empty end.

Definition is_inr_and {A B} (P : B -> Type@{p}) : A + B -> Type@{p}
  := fun x => match x with inl _ => Empty | inr b => P b end.

Definition is_inl {A B} : A + B -> Type0
  := is_inl_and (fun _ => Unit).

Definition is_inr {A B} : A + B -> Type0
  := is_inr_and (fun _ => Unit).

Global Instance ishprop_is_inl {A B} (x : A + B)
: IsHProp (is_inl x).
Proof.
  destruct x; exact _.
Defined.

Global Instance ishprop_is_inr {A B} (x : A + B)
: IsHProp (is_inr x).
Proof.
  destruct x; exact _.
Defined.

Global Instance decidable_is_inl {A B} (x : A + B)
: Decidable (is_inl x).
Proof.
  destruct x; exact _.
Defined.

Global Instance decidable_is_inr {A B} (x : A + B)
: Decidable (is_inr x).
Proof.
  destruct x; exact _.
Defined.

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

Definition is_inl_not_inr {A B} (x : A + B)  (na : ~ A)
: is_inr x
  := match x with
     | inl a => na a
     | inr b => tt
     end.

Definition is_inr_not_inl {A B} (x : A + B)  (nb : ~ B)
: is_inl x
  := match x with
     | inl a => tt
     | inr b => nb b
     end.

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

Section FunctorSum.
  Context {A A' B B' : Type} (f : A -> A') (g : B -> B').

  Definition functor_sum : A + B -> A' + B'
    := fun z => match z with inl z' => inl (f z') | inr z' => inr (g z') end.

  Definition functor_code_sum {z z' : A + B} (c : code_sum z z')
    : code_sum (functor_sum z) (functor_sum z').
  Proof.
    destruct z, z'.
    - destruct c. reflexivity.
    - elim c.
    - elim c.
    - destruct c. reflexivity.
  Defined.

  Definition ap_functor_sum {z z' : A + B} (c : code_sum z z')
    : ap functor_sum (path_sum c) = path_sum (functor_code_sum c).
  Proof.
    destruct z, z'.
    - destruct c. reflexivity.
    - elim c.
    - elim c.
    - destruct c. reflexivity.
  Defined.

  (** The fibers of [functor_sum] are those of [f] and [g]. *)
  Definition hfiber_functor_sum_l (a' : A')
  : hfiber functor_sum (inl a') <~> hfiber f a'.
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    - intros [[a|b] p].
      + exists a.
        exact (path_sum_inl _ p).
      + elim (inr_ne_inl _ _ p).
    - intros [a p].
      exists (inl a).
      exact (ap inl p).
    - intros [a p].
      apply ap.
      (** Why doesn't Coq find this? *)
      pose (@isequiv_path_sum A' B' (inl (f a)) (inl a')).
      exact (eissect (@path_sum A' B' (inl (f a)) (inl a')) p).
    - intros [[a|b] p]; simpl.
      + apply ap.
        pose (@isequiv_path_sum A' B' (inl (f a)) (inl a')).
        exact (eisretr (@path_sum A' B' (inl (f a)) (inl a')) p).
      + elim (inr_ne_inl _ _ p).
  Defined.

  Definition hfiber_functor_sum_r (b' : B')
  : hfiber functor_sum (inr b') <~> hfiber g b'.
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    - intros [[a|b] p].
      + elim (inl_ne_inr _ _ p).
      + exists b.
        exact (path_sum_inr _ p).
    - intros [b p].
      exists (inr b).
      exact (ap inr p).
    - intros [b p].
      apply ap.
      (** Why doesn't Coq find this? *)
      pose (@isequiv_path_sum A' B' (inr (g b)) (inr b')).
      exact (eissect (@path_sum A' B' (inr (g b)) (inr b')) p).
    - intros [[a|b] p]; simpl.
      + elim (inl_ne_inr _ _ p).
      + apply ap.
        pose (@isequiv_path_sum A' B' (inr (g b)) (inr b')).
        exact (eisretr (@path_sum A' B' (inr (g b)) (inr b')) p).
  Defined.

End FunctorSum.

Definition functor_sum_homotopic {A A' B B' : Type}
  {f f' : A -> A'} {g g' : B -> B'} (p : f == f') (q : g == g')
  : functor_sum f g == functor_sum f' g'.
Proof.
  intros [a|b].
  - exact (ap inl (p a)).
  - exact (ap inr (q b)).
Defined.

Definition functor_sum_compose {A A' A'' B B' B'' : Type}
  {f : A -> A'} {f' : A' -> A''} {g : B -> B'} {g' : B' -> B''}
  : functor_sum (f' o f) (g' o g) == functor_sum f' g' o functor_sum f g.
Proof.
  intros [a|b]; reflexivity.
Defined.

Definition functor_sum_idmap {A B : Type}
  : functor_sum (A:=A) (B:=B) idmap idmap == idmap.
Proof.
  intros [a|b]; reflexivity.
Defined.

(** ** "Unfunctorial action" *)

(** Not every function [A + B -> A' + B'] is of the form [functor_sum f g].  However, this is the case if it preserves the summands, i.e. if it maps [A] into [A'] and [B] into [B'].  More generally, if a function [A + B -> A' + B'] maps [A] into [A'] only, then we can extract from it a function [A -> A'].  Since these operations are a sort of inverse to [functor_sum], we call them [unfunctor_sum_*]. *)

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

(** [unfunctor_sum] also preserves fibers, if both summands are preserved. *)
Definition hfiber_unfunctor_sum_l {A A' B B' : Type}
           (h : A + B -> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
           (a' : A')
: hfiber (unfunctor_sum_l h Ha) a' <~> hfiber h (inl a').
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [a p].
    exists (inl a).
    refine (_ @ ap inl p).
    symmetry; apply inl_un_inl.
  - intros [[a|b] p].
    + exists a.
      apply path_sum_inl with B'.
      refine (_ @ p).
      apply inl_un_inl.
    + specialize (Hb b).
      abstract (rewrite p in Hb; elim Hb).
  - intros [[a|b] p]; simpl.
    + apply ap.
      apply moveR_Vp.
      exact (eisretr (@path_sum A' B' _ _)
                     (inl_un_inl (h (inl a)) (Ha a) @ p)).
    + apply Empty_rec.
      specialize (Hb b).
      abstract (rewrite p in Hb; elim Hb).
  - intros [a p].
    apply ap.
    rewrite concat_p_Vp.
    pose (@isequiv_path_sum
            A' B' (inl (unfunctor_sum_l h Ha a)) (inl a')).
    exact (eissect (@path_sum A' B' (inl (unfunctor_sum_l h Ha a)) (inl a')) p).
Defined.

Definition hfiber_unfunctor_sum_r {A A' B B' : Type}
           (h : A + B -> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
           (b' : B')
: hfiber (unfunctor_sum_r h Hb) b' <~> hfiber h (inr b').
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [b p].
    exists (inr b).
    refine (_ @ ap inr p).
    symmetry; apply inr_un_inr.
  - intros [[a|b] p].
    + specialize (Ha a).
      abstract (rewrite p in Ha; elim Ha).
    + exists b.
      apply path_sum_inr with A'.
      refine (_ @ p).
      apply inr_un_inr.
  - intros [[a|b] p]; simpl.
    + apply Empty_rec.
      specialize (Ha a).
      abstract (rewrite p in Ha; elim Ha).
    + apply ap.
      apply moveR_Vp.
      exact (eisretr (@path_sum A' B' _ _)
                     (inr_un_inr (h (inr b)) (Hb b) @ p)).
  - intros [b p].
    apply ap.
    rewrite concat_p_Vp.
    pose (@isequiv_path_sum
            A' B' (inr (unfunctor_sum_r h Hb b)) (inr b')).
    exact (eissect (@path_sum A' B' (inr (unfunctor_sum_r h Hb b)) (inr b')) p).
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
  := Build_Equiv _ _ (functor_sum f g) _.

Definition equiv_functor_sum' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
: A + B <~> A' + B'
  := equiv_functor_sum (f := f) (g := g).

Notation "f +E g" := (equiv_functor_sum' f g) : equiv_scope.

Definition equiv_functor_sum_l {A B B' : Type} (g : B <~> B')
: A + B <~> A + B'
  := 1 +E g.

Definition equiv_functor_sum_r {A A' B : Type} (f : A <~> A')
: A + B <~> A' + B
  := f +E 1.

Definition iff_functor_sum {A A' B B' : Type} (f : A <-> A') (g : B <-> B')
  : A + B <-> A' + B'
  := (functor_sum (fst f) (fst g), functor_sum (snd f) (snd g)).

(** ** Unfunctoriality on equivalences *)

Global Instance isequiv_unfunctor_sum_l {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: IsEquiv (unfunctor_sum_l h Ha).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
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
  := Build_Equiv _ _ (unfunctor_sum_l h Ha)
                (isequiv_unfunctor_sum_l h Ha Hb).

Global Instance isequiv_unfunctor_sum_r {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: IsEquiv (unfunctor_sum_r h Hb).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
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
  := Build_Equiv _ _ (unfunctor_sum_r h Hb)
                (isequiv_unfunctor_sum_r h Ha Hb).

Definition equiv_unfunctor_sum {A A' B B' : Type}
           (h : A + B <~> A' + B')
           (Ha : forall a:A, is_inl (h (inl a)))
           (Hb : forall b:B, is_inr (h (inr b)))
: (A <~> A') * (B <~> B')
  := (equiv_unfunctor_sum_l h Ha Hb , equiv_unfunctor_sum_r h Ha Hb).

(** ** Symmetry *)

(* This is a special property of [sum], of course, not an instance of a general family of facts about types. *)

Definition equiv_sum_symm@{u v k | u <= k, v <= k} (A : Type@{u}) (B : Type@{v})
  : Equiv@{k k} (A + B) (B + A).
Proof.
  apply (equiv_adjointify
           (fun ab => match ab with inl a => inr a | inr b => inl b end)
           (fun ab => match ab with inl a => inr a | inr b => inl b end));
  intros [?|?]; exact idpath.
Defined.

(** ** Associativity *)

Definition equiv_sum_assoc (A B C : Type) : (A + B) + C <~> A + (B + C).
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [[a|b]|c];
    [ exact (inl a) | exact (inr (inl b)) | exact (inr (inr c)) ].
  - intros [a|[b|c]];
    [ exact (inl (inl a)) | exact (inl (inr b)) | exact (inr c) ].
  - intros [a|[b|c]]; reflexivity.
  - intros [[a|b]|c]; reflexivity.
Defined.

(** ** Identity *)

Definition sum_empty_l@{u|} (A : Type@{u}) : Equiv@{u u} (Empty + A) A.
Proof.
  snrapply equiv_adjointify@{u u}.
  - intros [e|a]; [ exact (Empty_rec@{u} e) | exact a ].
  - intros a; exact (inr@{Set u} a).
  - intro x; exact idpath@{u}.
  - intros [e|z]; [ elim e | exact idpath@{u}].
Defined.

Definition sum_empty_r@{u} (A : Type@{u}) : Equiv@{u u} (A + Empty) A
  := equiv_compose'@{u u u} (sum_empty_l A) (equiv_sum_symm@{u Set u} _ _).

(** ** Distributivity *)

Definition sum_distrib_l A B C
: A * (B + C) <~> (A * B) + (A * C).
Proof.
  snrapply Build_Equiv.
  2: snrapply Build_IsEquiv.
  - intros [a [b|c]].
    + exact (inl@{u u} (a, b)).
    + exact (inr@{u u} (a, c)).
  - intros [[a b]|[a c]].
    + exact (a, inl@{u u} b).
    + exact (a, inr@{u u} c).
  - intros [[a b]|[a c]]; reflexivity.
  - intros [a [b|c]]; reflexivity.
  - intros [a [b|c]]; reflexivity.
Defined.

Definition sum_distrib_r A B C
: (B + C) * A <~> (B * A) + (C * A).
Proof.
  refine (Build_Equiv ((B + C) * A) ((B * A) + (C * A))
            (fun abc => let (bc,a) := abc in
                        match bc with
                          | inl b => inl (b,a)
                          | inr c => inr (c,a)
                        end) _).
  simple refine (Build_IsEquiv ((B + C) * A) ((B * A) + (C * A)) _
            (fun ax => match ax with
                         | inl (b,a) => (inl b,a)
                         | inr (c,a) => (inr c,a)
                       end) _ _ _).
  - intros [[b a]|[c a]]; reflexivity.
  - intros [[b|c] a]; reflexivity.
  - intros [[b|c] a]; reflexivity.
Defined.

(** ** Extensivity *)

(** We can phrase extensivity in two ways, using either dependent types or functions. *)

(** The first is a statement about types dependent on a sum type. *)
Definition equiv_sigma_sum A B (C : A + B -> Type)
: { x : A+B & C x } <~>
  { a : A & C (inl a) } + { b : B & C (inr b) }.
Proof.
  refine (Build_Equiv { x : A+B & C x }
                     ({ a : A & C (inl a) } + { b : B & C (inr b) })
           (fun xc => let (x,c) := xc in
                      match x return
                            C x -> ({ a : A & C (inl a) } + { b : B & C (inr b) })
                      with
                        | inl a => fun c => inl (a;c)
                        | inr b => fun c => inr (b;c)
                      end c) _).
  simple refine (Build_IsEquiv { x : A+B & C x }
                       ({ a : A & C (inl a) } + { b : B & C (inr b) }) _
           (fun abc => match abc with
                         | inl (a;c) => (inl a ; c)
                         | inr (b;c) => (inr b ; c)
                       end) _ _ _).
  - intros [[a c]|[b c]]; reflexivity.
  - intros [[a|b] c]; reflexivity.
  - intros [[a|b] c]; reflexivity.
Defined.

(** The second is a statement about functions into a sum type. *)
Definition decompose_l {A B C} (f : C -> A + B) : Type
  := { c:C & is_inl (f c) }.

Definition decompose_r {A B C} (f : C -> A + B) : Type
  := { c:C & is_inr (f c) }.

Definition equiv_decompose {A B C} (f : C -> A + B)
: decompose_l f + decompose_r f <~> C.
Proof.
  simple refine (equiv_adjointify (sum_ind (fun _ => C) pr1 pr1) _ _ _).
  - intros c; destruct (is_inl_or_is_inr (f c));
    [ left | right ]; exists c; assumption.
  - intros c; destruct (is_inl_or_is_inr (f c)); reflexivity.
  - intros [[c l]|[c r]]; simpl; destruct (is_inl_or_is_inr (f c)).
    + apply ap, ap, path_ishprop.
    + elim (not_is_inl_and_inr' _ l i).
    + elim (not_is_inl_and_inr' _ i r).
    + apply ap, ap, path_ishprop.
Defined.

Definition is_inl_decompose_l {A B C} (f : C -> A + B)
           (z : decompose_l f)
: is_inl (f (equiv_decompose f (inl z)))
  := z.2.

Definition is_inr_decompose_r {A B C} (f : C -> A + B)
           (z : decompose_r f)
: is_inr (f (equiv_decompose f (inr z)))
  := z.2.

(** ** Indecomposability *)

(** A type is indecomposable if whenever it maps into a finite sum, it lands entirely in one of the summands.  It suffices to assert this for binary and nullary sums; in the latter case it reduces to nonemptiness. *)
Class Indecomposable (X : Type) :=
  { indecompose : forall A B (f : X -> A + B),
                    (forall x, is_inl (f x)) + (forall x, is_inr (f x))
  ; indecompose0 : ~~X }.

(** For instance, contractible types are indecomposable. *)
Global Instance indecomposable_contr `{Contr X} : Indecomposable X.
Proof.
  constructor.
  - intros A B f.
    destruct (is_inl_or_is_inr (f (center X))); [ left | right ]; intros x.
    all:refine (transport _ (ap f (contr x)) _); assumption.
  - intros nx; exact (nx (center X)).
Defined.

(** In particular, if an indecomposable type is equivalent to a sum type, then one summand is empty and it is equivalent to the other. *)
Definition equiv_indecomposable_sum {X A B} `{Indecomposable X}
           (f : X <~> A + B)
: ((X <~> A) * (Empty <~> B)) + ((X <~> B) * (Empty <~> A)).
Proof.
  destruct (indecompose A B f) as [i|i]; [ left | right ].
  1:pose (g := (f oE sum_empty_r X)).
  2:pose (g := (f oE sum_empty_l X)).
  2:apply (equiv_prod_symm _ _).
  all:refine (equiv_unfunctor_sum g _ _); try assumption; try intros [].
Defined.

(** Summing with an indecomposable type is injective on equivalence classes of types. *)
Definition equiv_unfunctor_sum_indecomposable_ll {A B B' : Type}
           `{Indecomposable A} (h : A + B <~> A + B')
: B <~> B'.
Proof.
  pose (f := equiv_decompose (h o inl)).
  pose (g := equiv_decompose (h o inr)).
  pose (k := (h oE (f +E g))).
  (** This looks messy, but it just amounts to swapping the middle two summands in [k]. *)
  pose (k' := k
                oE (equiv_sum_assoc _ _ _)
                oE ((equiv_sum_assoc _ _ _)^-1 +E 1)
                oE (1 +E (equiv_sum_symm _ _) +E 1)
                oE ((equiv_sum_assoc _ _ _) +E 1)
                oE (equiv_sum_assoc _ _ _)^-1).
  destruct (equiv_unfunctor_sum k'
       (fun x : decompose_l (h o inl) + decompose_l (h o inr) =>
        match x as x0 return (is_inl (k' (inl x0))) with
        | inl x0 => x0.2
        | inr x0 => x0.2
        end)
       (fun x : decompose_r (h o inl) + decompose_r (h o inr) =>
        match x as x0 return (is_inr (k' (inr x0))) with
        | inl x0 => x0.2
        | inr x0 => x0.2
        end)) as [s t]; clear k k'.
  refine (t oE (_ +E 1) oE g^-1).
  destruct (equiv_indecomposable_sum s^-1) as [[p q]|[p q]];
  destruct (equiv_indecomposable_sum f^-1) as [[u v]|[u v]].
  - refine (v oE q^-1).
  - elim (indecompose0 (v^-1 o p)).
  - refine (Empty_rec (indecompose0 _)); intros a.
    destruct (is_inl_or_is_inr (h (inl a))) as [l|r].
    * exact (q^-1 (a;l)).
    * exact (v^-1 (a;r)).
  - refine (u oE p^-1).
Defined.

Definition equiv_unfunctor_sum_contr_ll {A A' B B' : Type}
           `{Contr A} `{Contr A'}
           (h : A + B <~> A' + B')
: B <~> B'
  := equiv_unfunctor_sum_indecomposable_ll
       ((equiv_contr_contr +E 1) oE h).

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
  := Build_Equiv _ _ _ (isequiv_sum_ind P).

(* The non-dependent version, which is a special case, is the sum-distributive equivalence. *)
Definition equiv_sum_distributive `{Funext} (A B C : Type)
: (A -> C) * (B -> C) <~> (A + B -> C)
  := equiv_sum_ind (fun _ => C).

(** ** Sums preserve most truncation *)

Global Instance istrunc_sum n' (n := n'.+2)
         `{IsTrunc n A, IsTrunc n B}
: IsTrunc n (A + B) | 100.
Proof.
  apply istrunc_S.
  intros a b.
  eapply istrunc_equiv_istrunc;
    [ exact (equiv_path_sum _ _) | ].
  destruct a, b; exact _.
Defined.

Global Instance ishset_sum `{HA : IsHSet A, HB : IsHSet B} : IsHSet (A + B) | 100
  := @istrunc_sum (-2) A HA B HB.

(** Sums don't preserve hprops in general, but they do for disjoint sums. *)

Global Instance ishprop_sum A B `{IsHProp A} `{IsHProp B}
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
Global Instance decidable_sum@{u v k | u <= k, v <= k} {A : Type@{u}} {B : Type@{v}}
  `{Decidable A} `{Decidable B}
  : Decidable@{k} (A + B).
Proof.
  destruct (dec A) as [x1|y1].
  - exact (inl@{k k} (inl x1)).
  - destruct (dec@{v} B) as [x2|y2].
    + exact (inl@{k k} (inr x2)).
    + apply inr@{k k}; intros z.
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
      exact (np (path_sum^-1 p)).
  - exact (inr path_sum^-1).
  - exact (inr path_sum^-1).
  - destruct (dec_paths b1 b2) as [p|np].
    + exact (inl (ap inr p)).
    + apply inr; intros p.
      exact (np (path_sum^-1 p)).
Defined.

(** Because of [ishprop_sum], decidability of an hprop is again an hprop. *)
Global Instance ishprop_decidable_hprop `{Funext} A `{IsHProp A}
: IsHProp (Decidable A).
Proof.
  unfold Decidable; refine (ishprop_sum _ _ _).
  intros a na; exact (na a).
Defined.

(** ** Binary coproducts are equivalent to dependent sigmas where the first component is a bool. *)

Definition sig_of_sum A B (x : A + B)
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

Definition sum_of_sig A B (x : { b : Bool & if b then A else B })
: A + B
  := match x with
       | (true; a) => inl a
       | (false; b) => inr b
     end.

Global Instance isequiv_sig_of_sum A B : IsEquiv (@sig_of_sum A B) | 0.
Proof.
  apply (isequiv_adjointify (@sig_of_sum A B)
                            (@sum_of_sig A B)).
  - intros [[] ?]; exact idpath.
  - intros []; exact idpath.
Defined.

Global Instance isequiv_sum_of_sig A B : IsEquiv (sum_of_sig A B)
  := isequiv_inverse (@sig_of_sum A B).

(** An alternative way of proving the truncation property of [sum]. *)
Definition trunc_sum' n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B}
: (IsTrunc n (A + B)).
Proof.
  eapply istrunc_equiv_istrunc; [ esplit;
                         exact (@isequiv_sum_of_sig _ _)
                       | ].
  typeclasses eauto.
Defined.
