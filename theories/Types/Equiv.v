Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall Types.Arrow Types.Paths.

Local Open Scope path_scope.

(** * Equivalences *)

(** ** [IsEquiv f] is logically equivalent to [IsTruncMap (-2) f] *)

Instance contr_map_isequiv {A B} (f : A -> B) `{IsEquiv _ _ f}
  : IsTruncMap (-2) f.
Proof.
  intros b; refine (contr_equiv' {a : A & a = f^-1 b} _).
  apply equiv_functor_sigma_id; intros a.
  apply equiv_moveR_equiv_M.
Defined.

Definition isequiv_contr_map {A B} (f : A -> B) `{IsTruncMap (-2) A B f}
  : IsEquiv f.
Proof.
  srapply Build_IsEquiv.
  - intros b; exact (center {a : A & f a = b}).1.
  - intros b. exact (center {a : A & f a = b}).2.
  - intros a. exact (@contr {x : A & f x = f a} _ (a;1))..1.
  - intros a; cbn. apply moveL_M1.
    lhs_V napply transport_paths_l.
    lhs_V napply transport_compose.
    exact ((@contr {x : A & f x = f a} _ (a;1))..2).
Defined.

(** As usual, we can't make both of these [Instances]. *)
#[export] Hint Immediate isequiv_contr_map : typeclass_instances.

(** It follows that when proving a map is an equivalence, we may assume its codomain is inhabited. *)
Definition isequiv_inhab_codomain {A B} (f : A -> B) (feq : B -> IsEquiv f)
  : IsEquiv f.
Proof.
  apply isequiv_contr_map.
  intros b.
  pose (feq b); exact _.
Defined.

(** If [functor_sigma idmap g] is an equivalence then so is g. *)
Definition isequiv_from_functor_sigma {A} (P Q : A -> Type)
  (g : forall a, P a -> Q a) `{!IsEquiv (functor_sigma idmap g)}
  : forall (a : A), IsEquiv (g a).
Proof.
  intros a; apply isequiv_contr_map.
  apply istruncmap_from_functor_sigma.
  exact _.
Defined.

(** Theorem 4.7.7: [functor_sigma idmap g] is an equivalence if and only if g is. *)
Definition equiv_total_iff_equiv_fiberwise {A} (P Q : A -> Type)
  (g : forall a, P a -> Q a)
  : IsEquiv (functor_sigma idmap g) <-> forall a, IsEquiv (g a).
Proof.
  split.
  - apply isequiv_from_functor_sigma.
  - intro K. exact isequiv_functor_sigma.
Defined.

(** ** Assuming [Funext], [IsEquiv f] is an hprop, which has further consequences *)

Section AssumeFunext.
  Context `{Funext}.

  #[export] Instance contr_sect_equiv {A B} (f : A -> B) `{IsEquiv A B f}
    : Contr {g : B -> A & f o g == idmap}.
  Proof.
    refine (contr_change_center (f^-1 ; eisretr f)).
    refine (contr_equiv' { g : B -> A & f o g = idmap } _).
    (* Typeclass inference finds this contractible instance: it's the fiber over [idmap] of postcomposition with [f], and the latter is an equivalence since [f] is. *)
    apply equiv_functor_sigma_id; intros g.
    apply equiv_ap10.
  Defined.

  #[export] Instance contr_retr_equiv {A B} (f : A -> B) `{IsEquiv A B f}
    : Contr {g : B -> A & g o f == idmap}.
  Proof.
    refine (contr_change_center (f^-1 ; eissect f)).
    refine (contr_equiv' { g : B -> A & g o f = idmap } _).
    apply equiv_functor_sigma_id; intros g.
    apply equiv_ap10.
  Defined.

  #[export] Instance hprop_isequiv {A B} (f : A -> B)
    : IsHProp (IsEquiv f).
  Proof.
    (* We will show that assuming [f] is an equivalence, [IsEquiv f] decomposes into a sigma of two contractible types. *)
    apply hprop_inhabited_contr; intros feq.
    nrefine (contr_equiv' _ (issig_isequiv f oE (equiv_sigma_assoc' _ _)^-1)).
    srefine (contr_equiv' _ (equiv_contr_sigma _)^-1).
    (* Each of these types is equivalent to a based homotopy space.  The first is exactly [contr_sect_equiv]. *)
    1: rapply contr_sect_equiv.
    (* The second requires a bit more work. *)
    cbn.
    refine (contr_equiv' { s : f^-1 o f == idmap & eissect f == s } _).
    apply equiv_functor_sigma_id; intros s; cbn.
    apply equiv_functor_forall_id; intros a.
    refine (equiv_concat_l (eisadj f a) _ oE _).
    rapply equiv_ap.
  Qed.

  (** Now since [IsEquiv f] and the assertion that its fibers are contractible are both HProps, logical equivalence implies equivalence. *)
  Definition equiv_contr_map_isequiv {A B} (f : A -> B)
    : IsTruncMap (-2) f <~> IsEquiv f.
  Proof.
    rapply equiv_iff_hprop.
    (** Both directions are found by typeclass inference! *)
  Defined.

  (** It also follows that paths of equivalences are equivalent to paths of functions. *)
  Lemma equiv_path_equiv {A B : Type} (e1 e2 : A <~> B)
    : (e1 = e2 :> (A -> B)) <~> (e1 = e2 :> (A <~> B)).
  Proof.
    equiv_via ((issig_equiv A B) ^-1 e1 = (issig_equiv A B) ^-1 e2).
    2: symmetry; rapply equiv_ap.
    exact (equiv_path_sigma_hprop ((issig_equiv A B)^-1 e1) ((issig_equiv A B)^-1 e2)).
  Defined.

  Definition path_equiv {A B : Type} {e1 e2 : A <~> B}
    : (e1 = e2 :> (A -> B)) -> (e1 = e2 :> (A <~> B))
    := equiv_path_equiv e1 e2.

  #[export] Instance isequiv_path_equiv {A B : Type} {e1 e2 : A <~> B}
    : IsEquiv (@path_equiv _ _ e1 e2)
    (* Coq can find this instance by itself, but it's slow. *)
    := equiv_isequiv (equiv_path_equiv e1 e2).

  (** The inverse equivalence is homotopic to [ap equiv_fun], so that is also an equivalence. *)
  #[export] Instance isequiv_ap_equiv_fun {A B : Type} (e1 e2 : A <~> B)
    : IsEquiv (ap (x:=e1) (y:=e2) (@equiv_fun A B)).
  Proof.
    snapply isequiv_homotopic.
    - exact (equiv_path_equiv e1 e2)^-1%equiv.
    - exact _.
    - intro p. exact (ap_compose (fun v => (equiv_fun v; equiv_isequiv v)) pr1 p)^.
  Defined.

  (** This implies that types of equivalences inherit truncation.  Note that we only state the theorem for [n.+1]-truncatedness, since it is not true for contractibility: if [B] is contractible but [A] is not, then [A <~> B] is not contractible because it is not inhabited.

   Don't confuse this lemma with [trunc_equiv], which says that if [A] is truncated and [A] is equivalent to [B], then [B] is truncated.  It would be nice to find a better pair of names for them. *)
  #[export] Instance istrunc_equiv {n : trunc_index} {A B : Type} `{IsTrunc n.+1 B}
    : IsTrunc n.+1 (A <~> B).
  Proof.
    apply istrunc_S.
    intros e1 e2.
    exact (istrunc_equiv_istrunc _ (equiv_path_equiv e1 e2)).
  Defined.

  (** In the contractible case, we have to assume that *both* types are contractible to get a contractible type of equivalences. *)
  #[export] Instance contr_equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
    : Contr (A <~> B).
  Proof.
    apply (Build_Contr _ equiv_contr_contr).
    intros e. apply path_equiv, path_forall. intros ?; apply contr.
  Defined.

  (** The type of *automorphisms* of an hprop is always contractible *)
  #[export] Instance contr_aut_hprop A `{IsHProp A}
    : Contr (A <~> A).
  Proof.
    apply (Build_Contr _ 1%equiv).
    intros e; apply path_equiv, path_forall. intros ?; apply path_ishprop.
  Defined.

  (** Equivalences are functorial under equivalences. *)
  Definition functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
    : (A <~> B) -> (C <~> D)
    := fun f => ((k oE f) oE h^-1).

  #[export] Instance isequiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
    : IsEquiv (functor_equiv h k).
  Proof.
    refine (isequiv_adjointify _
              (functor_equiv (equiv_inverse h) (equiv_inverse k)) _ _).
    - intros f; apply path_equiv, path_arrow; intros x; simpl.
      exact (eisretr k _ @ ap f (eisretr h x)).
    - intros g; apply path_equiv, path_arrow; intros x; simpl.
      exact (eissect k _ @ ap g (eissect h x)).
  Defined.

  Definition equiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
    : (A <~> B) <~> (C <~> D)
    := Build_Equiv _ _ (functor_equiv h k) _.

  Definition equiv_functor_precompose_equiv@{i j k u v | i <= u, j <= v, k <= u, k <= v}
    {X : Type@{i}} {Y : Type@{j}} (Z : Type@{k}) (e : X <~> Y)
    : Equiv@{v u} (Y <~> Z) (X <~> Z)
    := equiv_functor_equiv e^-1%equiv 1%equiv.

  Definition equiv_functor_postcompose_equiv@{i j k u v | i <= u, j <= v, k <= u, k <= v}
    {X : Type@{i}} {Y : Type@{j}} (Z : Type@{k}) (e : X <~> Y)
    : Equiv@{u v} (Z <~> X) (Z <~> Y)
    := equiv_functor_equiv 1%equiv e.

  (** Reversing equivalences is an equivalence *)
  #[export]  Instance isequiv_equiv_inverse {A B}
    : IsEquiv (@equiv_inverse A B).
  Proof.
    refine (isequiv_adjointify _ equiv_inverse _ _);
      intros e; apply path_equiv; reflexivity.
  Defined.

  Definition equiv_equiv_inverse A B
    : (A <~> B) <~> (B <~> A)
    := Build_Equiv _ _ (@equiv_inverse A B) _.

End AssumeFunext.

(** ** Other facts about equivalences *)

(** This is like [transport_arrow], but for a family of equivalence types. It just shows that the functions are homotopic. *)
Definition transport_equiv {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C x1) (y : B x2)
  : (transport (fun x => B x <~> C x) p f) y = p # (f (p^ # y)).
Proof.
  destruct p; auto.
Defined.

(** A version that shows that the underlying functions are equal. *)
Definition transport_equiv' {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C x1)
  : transport (fun x => B x <~> C x) p f = (transport _ p) o f o (transport _ p^) :> (B x2 -> C x2).
Proof.
  destruct p; auto.
Defined.

(** A version that shows that the equivalences are equal.  Here we do need [Funext], for [path_equiv]. *)
Definition transport_equiv'' `{Funext} {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C x1)
  : transport (fun x => B x <~> C x) p f = (equiv_transport _ p) oE f oE (equiv_transport _ p^).
Proof.
  apply path_equiv.
  destruct p; auto.
Defined.

(** The special case when the codomain type is constant. *)
Definition transport_equiv_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C) (y : B x2)
  : (transport (fun x => B x <~> C) p f) y = f (p^ # y).
Proof.
  by destruct p.
Defined.

Definition transport_equiv_toconst' {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C)
  : transport (fun x => B x <~> C) p f = f o (transport _ p^) :> (B x2 -> C).
Proof.
  by destruct p.
Defined.

Definition transport_equiv_toconst'' `{Funext} {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 <~> C)
  : transport (fun x => B x <~> C) p f = f oE (equiv_transport _ p^).
Proof.
  apply path_equiv.
  by destruct p.
Defined.

(** The special case when the domain type is constant. *)
Definition transport_equiv_fromconst {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B <~> C x1) (y : B)
  : (transport (fun x => B <~> C x) p f) y = p # (f y).
Proof.
  by destruct p.
Defined.

Definition transport_equiv_fromconst' {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B <~> C x1)
  : (transport (fun x => B <~> C x) p f) = transport C p o f :> (B -> C x2).
Proof.
  by destruct p.
Defined.

Definition transport_equiv_fromconst'' `{Funext} {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B <~> C x1)
  : (transport (fun x => B <~> C x) p f) = equiv_transport C p oE f.
Proof.
  apply path_equiv.
  by destruct p.
Defined.
