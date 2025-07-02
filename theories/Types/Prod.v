(** * Theorems about cartesian products *)

Require Import Basics.Overture Basics.Equivalences Basics.PathGroupoids
               Basics.Tactics Basics.Trunc Basics.Decidable Basics.Iff.
Require Import Types.Empty.
Local Open Scope path_scope.

Local Set Universe Minimization ToSet.

Generalizable Variables X A B f g n.

(* TODO: ": rename" is needed because the default names changed in Rocq 9.2.0.  When the minimum supported version is >= 9.2.0, the ": rename" can be removed. *)
Scheme prod_ind := Induction for prod Sort Type.
Arguments prod_ind {A B} P f p : rename.

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
  : (z = z').
Proof.
  change ((fst z, snd z) = (fst z', snd z')).
  case (fst pq). case (snd pq).
  reflexivity.
Defined.

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
  change z with (fst z, snd z).
  change z' with (fst z', snd z').
  destruct p, q.
  reflexivity.
Defined.

Definition ap_fst_path_prod' {A B : Type} {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap fst (path_prod' p q) = p.
Proof.
  apply ap_fst_path_prod.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  change z with (fst z, snd z).
  change z' with (fst z', snd z').
  destruct p, q.
  reflexivity.
Defined.

Definition ap_snd_path_prod' {A B : Type} {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap snd (path_prod' p q) = q.
Proof.
  apply ap_snd_path_prod.
Defined.

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
Proof.
  destruct p. reflexivity.
Defined.

Definition ap_path_prod {A B C : Type} (f : A -> B -> C)
           {z z' : A * B} (p : fst z = fst z') (q : snd z = snd z')
: ap (fun z => f (fst z) (snd z)) (path_prod _ _ p q)
  = ap011 f p q.
Proof.
  destruct z, z'; simpl in *; destruct p, q; reflexivity.
Defined.

(** Now we show how these compute with transport. *)

Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport P (path_prod_uncurried _ _ H) Px
  = transport (fun x => P (x, snd y))
              (fst H)
              (transport (fun y => P (fst x, y))
                         (snd H)
                         Px).
Proof.
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod {A B} (P : A * B -> Type) {x y : A * B}
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           (Px : P x)
: transport P (path_prod _ _ HA HB) Px
  = transport (fun x => P (x, snd y))
              HA
              (transport (fun y => P (fst x, y))
                         HB
                         Px)
  := transport_path_prod_uncurried P (HA, HB) Px.

Definition transport_path_prod'
           {A B} (P : A * B -> Type)
           {x y : A}
           {x' y' : B}
           (HA : x = y)
           (HB : x' = y')
           (Px : P (x,x'))
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px)
  := @transport_path_prod _ _ P (x, x') (y, y') HA HB Px.

(** This lets us identify the path space of a product type, up to equivalence. *)

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z') | 0.
Proof.
  refine (Build_IsEquiv _ _ _
            (fun r => (ap fst r, ap snd r))
            eta_path_prod
            (fun pq => path_prod'
                         (ap_fst_path_prod (fst pq) (snd pq))
                         (ap_snd_path_prod (fst pq) (snd pq)))
            _).
  destruct z as [x y], z' as [x' y'].
  intros [p q]; simpl in p, q.
  destruct p, q; reflexivity.
Defined.

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := Build_Equiv _ _ (path_prod_uncurried z z') _.

(** Path algebra *)

(** Composition.  The next three lemma are displayed equations in section 2.6 of the book, but they have no numbers so we can't put them into [HoTTBook.v]. *)
Definition path_prod_pp {A B : Type} (z z' z'' : A * B)
           (p : fst z = fst z') (p' : fst z' = fst z'')
           (q : snd z = snd z') (q' : snd z' = snd z'')
: path_prod z z'' (p @ p') (q @ q') = path_prod z z' p q @ path_prod z' z'' p' q'.
Proof.
  destruct z, z', z''; simpl in *; destruct p, p', q, q'.
  reflexivity.
Defined.

(** Associativity *)
Definition path_prod_pp_p  {A B : Type} (u v z w : A * B)
           (p : fst u = fst v) (q : fst v = fst z) (r : fst z = fst w)
           (p' : snd u = snd v) (q' : snd v = snd z) (r' : snd z = snd w)
: path_prod_pp u z w (p @ q) r (p' @ q') r'
  @ whiskerR (path_prod_pp u v z p q p' q') (path_prod z w r r')
  @ concat_pp_p (path_prod u v p p') (path_prod v z q q') (path_prod z w r r')
  = ap011 (path_prod u w) (concat_pp_p p q r) (concat_pp_p p' q' r')
    @ path_prod_pp u v w p (q @ r) p' (q' @ r')
    @ whiskerL (path_prod u v p p') (path_prod_pp v z w q r q' r').
Proof.
  destruct u, v, z, w; simpl in *; destruct p, p', q, q', r, r'.
  reflexivity.
Defined.

(** Inversion *)
Definition path_prod_V {A B : Type} (u v: A * B)
           (p : fst u = fst v)
           (q : snd u = snd v)
  : path_prod v u p^ q^ = (path_prod u v p q)^.
Proof.
  destruct u, v; simpl in *; destruct p, q.
  reflexivity.
Defined.

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
Proof.
  snapply Build_IsEquiv.
  - exact (functor_prod f^-1 g^-1).
  - intro z.
    exact (path_prod' (eisretr f _) (eisretr g _)).
  - intro w.
    exact (path_prod' (eissect f _) (eissect g _)).
  - intros [a b]; simpl.
    lhs napply (ap (fun p => path_prod' p _) (eisadj f _)).
    rhs napply ap_functor_prod.
    exact (ap _ (eisadj g _)).
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _. (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.
Defined.

Notation "f *E g" := (equiv_functor_prod' f g) : equiv_scope.

Definition equiv_functor_prod_l {A B B' : Type} (g : B <~> B')
  : A * B <~> A * B'
  := 1 *E g.

Definition equiv_functor_prod_r {A A' B : Type} (f : A <~> A')
  : A * B <~> A' * B
  := f *E 1.

(** ** Logical equivalences *)

Definition iff_functor_prod {A A' B B' : Type} (f : A <-> A') (g : B <-> B')
  : A * B <-> A' * B'
  := (functor_prod (fst f) (fst g) , functor_prod (snd f) (snd g)).

(** ** Symmetry *)

(** This is a special property of [prod], of course, not an instance of a general family of facts about types. *)

Definition equiv_prod_symm (A B : Type) : A * B <~> B * A.
Proof.
  make_equiv.
Defined.

(** ** Associativity *)

(** This, too, is a special property of [prod], of course, not an instance of a general family of facts about types. *)
Definition equiv_prod_assoc (A B C : Type) : A * (B * C) <~> (A * B) * C.
Proof.
  make_equiv.
Defined.

(** ** Unit and annihilation *)

Definition prod_empty_r@{u} (X : Type@{u}) : X * Empty <~> Empty
  := (Build_Equiv@{u u} _ _ snd _).

Definition prod_empty_l@{u} (X : Type@{u}) : Empty * X <~> Empty
  := (Build_Equiv@{u u} _ _ fst _).

Definition prod_unit_r X : X * Unit <~> X.
Proof.
  refine (Build_Equiv _ _ fst _).
  simple refine (Build_IsEquiv _ _ _ (fun x => (x,tt)) _ _ _).
  - intros x; reflexivity.
  - intros [x []]; reflexivity.
  - intros [x []]; reflexivity.
Defined.

Definition prod_unit_l X : Unit * X <~> X.
Proof.
  refine (Build_Equiv _ _ snd _).
  simple refine (Build_IsEquiv _ _ _ (fun x => (tt,x)) _ _ _).
  - intros x; reflexivity.
  - intros [[] x]; reflexivity.
  - intros [[] x]; reflexivity.
Defined.

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions.  Moreover, because the product type can expressed both positively and negatively, it has both a left universal property and a right one. *)

(* First the positive universal property. *)
Instance isequiv_prod_ind `(P : A * B -> Type)
: IsEquiv (prod_ind P) | 0
  := Build_IsEquiv
       _ _
       (prod_ind P)
       (fun f x y => f (x, y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_prod_ind `(P : A * B -> Type)
  : (forall (a : A) (b : B), P (a, b)) <~> (forall p : A * B, P p)
  := Build_Equiv _ _ (prod_ind P) _.

(* The non-dependent version, which is a special case, is the currying equivalence. *)
Definition equiv_uncurry (A B C : Type)
  : (A -> B -> C) <~> (A * B -> C)
  := equiv_prod_ind (fun _ => C).

(* Now the negative universal property. *)
Definition prod_coind_uncurried `{A : X -> Type} `{B : X -> Type}
  : (forall x, A x) * (forall x, B x) -> (forall x, A x * B x)
  := fun fg x => (fst fg x, snd fg x).

Definition prod_coind `(f : forall x:X, A x) `(g : forall x:X, B x)
  : forall x, A x * B x
  := prod_coind_uncurried (f, g).

Instance isequiv_prod_coind `(A : X -> Type) (B : X -> Type)
: IsEquiv (@prod_coind_uncurried X A B) | 0
  := Build_IsEquiv
       _ _
       (@prod_coind_uncurried X A B)
       (fun h => (fun x => fst (h x), fun x => snd (h x)))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_prod_coind `(A : X -> Type) (B : X -> Type)
  : ((forall x, A x) * (forall x, B x)) <~> (forall x, A x * B x)
  := Build_Equiv _ _ (@prod_coind_uncurried X A B) _.

(** ** Products preserve truncation *)

Instance istrunc_prod `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  simple_induction n n IH; simpl; (intros A ? B ?).
  { apply (Build_Contr _ (center A, center B)).
    intros z; apply path_prod; apply contr. }
  apply istrunc_S.
  intros x y.
  exact (istrunc_equiv_istrunc _ (equiv_path_prod x y)).
Defined.

Instance contr_prod `{CA : Contr A} `{CB : Contr B} : Contr (A * B) | 100
  := istrunc_prod.

(** ** Decidability *)

Instance decidable_prod {A B : Type}
       `{Decidable A} `{Decidable B}
: Decidable@{k} (A * B).
Proof.
  destruct (dec A) as [x1|y1]; destruct (dec B) as [x2|y2].
  - exact (inl@{k k} (x1,x2)).
  - apply inr@{k k}; intros [_ x2]; exact (y2 x2).
  - apply inr@{k k}; intros [x1 _]; exact (y1 x1).
  - apply inr@{k k}; intros [x1 _]; exact (y1 x1).
Defined.

(** Interaction of [ap] and uncurry *)

(** The function in [ap011] can be uncurried *)
Definition ap_uncurry {A B C} (f : A -> B -> C) {a a' : A} (p : a = a')
  {b b' : B} (q : b = b')
  : ap (uncurry f) (path_prod' p q) = ap011 f p q.
Proof.
  by destruct q, p.
Defined.

(** Fibers *)

(** ** Fibers of [functor_prod] *)
Definition hfiber_functor_prod {A B C D : Type} (f : A -> B) (g : C -> D) y
  : hfiber (functor_prod f g) y <~> (hfiber f (fst y) * hfiber g (snd y)).
Proof.
  unfold functor_prod.
  snrefine (equiv_adjointify _ _ _ _).
  - exact (fun x => ((fst x.1; ap fst x.2), (snd x.1; ap snd x.2))).
  - refine (fun xs => (((fst xs).1, (snd xs).1); _)).
    apply Prod.path_prod;simpl.
    + exact (fst xs).2.
    + exact (snd xs).2.
  - destruct y as [y1 y2]; intros [[x1 p1] [x2 p2]].
    simpl in *. destruct p1,p2. reflexivity.
  - intros [[x1 x2] p]. destruct p;cbn. reflexivity.
Defined.

Instance istruncmap_functor_prod (n : trunc_index) {A B C D : Type}
  (f : A -> B) (g : C -> D) `{!IsTruncMap n f} `{!IsTruncMap n g}
  : IsTruncMap n (Prod.functor_prod f g)
  := fun y => istrunc_equiv_istrunc _ (hfiber_functor_prod _ _ _)^-1.
