(* Basic material on identity types *)

Add Rec LoadPath "../univalent_foundations/Generalities".

Unset Automatic Introduction.

Require Export uu0.

Notation U := UUU.
Notation Id := paths.
Notation refl := idpath. 
Notation Sigma := total2.
Notation dpair := tpair.
Notation p1 := pr1.
Notation p2 := pr2.
Notation sym := pathsinv0.
Notation trans := @pathscomp0.
Notation refl_right_id := pathscomp0rid.
Notation inv_left_inv := pathsinv0l.
Notation inv_right_inv := pathsinv0r.
Notation inv_idem := pathsinv0inv0.
Notation transport := transportf.
Notation mapid := maponpaths.
Notation mapid_concat := maponpathscomp0.
Notation mapid_inv := maponpathsinv0.
Notation mapid_id := maponpathsidfun.
Notation mapid_comp := maponpathscomp.
Notation funext := funextfun.
Notation dfunext := funextsec.
Notation map_from_weq := pr1weq.
Notation inv_map_from_weq := invmap.
Notation weq_isom_right := homotweqinvweq.
Notation weq_isom_left := homotinvweqweq0.
Notation dep_appid_weq := weqtoforallpaths.

Implicit Arguments map_from_weq [X Y].

Notation "p @ q" := (pathscomp0 p q) (at level 60).
Notation "p !" := (pathsinv0 p) (at level 50).
Notation "f ; g" := (funcomp f g) (at level 50).

Definition Prod (A B : U) := Sigma (fun _ : A => B).
Definition pair {A B : U} (a : A) (b : B) := dpair _ a b.

(************************************************************************)
(************************************************************************)

(** Path properties **) 

Lemma assoc {X : U} {a b c d : X} (p : Id a b) (q : Id b c) (r : Id c d) :
  Id (p @ (q @ r)) ((p @ q) @ r).
Proof. 
intros. 
destruct p. 
apply refl.
Defined.

Lemma inv_cong {X : U} {a b : X} {p_1 p_2 : Id a b} :
  Id p_1 p_2 -> Id (p_1!) (p_2!).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma concat_cong_right {X : U} {a b c : X} {p_1 p_2 : Id a b} (q : Id b c) :
  Id p_1 p_2 -> Id (p_1 @ q) (p_2 @ q).
Proof.
intros.
destruct H. 
apply refl.
Defined.

Lemma concat_cong_left {X : U} {a b c : X} {q_1 q_2 : Id b c} (p : Id a b) :
  Id q_1 q_2 -> Id (p @ q_1) (p @ q_2).
Proof.
intros.
destruct H. 
apply refl.
Defined.

Lemma cancel_right {X : U} {a b c : X} (p : Id a c) (q_1 : Id a b) (q_2 : Id b c) :
  Id p (q_1 @ q_2) -> Id (p @ q_2!) q_1.
Proof. 
intros. 
destruct q_2.
apply trans with (b := p).
apply refl_right_id.
apply trans with (b := q_1 @ (refl b)).
apply H.
apply refl_right_id.
Defined.

Lemma cancel_left {X : U} {a b c : X} (p : Id a c) (q_1 : Id a b) (q_2 : Id b c) : 
 Id p (q_1 @ q_2) -> Id (q_1! @ p) q_2.
Proof. 
intros.
destruct q_1.
apply H.
Defined.

Lemma cancel_right_inv {X : U} {a b c : X} (p : Id a c) (q_1 : Id a b) (q_2 : Id c b) : 
 Id p (q_1 @ q_2!) -> Id (p @ q_2) q_1.
Proof. 
intros.
apply cancel_right in H.
apply trans with (b := p @ q_2!!).
apply concat_cong_left.
apply sym.
apply inv_idem.
apply H.
Defined.

Lemma cancel_left_inv {X : U} {a b c : X} (p : Id a c) (q_1 : Id b a) (q_2 : Id b c) : 
 Id p (q_1! @ q_2) -> Id (q_1 @ p) q_2.
Proof. 
intros.
destruct q_1.
apply H. 
Defined.

Lemma cancel_right_from_id {X : U} {a b : X} (p : Id a b) (q : Id b a) : 
 Id (p @ q) (refl a) -> Id p (q!).
Proof. 
intros.
apply sym in H.
apply cancel_right in H.
apply sym.
apply H.
Defined.

Lemma cancel_left_from_id {X : U} {a b : X} (p : Id a b) (q : Id b a) : 
 Id (p @ q) (refl a) -> Id (p!) q.
Proof. 
intros.
destruct p.
apply sym. 
apply H.
Defined.

Lemma cancel_right_inv_from_id {X : U} {a b : X} (p : Id a b) (q : Id a b) : 
 Id (p @ q!) (refl a) -> Id p q.
Proof. 
intros.
apply sym in H.
apply cancel_right_inv in H.
apply sym.
apply H.
Defined.

Lemma cancel_left_inv_from_id {X : U} {a b : X} (p : Id b a) (q : Id b a) : 
 Id (p! @ q) (refl a) -> Id p q.
Proof. 
intros.
destruct p.
apply sym.
apply H.
Defined.

(************************************************************************)
(************************************************************************)

(** Interaction between identity types and product types **)

Definition projid {A B : U} {p_1 p_2 : Prod A B} :
  Id p_1 p_2 -> Prod (Id (p1 p_1) (p1 p_2)) (Id (p2 p_1) (p2 p_2)).
Proof.
intros.
destruct H.
split.
apply refl.
apply refl.
Defined.

Definition p1id {A B : U} {p_1 p_2 : Prod A B} (p : Id p_1 p_2) := p1 (projid p).
Definition p2id {A B : U} {p_1 p_2 : Prod A B} (p : Id p_1 p_2) := p2 (projid p).

Definition prodext {A B : U} (p_1 p_2 : Prod A B) :
  Prod (Id (p1 p_1) (p1 p_2)) (Id (p2 p_1) (p2 p_2)) -> Id p_1 p_2.
Proof.
intros.
destruct H as [q_1 q_2].
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
simpl in q_1.
simpl in q_2.
destruct q_1.
destruct q_2.
apply refl.
Defined.

Lemma projid_prodext {A B : U} (p_1 p_2 : Prod A B) q :
  Id (projid (prodext p_1 p_2 q)) q.
Proof.
destruct q as [q_1 q_2].
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
simpl in q_1.
simpl in q_2.
destruct q_1.
destruct q_2.
apply refl.
Defined.

Lemma prodext_projid {A B : U} {p_1 p_2 : Prod A B} (q : Id p_1 p_2) :
  Id (prodext p_1 p_2 (projid q)) q.
Proof.
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
destruct q.
apply refl.
Defined.

Lemma projid_cong {A B : U} {p_1 p_2 : Prod A B} {q_1 q_2 : Id p_1 p_2} :
  Id q_1 q_2 -> Id (projid q_1) (projid q_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma prodext_cong {A B : U} (p_1 p_2 : Prod A B) {q_1 q_2} :
  Id q_1 q_2 -> Id (prodext p_1 p_2 q_1) (prodext p_1 p_2 q_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Definition dprojid {A : U} {B : A -> U} {p_1 p_2 : Sigma B} :
  Id p_1 p_2 ->
  Sigma (fun q : Id (p1 p_1) (p1 p_2) => Id (transport B q (p2 p_1)) (p2 p_2)).
Proof.
intros.
destruct H.
split with (refl (p1 p_1)).
apply refl.
Defined.

Definition dp1id {A : U} {B : A -> U} {p_1 p_2 : Sigma B} (p : Id p_1 p_2)
  := p1 (dprojid p).

Definition dp2id {A : U} {B : A -> U} {p_1 p_2 : Sigma B} (p : Id p_1 p_2)
  := p2 (dprojid p).

Definition dprodext {A : U} {B : A -> U} (p_1 p_2 : Sigma B) :
  Sigma (fun q : Id (p1 p_1) (p1 p_2) => Id (transport B q (p2 p_1)) (p2 p_2)) ->
  Id p_1 p_2.
Proof.
intros.
destruct H as [q_1 q_2].
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
simpl in q_1.
destruct q_1.
simpl in q_2.
destruct q_2.
apply refl.
Defined.

Lemma dprojid_dprodext {A : U} {B : A -> U} (p_1 p_2 : Sigma B) q :
  Id (dprojid (dprodext p_1 p_2 q)) q.
Proof.
destruct q as [q_1 q_2].
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
simpl in q_1.
simpl in q_2.
destruct q_1.
destruct q_2.
apply refl.
Defined.

Lemma dprodext_projid {A : U} {B : A -> U} {p_1 p_2 : Sigma B} (q : Id p_1 p_2) :
  Id (dprodext p_1 p_2 (dprojid q)) q.
Proof.
destruct p_1 as [a_1 b_1].
destruct p_2 as [a_2 b_2].
destruct q.
apply refl.
Defined.

Lemma dprojid_cong {A : U} {B : A -> U} {p_1 p_2 : Sigma B} {q_1 q_2 : Id p_1 p_2} :
  Id q_1 q_2 -> Id (dprojid q_1) (dprojid q_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma dprodext_cong {A : U} {B : A -> U} (p_1 p_2 : Sigma B) {q_1 q_2} :
  Id q_1 q_2 -> Id (dprodext p_1 p_2 q_1) (dprodext p_1 p_2 q_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

(************************************************************************)
(************************************************************************)

(** Interaction between identity types and function types **)

Definition appid {X Y : U} {f g : X -> Y} :
  Id f g -> forall (x : X), Id (f x) (g x).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma appid_funext {X Y : U} (f g : X -> Y) p :
  Id (appid (funext f g p)) p.
Proof.
intros.
unfold funext.
unfold dfunext.
set (w := dep_appid_weq (fun _ : X => Y) f g).
change appid with (map_from_weq w).
apply weq_isom_right.
Defined.

Lemma funext_appid {X Y : U} (f g : X -> Y) (p : Id f g) :
  Id (funext f g (appid p)) p.
Proof.
intros.
unfold funext.
unfold dfunext.
set (w := dep_appid_weq (fun _ : X => Y) f g).
change appid with (map_from_weq w).
apply sym.
apply weq_isom_left.
Defined.

Lemma appid_cong {X Y : U} {f g : X -> Y} {p_1 p_2 : Id f g} :
  Id p_1 p_2 -> Id (appid p_1) (appid p_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma funext_cong {X Y : U} (f g : X -> Y) {p_1 p_2} :
  Id p_1 p_2 -> Id (funext f g p_1) (funext f g p_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma funext_refl {X Y : U} (f : X -> Y) :
  Id (funext f f (fun x => refl (f x))) (refl f).
Proof.
intros.
change (fun x : X => refl (f x)) with (appid (refl f)).
apply funext_appid.
Defined. 

Definition dappid {X : U} (Y : X -> U) {f g : forall (x : X), Y x} :
  Id f g -> forall (x : X), Id (f x) (g x).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma dappid_dfunext {X : U} (Y : X -> U) (f g : forall (x : X), Y x) p :
  Id (dappid Y (dfunext Y f g p)) p.
Proof.
intros.
unfold dfunext.
set (w := dep_appid_weq Y f g).
change (dappid Y) with (map_from_weq w).
apply weq_isom_right.
Defined.

Lemma dfunext_dappid {X : U} (Y : X -> U) (f g : forall (x : X), Y x) (p : Id f g) :
  Id (dfunext Y f g (dappid Y p)) p.
Proof.
intros.
unfold dfunext.
set (w := dep_appid_weq Y f g).
change (dappid Y) with (map_from_weq w).
apply sym.
apply weq_isom_left.
Defined.

Lemma dappid_cong {X : U} (Y : X -> U) (f g : forall (x : X), Y x) {p_1 p_2 : Id f g} :
  Id p_1 p_2 -> Id (dappid Y p_1) (dappid Y p_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma dfunext_cong {X : U} (Y : X -> U) (f g : forall (x : X), Y x) {p_1 p_2} :
  Id p_1 p_2 -> Id (dfunext Y f g p_1) (dfunext Y f g p_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma dfunext_refl {X : U} (Y : X -> U) (f : forall (x : X), Y x) :
  Id (dfunext Y f f (fun x => refl (f x))) (refl f).
Proof.
intros.
change (fun x : X => refl (f x)) with (dappid Y (refl f)).
apply dfunext_dappid.
Defined.

(************************************************************************)
(************************************************************************)

(** Transporting between fibers *) 

Lemma transport_cong {X : U} (P : X -> U) {a b : X} {p q : Id a b} :
  Id p q -> Id (transport P p) (transport P q).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma transport_concat {X : U} (P : X -> U) {a b c : X} (p_1 : Id a b) (p_2 : Id b c) :
  Id (transport P (p_1 @ p_2)) (transport P p_1 ; transport P p_2).
Proof.
intros.
destruct p_1.
apply funext.
intros.
apply refl.
Defined.

Lemma transport_isom_left {X : U} (P : X -> U) {a b : X} (p : Id a b) (x : P a) :
  Id (transport P (p!) (transport P p x)) x.
Proof.
intros.
destruct p.
apply refl.
Defined.

Lemma transport_isom_right {X : U} (P : X -> U) {a b : X} (p : Id a b) (x : P b) :
  Id (transport P p (transport P (p!) x)) x.
Proof.
intros.
destruct p.
apply refl.
Defined.

Lemma transport_const {X : U} (A : U) {a b : X} (p : Id a b) :
  Id (transport (fun x => A) p) (idfun A).
Proof.
intros.
destruct p.
apply refl.
Defined.

Lemma transport_prod {X : U} (A B : X -> U) {a b : X} (p : Id a b) :
  Id (transport (fun x => Prod (A x) (B x)) p)
     (fun c => pair (transport A p (p1 c)) (transport B p (p2 c))).
Proof.
intros.
destruct p.
apply funext.
intro c.
destruct c as [c1 c2].
apply refl.
Defined.

Lemma transport_sig {X A : U} (B : X -> A -> U) {a b : X} (p : Id a b) :
  Id (transport (fun x => Sigma (B x)) p)
     (fun c => dpair (B b) (p1 c) (transport (fun x => B x (p1 c)) p (p2 c))).
Proof.
intros.
destruct p.
apply funext.
intro c.
destruct c as [c1 c2].
apply refl.
Defined.

Lemma transport_fun {X : U} (A B : X -> U) {x y : X} (p : Id x y) :
  Id (transport (fun x => A x -> B x) p)
     (fun f a => transport B p (f (transport A (p!) a))).
Proof.
intros.
destruct p.
apply funext.
intros f.
apply funext.
intros a.
apply refl.
Defined.

Lemma transport_forall {X A : U} (B : X -> A -> U) {x y : X} (p : Id x y) :
  Id (transport (fun x => forall (a : A), B x a) p)
     (fun f a => transport (fun x => B x a) p (f a)).
Proof.
intros.
destruct p.
apply funext.
intros f.
apply dfunext.
intros a.
apply refl.
Defined.

Lemma transport_id {X A : U} (f g : X -> A) {a b : X} (p : Id a b) :
  Id (transport (fun x => Id (f x) (g x)) p)
     (fun q => (mapid f p)! @ q @ (mapid g p)).
Proof.
intros.
destruct p.
apply funext.
intros q.
apply sym.
apply refl_right_id.
Defined.

(************************************************************************)
(************************************************************************)

(* Maps on identity proofs. *)

Lemma mapid_cong {X Y : U} (F : X -> Y) {a b : X} {p_1 p_2 : Id a b} :
  Id p_1 p_2 -> Id (mapid F p_1) (mapid F p_2).
Proof.
intros.
destruct H.
apply refl.
Defined.

Lemma mapid_const {X Y : U} (N : Y) {a b : X} (p : Id a b) :
  Id (mapid (fun x => N) p) (refl N).
Proof.
intros.
destruct p.
apply refl.
Defined.
 
Lemma mapid_app_to_const {X Y Z : U} (N : Z) (M : X -> Z -> Y) {a b : X} (p : Id a b) :
  Id (mapid (fun x => (M x) N) p) (appid (mapid M p) N).
Proof.
intros.
destruct p.
apply refl.
Defined.

Lemma mapid_app_of_const {X Y Z : U} (M : Z -> Y) (N : X -> Z) {a b : X} (p : Id a b) :
  Id (mapid (fun x => M (N x)) p) (mapid M (mapid N p)).
Proof.
intros.
destruct p.
apply refl.
Defined.

Lemma mapid_fun {X A : U} (B : A -> U) (M : forall (x : X) (a : A), B a) {x y : X} (p : Id x y) :
  Id (mapid (fun x => fun a => M x a) p)
     (dfunext B (fun a => M x a) (fun a => M y a) (fun a => mapid (fun x => M x a) p)).
Proof.
intros.
destruct p.
apply sym.
apply dfunext_refl.
Defined.

(** Horizontal composition of a path with a function  *) 

Definition comppathwithfun {X Y Z : U}{f_1 f_2 : X -> Y} : 
 forall (e : Id f_1 f_2)(g : Y -> Z), Id (funcomp f_1 g) (funcomp f_2 g).
Proof. 
intros. 
destruct e. 
apply refl.
Defined.

(** Horizontal composition of a function with a path *) 

Definition compfunwithpath {X Y Z : U}(f : X -> Y){g_1 g_2 : Y -> Z}(e : Id g_1 g_2) : 
 Id (funcomp f g_1)(funcomp f g_2).
Proof. 
intros. 
destruct e. 
apply refl.
Defined.

(** Associativity of composition of paths *) 

Definition pathscomp0assoc {X : U}{a b c d : X} : 
 forall (p : Id a b)(q : Id b c)(r : Id c d), Id (pathscomp0 p (pathscomp0 q r)) (pathscomp0 (pathscomp0 p q) r).
Proof. 
intros. 
destruct p. 
apply refl.
Defined.

(** Composition with a fixed path preserves propositional equality *) 

Definition compat_with_comp {X : U}{a b c : X}(p : Id a b){q_1 q_2 : Id b c}(alpha : Id q_1 q_2) :
 Id (pathscomp0 p q_1)(pathscomp0 p q_2).
Proof. 
intros. 
destruct alpha. 
apply refl.
Defined.
 
(** The operation of pre-composition with a fixed path is a weak equivalence *) 

Definition isweqpathcomp0r {X : U}(a b : X)(p : Id a b)(x : X) : 
 isweq (fun e : Id x a => pathscomp0 e p).
Proof. 
intros. 
apply (gradth (fun e : Id x a => pathscomp0 e p) (fun e : Id x b => pathscomp0 e (pathsinv0 p))).
intro e. 
destruct e. 
simpl. 
apply pathsinv0r. 
intro e. 
destruct e. 
simpl. 
apply pathsinv0l.
Defined.

(** The map from Id (p, q_1 @ q_2) to Id (q_1^{-1} @ p, q_2) *) 

Definition leftcancellationlaw {X : U}{a b c : X}(p : Id a c)(q_1 : Id a b)(q_2 : Id b c) : 
 Id p (pathscomp0 q_1 q_2) -> Id ( pathscomp0 ( pathsinv0 q_1) p ) q_2.
Proof. 
intros X a b c p q_1 q_2 e. 
destruct q_1. 
unfold pathsinv0. 
simpl. 
apply e.
Defined.

(** This map is a weak equivalence. This will be needed to deduce the 
contractibility of T from that of T' *) 

Definition isweqleftcancellationlaw {X : U}{a b c : X}(p : Id a c)(q_1 : Id a b)(q_2 : Id b c) : 
 isweq (leftcancellationlaw p q_1 q_2).
Proof. 
intros. 
unfold leftcancellationlaw. 
destruct q_1. 
simpl. 
apply (idisweq).
Defined.

Definition weqleftcancellationlaw {X : U}{a b c : X}(p : Id a c)(q_1 : Id a b)(q_2 : Id b c) : 
  weq (Id p (pathscomp0 q_1 q_2)) (Id ( pathscomp0 ( pathsinv0 q_1) p ) q_2).
Proof. 
intros. 
split with (leftcancellationlaw p q_1 q_2). 
apply (isweqleftcancellationlaw p q_1 q_2).
Defined.

(** Another useful lemma that we isolate separately *) 

Definition cancellationlemma {X : U}{a b c : X}(p : Id a b)(q : Id b c)(r : Id a c) : 
 Id (pathscomp0 p q) (pathscomp0 (pathscomp0 r (pathsinv0 q)) q) -> Id (pathscomp0 p q) r.
Proof. intros X a b c p q r e_1. 
assert (e_2 :  Id (pathscomp0 (pathscomp0 r (pathsinv0 q)) q) (pathscomp0 r (pathscomp0 (pathsinv0 q) q))).
destruct q. simpl. apply pathscomp0rid.
assert (e_3 : Id (pathscomp0 r (pathscomp0 (pathsinv0 q) q)) r).
destruct r. simpl. apply pathsinv0l.
apply (pathscomp0 (pathscomp0 e_1 e_2) e_3).
Defined.

(** Another useful law *) 

Definition second_square_lemma {X : U}{a b c d : X}(p : Id a b)(q : Id b d)(r : Id a c)(s : Id c d) :
 Id (pathscomp0 p q)(pathscomp0 r s) -> Id (pathscomp0 (pathsinv0 p) r) (pathscomp0 q (pathsinv0 s)).
Proof.
intros X a b c d p q r s e.
destruct p.
unfold pathsinv0.
simpl.
destruct q.
simpl.
destruct s.
simpl.
change (Id (pathscomp0 (refl c) (refl c)) (pathscomp0 r (refl c))) with (Id (refl c) (pathscomp0 r (refl c))) in e.
assert (e_1 : Id (refl c) r).
apply (transportf (fun z => Id (refl c) z) (pathscomp0rid r)).
apply e.
apply (pathsinv0 e_1).
Defined.

(** Functoriality of transportf *) 

Definition pathcompvstransportcomp {X : U}(E : X -> U){a b c : X}
(p : Id a b)(q : Id b c) : 
 Id ( (funcomp (transportf E p) (transportf E q))) 
  (transportf E (pathscomp0 p q)).

Proof.
intros.
apply funextfun.
destruct p.
unfold transportf.
simpl.
unfold idfun.
unfold funcomp.
intro x.
apply refl.
Defined.

(** Adjointness of transportf and transportb *)

Definition transposetransportfb {X : U}(P : X -> U)(x y : X)(e : Id x y) : 
 forall (a : P x)(b : P y), Id b (transportf P e a) -> Id (transportb P e b) a.
Proof.
intros X P x y e a b p.
destruct e.
unfold transportb.
simpl.
unfold transportf.
simpl.
apply p.
Defined.

Definition transposetransportbf {X : U}(P : X -> U)(x y : X)(e : Id x y) : 
 forall (a : P x)(b : P y), Id a (transportb P e b) -> Id (transportf P e a) b .
Proof.
intros X P x y e a b p.
destruct e.
unfold transportb.
simpl.
unfold transportf.
simpl.
apply p.
Defined.

(** Naturality property of transportf - as on p. 16 of Notes III *) 

Definition naturalityoftransportf {X : U}(P : X -> U)(Q : X -> U)(s : forall x : X, P x -> Q x){a b : X}(e : Id a b) :
 Id (funcomp (transportf P e) (s b)) (funcomp (s a) (transportf Q e)).
Proof.
intros.
destruct e.
unfold transportf.
unfold constr1.
simpl.
unfold idfun.
unfold funcomp.
apply refl.
Defined.

Definition naturalityoftransportb {X : U}(P : X -> U)(Q : X -> U)(s : forall x : X, P x -> Q x){a b : X}(e : Id a b) :
 Id (funcomp (transportb P e) (s a)) (funcomp (s b) (transportb Q e)).
Proof.
intros.
destruct e.
unfold transportb.
unfold transportf.
unfold constr1.
simpl.
unfold idfun.
unfold funcomp.
apply refl.
Defined.

(** The Beck-Chevalley condition for transportf and transportb *) 

Definition beck_chevalley_for_paths {X : U}(E : X -> U){a b c d : X}(f : Id a b)(g : Id b d)(h : Id a c)(k : Id c d) :
 Id (pathscomp0 f g) (pathscomp0 h k) -> 
 Id (funcomp (transportb E h) (transportf E f)) (funcomp (transportf E k) (transportb E g)).
Proof.
intros X E a b c d f g h k e.
unfold transportb.
apply (transportb (fun z => Id z _) (pathcompvstransportcomp E (pathsinv0 h) f)).
apply (transportb (fun z => Id _ z) (pathcompvstransportcomp E k (pathsinv0 g))).
apply maponpaths.
apply second_square_lemma.
apply (pathsinv0 e).
Defined.

(** A simple observation on contractibility *) 

Definition iscontriscontrpath (X : U) :
 (iscontr X) -> forall x y : X, iscontr (Id x y).
Proof.
intros X p.
destruct p as [c f].
intros x y.
split with (pathscomp0 (f x) (pathsinv0 (f y))).
intro e.
destruct e.
apply pathsinv0.
apply pathsinv0r.
Defined.

(** * Homotopies, i.e. pointwise identity proofs *) 

Definition Hom {X Y : U}(f g : X -> Y) :=
 forall (x : X), Id (f x) (g x).

(** Vertical composition of homotopies *) 

Definition homcomp0 {X Y : U}{f g h : X -> Y}(phi : Hom f g)(psi : Hom g h) : 
 Hom f h.
Proof. 
intros.
intro x.
apply (pathscomp0 (phi x) (psi x)).
Defined.

(** Horizontal composition of a function with a homotopy *) 

Definition compfunwithhomotopy {X Y Z : U}(f : X -> Y){g_1 g_2 : Y -> Z}(alpha : Hom g_1 g_2) :
 Hom (funcomp f g_1) (funcomp f g_2).
Proof.
intros.
unfold Hom.
intro x.
apply (alpha (f x)).
Defined.

(** Horizontal composition of a homotopy with a function *) 

Definition comphomotopywithfun {X Y Z : U}{f_1 f_2 : X -> Y}(alpha : Hom f_1 f_2)(g : Y -> Z) : 
 Hom (funcomp f_1 g) (funcomp f_2 g).
Proof. 
intros.
unfold Hom.
intro x.
apply (maponpaths g (alpha x)).
Defined.

(** * Paths and homotopies 

We relate operations on paths and on homotopies 
using function extensionality         *) 


(** Result of applying toforallpaths to a vertical composition of paths 
 First done pointwise then globally *) 

Definition comppathcomphom {X Y : U}(f g h : X -> Y)(p : Id f g)(q : Id g h) : 
 forall x : X, 
 Id ((homcomp0 (toforallpaths _ f g  p) (toforallpaths _ g h q)) x) 
    (toforallpaths _ f h (pathscomp0 p q) x).
Proof. 
intros.
destruct p.
unfold toforallpaths.
simpl.
apply refl.
Defined.

Definition comppathcomphom2 {X Y : U}(f g h : X -> Y)(p : Id f g)(q : Id g h) :
   Id ( homcomp0 (toforallpaths _ f g  p) (toforallpaths _ g h q) )
    (fun x : X => ( toforallpaths _ f h (pathscomp0 p q) x)).
Proof.
intros.
apply funextsec. 
apply comppathcomphom.
Defined.

(** Result of applying funextfun on vertical composition of homotopies *) 

Definition compcomphomcomppath {X Y : U}(f g h : X -> Y)(phi : Hom f g)(psi : Hom g h) : 
 Id (funextfun _ _ (homcomp0 phi psi)) ( pathscomp0  (funextfun _  _ phi) (funextfun  _ _ psi)).
Proof.
intros.
set (p := (funextfun _ _ phi)).
set (q := (funextfun _ _ psi)).
set (p_flat := (toforallpaths _ _ _ p)).
set (q_flat := (toforallpaths _ _ _ q)).
assert (e_1 : Id p_flat phi).
apply (homotweqinvweq (weqtoforallpaths _ f g) phi).
assert (e_2 :  Id q_flat psi).
apply (homotweqinvweq (weqtoforallpaths _ g h) psi).
apply (transportf (fun u => Id (funextfun f h (homcomp0 u psi)) (pathscomp0 p q)) e_1).
apply (transportf (fun v => Id (funextfun f h (homcomp0 p_flat v)) (pathscomp0 p q)) e_2).
assert (e_3 : Id (homcomp0 p_flat q_flat) (fun x : X => ( toforallpaths _ f h (pathscomp0 p q) x))).
apply (comppathcomphom2 f g h p q).
apply (transportb (fun u : (Hom f h) =>  Id (funextfun f h u) (pathscomp0 p q)) e_3).
apply (pathsinv0 (homotinvweqweq0 (weqtoforallpaths _ f h) (pathscomp0 p q))).
Defined.

(** Result of applying toforallpaths to horizontal composition of path with a function *) 

Definition comparefuncompwithpathwithfuncompwithhomot {X Y Z : U}(f_1 f_2 : X -> Y){g : Y -> Z}(e : Id f_1 f_2) : 
 Id (toforallpaths _ _ _ (comppathwithfun e g)) (comphomotopywithfun (toforallpaths _ _ _ e) g).
Proof.
intros.
destruct e.
apply refl.
Defined.

(** Result of applying funextfun to horizontal composition of homotopy with a function *) 

Definition comparefuncompwithpathwithfuncompwithhomot2  {X Y Z : U}{f_1 f_2 : X -> Y}(g : Y -> Z)(alpha : Hom f_1 f_2) : 
 Id (funextfun _ _  (comphomotopywithfun alpha g)) (comppathwithfun (funextfun _ _  alpha) g).
Proof.
intros.
set (e := (funextfun _ _ alpha)).
assert (p_1 : Id (toforallpaths _ _ _ e) alpha ).
apply (homotweqinvweq (weqtoforallpaths _ f_1 f_2) alpha).
assert (p_2 : Id (comppathwithfun e g) (funextfun _ _ (toforallpaths _ _ _ (comppathwithfun e g)))).
apply (homotinvweqweq0 (weqtoforallpaths _ (funcomp f_1 g)(funcomp f_2 g)) (comppathwithfun e g)).
apply (transportb 
(fun v =>  Id
     (funextfun (funcomp f_1 g) (funcomp f_2 g) (comphomotopywithfun alpha g))
     v) p_2).
apply maponpaths.
apply (transportf (fun v => Id (comphomotopywithfun v g)
     (toforallpaths (fun _ : X => Z) (funcomp f_1 g) 
        (funcomp f_2 g) (comppathwithfun e g))) p_1).
apply (pathsinv0 (comparefuncompwithpathwithfuncompwithhomot f_1 f_2 e)).
Defined.

(** Result of applying toforallpaths to horizontal composition of a function with a path *) 

Definition comparepathcompwithfunwithhomotcompwithfun {X Y Z : U}(f : X -> Y){g_1 g_2 : Y -> Z}(e : Id g_1 g_2) : 
 Id (toforallpaths _ _ _ (compfunwithpath f e)) (compfunwithhomotopy f (toforallpaths _ _ _ e)).
Proof.
intros.
destruct e.
apply refl.
Defined.

(** Result of applying funextfun to horizontal composition of a function with a homotopy *)

Definition comparehomotopycompwithfunwithpathcompwithfun {X Y Z : U}(f : X -> Y){g_1 g_2 : Y -> Z}(alpha : Hom g_1 g_2) : 
  Id (funextfun _ _  (compfunwithhomotopy f alpha)) (compfunwithpath f (funextfun _ _  alpha)).
Proof.
intros.
set (e := (funextfun _ _ alpha)).
set (e_flat := (toforallpaths _ _ _ e)).
assert (p : Id e_flat alpha).
apply (homotweqinvweq (weqtoforallpaths _ g_1 g_2) alpha).
apply (transportf (fun u => Id (funextfun _ _ (compfunwithhomotopy f u)) (compfunwithpath f e)) p).
apply (transportb (fun u => Id
     (funextfun (funcomp f g_1) (funcomp f g_2)
        u) (compfunwithpath f e)) 
 (pathsinv0 (comparepathcompwithfunwithhomotcompwithfun f e))).
apply (pathsinv0 (homotinvweqweq0 (weqtoforallpaths _ (funcomp f g_1) (funcomp f g_2)) (compfunwithpath f e))).
Defined.

(** * Eta rules

We use function extensionality to obtain terms   
 expressing a propositional version of the eta   
 rule that reduce to pointwise reflexivities for 
 functions in eta-expanded form.    *) 


Definition eta_homotopy {X Y : U}(u : X -> Y) : 
 forall x : X, Id (u x) ((fun x => u x) x) := 
    fun x : X => refl (u x).

Definition eta_path {X Y : U} : forall u : X -> Y, Id u (fun x => u x).
Proof.
intros.
apply (funextfun _ _ (eta_homotopy u)).
Defined.

(** * Sigma-types and identity types *)

Definition idfibertoidsigma {A : U}(B : A -> U)(a : A)(b_1 b_2 : B a) : 
 Id b_1 b_2 -> Id (dpair _ a b_1) (dpair _ a b_2).
Proof. 
intros A B a b_1 b_2 e. 
destruct e. 
apply refl.
Defined.

Definition idfibertoidsigmacomp  {A : U}(B : A -> U)(a : A)(b : B a) : 
 Id (idfibertoidsigma B a b b (refl b)) (refl (dpair _ a b)).
Proof. 
intros.
apply refl.
Defined.

Definition idsigmatobase  {A : U}(B : A -> U)(c_1 c_2 : Sigma B) :
  Id c_1 c_2 -> Id (p1 c_1) (p1 c_2).
Proof. 
intros A B c_1 c_2 e. 
destruct e. 
apply refl.
Defined.

Definition idsigmatosigmaid {A : U}(B : A -> U)(c : Sigma B) (d : Sigma B) :
 Id c d -> Sigma (fun v : Id (p1 c)(p1 d) => Id (transportf B v (p2 c)) (p2 d)).
Proof. 
intros A B c d u. 
destruct u.
split with (refl (p1 c)).
apply (refl (p2 c)).
Defined.

Definition lemmasigmaidtoidsigma {A : U}(B : A -> U)(a_1 : A)(b_1 : B a_1)(a_2 : A)(b_2 : B a_2) :
forall (u : Id a_1 a_2)(v : Id (transportf B u b_1) b_2), Id (dpair _ a_1 b_1) (dpair _ a_2 b_2).
Proof. 
intros.
destruct u.
change (Id (transportf B (refl a_1) b_1) b_2) with (Id b_1 b_2) in v.
destruct v.
apply refl.
Defined.

Definition sigmaidtoidsigma {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 Sigma (fun v : Id (p1 c_1)(p1 c_2) => Id (transportf B v (p2 c_1))(p2 c_2)) -> Id c_1 c_2.
Proof. 
intros A B c_1 c_2.
destruct c_1 as [a_1 b_1].
destruct c_2 as [a_2 b_2]. 
intro e.
destruct e as [u v].
apply (lemmasigmaidtoidsigma B a_1 b_1 a_2 b_2 u v). 
Defined.

Definition idsigmaidsigma {A : U}(B : A -> U)(c : Sigma B) (d : Sigma B)(e : Id c d) : 
 Id ( sigmaidtoidsigma B c d  (idsigmatosigmaid B c d e)  ) e.
Proof. 
intros A B c d.
intro e.
destruct e.
destruct c as [a b].
apply refl.
Defined.

Definition lemmasigmaidsigmaid {A : U}(B : A -> U)(a_1 : A)(b_1 : B a_1)(a_2 : A)(b_2 : B a_2)
(e : Sigma (fun v : Id a_1 a_2 => Id (transportf B v b_1) b_2)) : 
Id (idsigmatosigmaid B _ _ (sigmaidtoidsigma B (dpair _ a_1 b_1) (dpair _ a_2 b_2) e)) e.
Proof. 
intros.
destruct e as [u v].
simpl.
destruct u.
change (Id (transportf B (refl a_1) b_1) b_2) with (Id b_1 b_2) in v.
destruct v.
simpl.
apply refl.
Defined.

Definition sigmaidsigmaid {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 forall (e : Sigma (fun v : Id (p1 c_1)(p1 c_2) => Id (transportf B v (p2 c_1)) (p2 c_2))),  
 Id (idsigmatosigmaid B _ _ (sigmaidtoidsigma B c_1 c_2 e)) e. 
Proof.
intros.
destruct c_1 as [a_1 b_1].
destruct c_2 as [a_2 b_2].
apply (lemmasigmaidsigmaid _ a_1 b_1 a_2 b_2 e).
Defined.

Definition isweqidsigmatosigmaid {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 isweq (idsigmatosigmaid _ c_1 c_2).
Proof.
intros.
apply (gradth (idsigmatosigmaid _ c_1 c_2) (sigmaidtoidsigma _ c_1 c_2)).
apply (idsigmaidsigma _ c_1 c_2).
apply (sigmaidsigmaid _ c_1 c_2).
Defined.

Definition weqidsigmatosigmaid {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 weq (Id c_1 c_2) (Sigma (fun v : Id (p1 c_1)(p1 c_2) => Id (transportf B v (p2 c_1)) (p2 c_2))).
Proof.
intros.
split with (idsigmatosigmaid _ c_1 c_2).
apply (isweqidsigmatosigmaid _ c_1 c_2). 
Defined.

Definition isweqsigmaidtoidsigma {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 isweq (sigmaidtoidsigma _ c_1 c_2).
Proof.
intros A B c_1 c_2.
apply (gradth (sigmaidtoidsigma _ c_1 c_2) (idsigmatosigmaid _ c_1 c_2)).
apply (sigmaidsigmaid _ c_1 c_2).
apply (idsigmaidsigma _ c_1 c_2).
Defined.

Definition weqsigmaidtoidsigma {A : U}(B : A -> U)(c_1 : Sigma B)(c_2 : Sigma B) : 
 weq  (Sigma (fun v : Id (p1 c_1)(p1 c_2) => Id (transportf B v (p2 c_1)) (p2 c_2))) (Id c_1 c_2).
Proof.
intros.
split with (sigmaidtoidsigma _ c_1 c_2).
apply (isweqsigmaidtoidsigma _ c_1 c_2).
Defined.

(** * Pointwise vs global transport *) 

(**  Pointwise vs global transport of maps *) 

Definition pointwisetransportfpath {X Y : U}(f g : X -> Y)(E : Y -> U)(e : Id f g) :
 forall x : X, Id
  (transportf E (toforallpaths _ f g e x)) 
  (transportf (fun u => E (u x)) e).
Proof.
intros.
destruct e.
unfold transportf.
simpl.
apply refl.
Defined.

Definition pointwisetransportfhomotopy  {X Y : U}(f g : X -> Y)(E : Y -> U)(alpha : Hom f g) :
 forall x : X, Id
  (transportf E (alpha x)) 
  (transportf (fun u => E (u x)) (funextfun _ _ alpha)).
Proof.
intros.
set (e := (funextfun f g alpha)).
assert (p : Id (toforallpaths _ f g e) alpha).
unfold e.
apply (homotweqinvweq (weqtoforallpaths _ f g) alpha).
apply (transportf (fun z => Id (transportf E (z x)) (transportf (fun u : X -> Y => E (u x)) e)) p).
apply (pointwisetransportfpath f g E e).
Defined.

Definition pointwisetransportbpath {X Y : U}(f g : X -> Y)(E : Y -> U)(e : Id f g) :
 forall x : X, Id
  (transportb E (toforallpaths _ f g e x)) 
  (transportb (fun u => E (u x)) e).
Proof.
intros.
destruct e.
unfold transportb.
simpl.
apply refl.
Defined.

Definition pointwisetransportbhomotopy  {X Y : U}(f g : X -> Y)(E : Y -> U)(alpha : Hom f g) :
 forall x : X, Id
  (transportb E (alpha x)) 
  (transportb (fun u => E (u x)) (funextfun _ _ alpha)).
Proof.
intros.
set (e := (funextfun f g alpha)).
assert (p : Id (toforallpaths _ f g e) alpha).
unfold e.
apply (homotweqinvweq (weqtoforallpaths _ f g) alpha).
apply (transportf (fun z => Id (transportb E (z x)) (transportb (fun u : X -> Y => E (u x)) e)) p).
apply (pointwisetransportbpath f g E e).
Defined.

(** ** Global vs pointwise transport of sections *)

Definition homotopysectiontransportb  (X Y : U)(E : Y -> U){f g : X -> Y}(alpha : Hom f g) :
 (forall x : X, E (g x)) -> (forall x : X, E (f x)).
Proof.
intros X Y E f g alpha s.
intro x.
apply (transportb E (alpha x) (s x)).
Defined.

Definition pathsectiontransportb (X Y : U)(E : Y -> U){f g : X -> Y}(e : Id f g) : 
  (forall x : X, E (g x)) -> (forall x : X, E (f x)).
Proof.
intros X Y E f g e s.
apply (transportb (fun u =>  forall x : X, E (u x)) e s).
Defined.

Definition pathvshomotopysectiontransportb  (X Y : U)(E : Y -> U){f g : X -> Y}(e : Id f g) : 
 Id (homotopysectiontransportb X Y E (toforallpaths _ _ _ e)) (pathsectiontransportb X Y E e).
Proof.
intros.
destruct e.
unfold toforallpaths.
unfold pathsectiontransportb.
unfold transportb.
unfold transportf.
simpl.
unfold idfun.
unfold homotopysectiontransportb.
unfold transportb.
unfold transportf.
simpl.
unfold idfun.
apply funextfun.
intro t.
apply funextsec.
intro x.
apply refl.
Defined.

Definition homotopyvspathsectiontransportb (X Y : U)(E : Y -> U){f g : X -> Y}(alpha : Hom f g) :
 Id (pathsectiontransportb X Y E (funextfun _ _ alpha)) (homotopysectiontransportb X Y E alpha).
Proof.
intros.
set (e := (funextfun _ _ alpha)).
assert (p : Id (toforallpaths _ _ _ e) alpha).
apply (homotweqinvweq (weqtoforallpaths _ f g) alpha).
apply (transportf (fun x => Id (pathsectiontransportb X Y E e) (homotopysectiontransportb X Y E x)) p).
apply (pathsinv0 (pathvshomotopysectiontransportb X Y E e)).
Defined.

Definition homotopytransportbalongetaisidentity (X Y : U)(E : Y -> U){f : X -> Y} : 
 Id (homotopysectiontransportb _ _ E (eta_homotopy f)) (idfun (forall x : X, E (f x))).
Proof.
intros.
unfold homotopysectiontransportb.
unfold eta_homotopy.
unfold transportb.
unfold transportf.
simpl.
unfold idfun.
apply funextsec.
intro s.
apply funextsec.
intro x.
apply refl.
Defined.

(** Key result that allows us to simplify the square (H)  *) 

Definition pathtransportbalongetaisidentity (X Y : U)(E : Y -> U){f : X -> Y} : 
 Id (pathsectiontransportb _ _ E (eta_path f)) (idfun (forall x : X, E (f x))).
Proof.
intros.
assert 
 (p_1 : Id (pathsectiontransportb _ _ E (eta_path f)) 
           (homotopysectiontransportb _ _ E (eta_homotopy f))).
unfold eta_path.
apply (homotopyvspathsectiontransportb _ _  E (eta_homotopy f)).
apply (transportb (fun z =>  Id z (idfun (forall x : X, E (f x)))) p_1).
apply ( homotopytransportbalongetaisidentity _ _ E).
Defined.