Require Import WildCat.SetoidRewrite.
Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd WildCat.PointedCat
  WildCat.Yoneda WildCat.Graph WildCat.ZeroGroupoid WildCat.Pullbacks
  WildCat.AbEnriched WildCat.FunctorCat.

(** * Epi-stable categories *)

(** Epi-stable categories are those in which pullbacks exist and epimorphisms are stable under pullback.  This is somewhat similar to a regular category, but differs in a couple of ways.  First, we use the ordinary epimorphisms rather than the effective epimorphisms, mostly because they are easier to formalize.  Second, we don't assume that kernel pairs have co-equalizers. *)

(** ** Definition *)

Class IsEpiStable (A : Type) `{Is1Cat A} := {
    haspullbacks :: HasPullbacks A;
    stable_epic :: forall {a b c} (f : a $-> c) (g : b $-> c) {ep : Epic f},
        Epic (cat_pb_pr2 (CatPullback:=haspullbacks a b c f g));
  }.

(** ** Diagram chasing in an epi-stable category *)

(** One can do a certain amount of diagram chasing in an epi-stable category.  We'll see below that more can be done with an enrichment over abelian groups. *)

Section EpiStable.

  Context {A : Type} `{IsEpiStable A}.

  (** A generalized element of [B] with domain [P]. *)
  Definition elt (P B : A) := P $-> B.

  (** A generalized lift of a generalized element. *)
  Definition Lift {B C P : A} (c : elt P C) (f : B $-> C)
    := { P' : A & { e : P' $->> P & { b : elt P' B & f $o b $== c $o e }}}.

  (** Epimorphisms are characterized by the existence of generalized lifts. *)

  Definition epic_elt_lift {B C : A} (f : B $-> C)
    (lift : forall P (c : elt P C), Lift c f)
    : Epic f.
  Proof.
    specialize (lift C (Id C)).
    destruct lift as [P' [[e ep] [b h]]].
    cbn in h.
    pose proof (h' := h $@ cat_idl e); clear h.
    rapply (epic_cancel b f).
    apply (epic_homotopic _ _ h'^$).
  Defined.

  (** For the converse, we need the pullback epi of an epi. *)
  Definition cat_pb_pr2_epi {a b c : A} (f : a $->> c) (g : b $-> c)
    : cat_pb f g $->> b.
  Proof.
    exists (cat_pb_pr2 (f:=f) (g:=g)).
    exact _.
  Defined.

  Definition elt_lift_epic {B C : A} (f : B $-> C) {ef : Epic f}
    {P} (c : elt P C)
    : Lift c f.
  Proof.
    exists (cat_pb f c).
    exists (cat_pb_pr2_epi (f; ef) c).
    exists (cat_pb_pr1 (f:=f) (g:=c)).
    apply cat_pb_glue.
  Defined.

  (** The definition of [Monic] already implicitly involves generalized elements.  So this result isn't really needed, but might become more useful if we introduce a separate notation for applying a function to an [elt]. *)
  Definition monic_via_elt {B C : A} (f : B $-> C)
    (m : forall P (b b' : elt P B), f $o b $== f $o b' -> b $== b')
    : Monic f
    := m.

  (** To lift [b] through [f], it's enough to lift a pullback of [b] along an epi through [f]. *)
  Definition lift_helper {B C P P' : A} {b : elt P C} {f : B $-> C}
    (e : P' $->> P) (l : Lift (b $o e) f)
    : Lift b f.
  Proof.
    destruct l as [P'' [[e' ep] [b' h]]].
    exists P''.
    exists (e $o e'; epic_compose _ _).
    exists b'.
    rhs' apply (cat_assoc_opp e' e b).
    exact h.
  Defined.

End EpiStable.

(** Many proofs using diagram chasing end by supplying an element of [Lift] with [e] being the identity map.  This helps with this common case. See below for an example. *)
Tactic Notation "provide_lift" uconstr(a) :=
  refine (_; id_epi _; a; _);
  try rhs' napply cat_idr.

(** ** Epi-stable categories enriched in abelian groups *)

Class IsAbEpiStable (A : Type) `{Is1Cat A} := {
    isepistable_abepistable :: IsEpiStable A;
    isabenriched_abepistable :: IsAbEnriched A;
  }.

Section AbEpiStable.

  Context {A : Type} `{IsAbEpiStable A}.

  Open Scope mc_add_scope.

  (** We *define* exactness using generalized elements, which avoids needing to assume the existence of kernels, cokernels or images (or even define them).  In a category with kernels and images, you can show that this implies that the natural map from the image to the kernel is monic and epic, so in a nice enough category it is an isomorphism. *)

  Class CatIsAbExact {B C D : A} (f : B $-> C) (g : C $-> D) :=
    {
      isabcomplex : g $o f $== 0;
      isabexact : forall P (b : elt P C), g $o b $== 0 -> Lift b f;
    }.

  (** If a sequence [B $-> C] and [0 : C $-> D] is exact, then [B $-> C] is epi. *)
  Definition epic_isabexact_nil_morphism {B C D : A} (f : B $-> C)
    `{!CatIsAbExact f (0 : C $-> D)}
    : Epic f.
  Proof.
    apply epic_elt_lift.
    intros P c.
    apply isabexact.
    apply precomp_zero.
  Defined.

  (** If [B $-> C] is epi, then the sequence [B $-> C] and [0 : C$-> D] is exact. *)
  Definition isabexact_nil_morphism_epic {B C D : A} (f : B $->> C)
    : CatIsAbExact f (0 : C $-> D).
  Proof.
    refine {| isabcomplex := precomp_zero _ |}.
    intros P c h.
    rapply elt_lift_epic.
  Defined.

  (** This is a variant of [ismonic], where the RHS is [0]. *)
  Definition ismonic' {B C : A} (f : B $-> C) `{!Monic f}
    {P} (b : elt P B) (h : f $o b $== 0)
    : b $== 0.
  Proof.
    apply (ismonic f).
    lhs' exact h.
    symmetry.
    apply postcomp_zero.
  Defined.

  (** A map is monic if only the zero map is mapped to zero by post-composition. *)
  Definition monic_via_elt_isemb_ab {B C : A} (f : B $-> C)
   (h : forall P : A, forall b : elt P B, f $o b $== 0 -> b $== 0)
    : Monic f.
  Proof.
    apply monic_via_elt; intros P b' b'' h'.
    apply inverse_r_homotopy_0gpd in h'.
    apply (fun x => postcomp_op_inv f b' b'' $@ x) in h'.
    apply moveL_0M_0gpd.
    exact (h P (b' - b'') h').
  Defined.

  (** If [C $-> D] is monic, then the sequence [0 : B $-> C] and [C $-> D] is exact. *)
  Definition isabexact_nil_morphism_monic {B C D : A} (f : C $>-> D)
    : CatIsAbExact (0 : B $-> C) f.
  Proof.
    refine {| isabcomplex := postcomp_zero _ |}.
    intros P b h.
    provide_lift 0.
    lhs' apply postcomp_zero.
    exact (ismonic' f b h)^$.
  Defined.

  (** If the sequence [0 : B $-> C] and [C $-> D] is exact, then [C $-> D] is a mono. *)
  Definition monic_isabexact_nil_morphism {B C D : A} (f : C $-> D)
    `{!CatIsAbExact (0 : B $-> C) f}
    : Monic f.
  Proof.
    apply monic_via_elt.
    intros P b b' h.
    apply inverse_r_homotopy_0gpd in h.
    rewrite <- postcomp_op_inv in h.
    apply isabexact in h.
    destruct h as [P' [e [b'' h]]].
    apply moveL_0M_0gpd.
    apply (isepic e).
    rhs' apply precomp_zero.
    rhs_V' apply (precomp_zero b'').
    exact h^$.
  Defined.

End AbEpiStable.

(** ** Tactics *)

(** The [fix_left] tactic is the key to smooth diagram chasing in an [IsAbEpiStable] category.  Given [lift : Lift ? ?]; we extract the lifted element using the provided name [d] and the proof it is a lift using the name [l].  Then we update all other generalized elements to have the same domain as [d].  We could also have a limited version of this tactic for an [IsEpiStable] category. *)
Ltac fix_lift lift d l :=
  let P2 := fresh "P" in
  let e := fresh "e" in
  let ee := fresh "ee" in
  destruct lift as [P2 [[e ee] [d l]]];
  unfold hom_epi, ".1" in l;
  match type of e with
  | P2 $-> ?P =>
      (* Adjust everything involving the domain [P] to have domain [P2]: *)
      repeat match goal with
        | [ |- @Lift _ _ _ _ _ _ _ P ?c ?f ] => apply (lift_helper (e; ee)); unfold hom_epi, ".1"
        | [ |- @GpdHom (@Hom _ _ P _) _ _ _ _ _ ] => apply ee
        | [ |- @GpdHom (@elt _ _ P _) _ _ _ _ _ ] => apply ee
        | [ h : @GpdHom (@Hom _ _ P _) _ _ _ _ _ |- _ ] =>
            apply (fun w => cat_prewhisker w e) in h
        end;
      clear ee;
      (* Reassociate all homotopies so that [e] is right against the map to its left: *)
      rewrite ? (cat_assoc e);
      repeat match goal with
        (* Replace [(g $o f) $o e] with [g $o (f $o e)]: *)
        | [ h : @GpdHom (@Hom _ _ P2 _) _ _ _ _ _ |- _ ] =>
            rewrite ! (cat_assoc e) in h
        (* The above sometimes doesn't do all of the reassociating it could.  In the notation of the next line, we know that [B] and [D] are definitionally equal, but they might not be syntactically equal, and this can cause the rewrite to fail. So we coerce it to be of the right type. The previous line is thus redundant, but having it causes no slowdown, and it makes it clear what we are doing here. Similar issues may arise with the four other rewrites in this tactic, as well as the [cat_prewhisker].  An alternative to fixing them all would be to "sanitize" all [cat_comp] occurences to have the canonical objects as implicit arguments. *)
        | [ h : context [ @cat_comp ?A _ _ P2 P ?B (@cat_comp ?A _ _ P ?C ?D ?g ?f) e ] |- _ ] =>
            rewrite (cat_assoc e f g : @cat_comp A _ _ P2 P B (@cat_comp A _ _ P C D g f) e $== _) in h
        (* Replace [(f - g) $o e] with [f $o e - (g $o e)]: *)
        | [ h : @GpdHom (@Hom _ _ P2 _) _ _ _ _ _ |- _ ] =>
            rewrite ! (precomp_op_inv e) in h
        (* Replace [(f + g) $o e] with [f $o e + g $o e]: *)
        | [ h : @GpdHom (@Hom _ _ P2 _) _ _ _ _ _ |- _ ] =>
            rewrite ! (precomp_op e) in h
        (* Replace [(-f) $o e] with [-(f $o e)]: *)
        | [ h : @GpdHom (@Hom _ _ P2 _) _ _ _ _ _ |- _ ] =>
            rewrite ! (precomp_inv e) in h
        end;
      (* At this point, all generalized elements [c] with domain [P] should only appear in the form [c $o e], so by generalizing [c $o e] we can replace them with elements with domain [P2]. *)
      repeat match goal with
        | [ c : elt P ?C |- _ ] =>
            let tmp := fresh in
            set (tmp := c $o e : elt P2 _) in *;
            (* Unfortunately, [set] doesn't always find all occurrences, sometimes because the implicit arguments giving the domains/codomains of [c] and [e] are syntactically different. The next match handles this. *)
            repeat match goal with
              | [ h : context [ ?f $o e ] |- _ ] => change (f $o e) with tmp in h
            end;
            clearbody tmp; clear c; rename tmp into c
        end;
      (* We may also have expressions of the form [0 $o e], so we replace those with [0]. *)
      rewrite ? (precomp_zero e) in *;
      (* Now we can get rid of [e] and [P]. Add [try] before these two lines when debugging. *)
      clear e P;
      rename P2 into P
  end.

(** Ideas for making the above tactic faster:
    - In localized tests, defining and using things like
        [pose (cp := fun c f g w => cat_prewhisker (c:=c) (f:=f) (g:=g) w e).]
      made things faster, maybe because typeclass inference of the wild category structure didn't need to be repeated.  But when done here, the overall speed does not improve.
    - In the last clause of the first [repeat match], we could add "revert h".  Then instead of the second [repeat match] we would just need to do rewriting in the goal, without scanning the context for appropriate terms, using something like:
        [repeat progress rewrite ? (cat_assoc e), ? (precomp_op_inv e), ? (precomp_op e), ? (precomp_inv e).]
      For this to work, we need to extend setoid rewriting to handle [->].
   - Alternatively, in the second [repeat match], we could make the matches more specific to ensure that the lemmas we try apply to the situation.
*)

Ltac elt_lift_epic f a b l := fix_lift (elt_lift_epic f a) b l.

Tactic Notation "elt_lift_exact" constr(f) constr(g) constr(a) ident(b) ident(l) :=
  let lift := fresh in
  unshelve epose proof (lift := isabexact (f:=f) (g:=g) _ a _);
  only 2: fix_lift lift b l.

(** This allows us to insert a tactic [tac] before [fix_lift] is called.  Typically this is used to clear unneeded hypotheses from the context, which speeds up [fix_lift]. *)
Tactic Notation "elt_lift_exact" constr(f) constr(g) constr(a) ident(b) ident(l) "using" tactic3(tac) :=
  let lift := fresh in
  unshelve epose proof (lift := isabexact (f:=f) (g:=g) _ a _);
  only 2: (tac; fix_lift lift b l).

(** Other tactics that are convenient when diagram chasing. *)

(** Given a homotopy [h : a $o b = a' $o b'], use associativity to change [a $o (b $o c)] to [a' $o (b' $o c)]. *)
Ltac rewrite_with_assoc h :=
  rewrite (cat_assoc_opp _ _ _ $@ cat_prewhisker h _ $@ cat_assoc _ _ _).

(** Similar, with the other parenthesization. *)
Ltac rewrite_with_assoc_opp h :=
  rewrite (cat_assoc _ _ _ $@ cat_postwhisker _ h $@ cat_assoc_opp _ _ _).
