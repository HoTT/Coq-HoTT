Require Import HoTT.Basics Types.Universe Types.Paths Types.Unit FunextVarieties.

Generalizable All Variables.

(** * Univalence Implies Functional Extensionality *)

(** Here we prove that univalence implies function extensionality. *)
Set Printing Universes.
(** We define an axiom-free variant of [Univalence] *)
Definition Univalence_type := forall (A B : Type@{i}), IsEquiv (equiv_path A B).

(** Univalence is a property of a single universe; its statement lives in a higher universe *)
Check Univalence_type@{i iplusone} : Type@{iplusone}.

Section UnivalenceImpliesFunext.
  Context `{ua : Univalence_type}.

  (** Exponentiation preserves equivalences, i.e., if [e] is an equivalence then so is post-composition by [e]. *)

  (* Should this go somewhere else? *)

  Theorem univalence_isequiv_postcompose `{H0 : IsEquiv A B w} C : IsEquiv (fun (g:C->A) => w o g).
  Proof.
    unfold Univalence_type in *.
    refine (isequiv_adjointify
              (fun (g:C->A) => w o g)
              (fun (g:C->B) => w^-1 o g)
              _
              _);
    intro;
    pose (BuildEquiv _ _ w _) as w';
    change H0 with (@equiv_isequiv _ _ w');
    change w with (@equiv_fun _ _ w');
    clearbody w'; clear H0 w;
    rewrite <- (@eisretr _ _ (@equiv_path A B) (ua A B) w');
    generalize ((@equiv_inv _ _ (equiv_path A B) (ua A B)) w');
    intro p;
    clear w';
    destruct p;
    reflexivity.
  Defined.

  (** We are ready to prove functional extensionality, starting with the naive non-dependent version. *)

  Local Instance isequiv_src_compose A B
  : @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
             (A -> B)
             (fun g => (fst o pr1) o g).
  Proof.
    rapply @univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (fst o pr1) (fun x => ((x, x); idpath))
              (fun _ => idpath)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  Defined.


  Local Instance isequiv_tgt_compose A B
  : @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
             (A -> B)
             (fun g => (snd o pr1) o g).
  Proof.
    rapply @univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (snd o pr1) (fun x => ((x, x); idpath))
              (fun _ => idpath)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  Defined.

  Theorem Univalence_implies_FunextNondep : NaiveNondepFunext.
  Proof.
    intros A B f g p.
    (** Consider the following maps. *)
    pose (d := fun x : A => existT (fun xy => fst xy = snd xy) (f x, f x) (idpath (f x))).
    pose (e := fun x : A => existT (fun xy => fst xy = snd xy) (f x, g x) (p x)).
    (** If we compose [d] and [e] with [free_path_target], we get [f] and [g], respectively. So, if we had a path from [d] to [e], we would get one from [f] to [g]. *)
    change f with ((snd o pr1) o d).
    change g with ((snd o pr1) o e).
    erapply (ap (fun g => snd o pr1 o g)).
    (** Since composition with [src] is an equivalence, we can freely compose with [src]. *)
    pose (fun A B x y=> @equiv_inv _ _ _ (@isequiv_ap _ _ _ (@isequiv_src_compose A B) x y)) as H'.
    apply H'.
    reflexivity.
  Defined.

End UnivalenceImpliesFunext.

(** Note that only the codomain universe of [NaiveNondepFunext] is required to be univalent. *)
Check @Univalence_implies_FunextNondep@{j jplusone i max j max}
  : Univalence_type@{j jplusone} -> NaiveNondepFunext@{i j max}.

(** Now we use this to prove strong dependent funext.  Again only the codomain universe must be univalent, but the domain universe must be no larger than it is.  Thus practically speaking this means that a univalent universe satisfies funext only for functions between two types in that same universe. *)

Definition Univalence_implies_WeakFunext : Univalence_type -> WeakFunext
  := NaiveNondepFunext_implies_WeakFunext o @Univalence_implies_FunextNondep.

Definition Univalence_type_implies_Funext_type
           `{ua : Univalence_type@{j jplusone} }
  : Funext_type@{i j j}
  := NaiveNondepFunext_implies_Funext
       (@Univalence_implies_FunextNondep ua).

(** As justified by the above proof, we may assume [Univalence -> Funext]. *)
Global Instance Univalence_implies_Funext `{Univalence} : Funext.
Admitted.
