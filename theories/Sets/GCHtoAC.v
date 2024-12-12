From HoTT Require Import TruncType ExcludedMiddle abstract_algebra.
From HoTT Require Import Universes.Smallness.
From HoTT Require Import Spaces.Nat.Core Spaces.Card.
From HoTT Require Import Equiv.BiInv.
From HoTT Require Import HIT.unique_choice.

From HoTT.Sets Require Import Ordinals Hartogs Powers GCH AC.

Open Scope type.
Close Scope trunc_scope.

(* The proof of Sierpinski's results that GCH implies AC given in this file consists of two ingredients:
   1. Adding powers of infinite sets does not increase the cardinality (path_infinite_power).
   2. A variant of Cantor's theorem saying that P(X) <= (X + Y) implies P(X) <= Y for large X (Cantor_injects_injects).
   Those are used to obtain that cardinality-controlled functions are well-behaved in the presence of GCH (Sierpinski), from which we obtain by instantiation with the Hartogs number that every set embeds into an ordinal, which is enough to conclude GCH -> AC (GCH_AC) since the well-ordering theorem implies AC (WO_AC). *)


(** * Constructive equivalences *)

(* For the first ingredient, we establish a bunch of paths and conclude the desired result by equational reasoning. *)

Section Preparation.

Context {UA : Univalence}.

Lemma path_sum_prod X Y Z :
  (X -> Z) * (Y -> Z) = ((X + Y) -> Z).
Proof.
  apply path_universe_uncurried. apply equiv_sum_distributive.
Qed.

Lemma path_sum_assoc X Y Z :
  X + (Y + Z) = X + Y + Z.
Proof.
  symmetry. apply path_universe_uncurried. apply equiv_sum_assoc.
Qed.

Lemma path_sum_bool X :
  X + X = Bool * X.
Proof.
  apply path_universe_uncurried. srapply equiv_adjointify.
  - exact (fun x => match x with inl x => (true, x) | inr x => (false, x) end).
  - exact (fun x => match x with (true, x) => inl x | (false, x) => inr x end).
  - intros [[]]; reflexivity.
  - intros []; reflexivity.
Qed.

Lemma path_unit_nat :
  Unit + nat = nat.
Proof.
  apply path_universe_uncurried. srapply equiv_adjointify.
  - exact (fun x => match x with inl _ => O | inr n => S n end).
  - exact (fun n => match n with O => inl tt | S n => inr n end).
  - by intros [].
  - by intros [[]|n]. 
Qed.

Lemma path_unit_fun X :
  X = (Unit -> X).
Proof.
  apply path_universe_uncurried. apply equiv_unit_rec.
Qed.


(** * Equivalences relying on LEM **)

Context {EM : ExcludedMiddle}.

Lemma path_bool_prop :
  HProp = Bool.
Proof.
  apply path_universe_uncurried. srapply equiv_adjointify.
  - exact (fun P => if LEM P _ then true else false).
  - exact (fun b : Bool => if b then merely Unit else merely Empty).
  - intros []; destruct LEM as [H|H]; auto.
    + destruct (H (tr tt)).
    + apply (@merely_destruct Empty); try done. exact _.
  - intros P. destruct LEM as [H|H]; apply equiv_path_iff_hprop.
    + split; auto. intros _. apply tr. exact tt.
    + split; try done. intros HE. apply (@merely_destruct Empty); try done. exact _.
Qed.

Lemma path_bool_subsingleton :
  (Unit -> HProp) = Bool.
Proof.
  rewrite <- path_unit_fun. apply path_bool_prop.
Qed.

Lemma path_pred_sum X (p : X -> HProp) :
  X = sig p + sig (fun x => ~ p x).
Proof.
  apply path_universe_uncurried. srapply equiv_adjointify.
  - intros x. destruct (LEM (p x) _) as [H|H]; [left | right]; by exists x.
  - intros [[x _]|[x _]]; exact x.
  - cbn. intros [[x Hx]|[x Hx]]; destruct LEM as [H|H]; try contradiction.
    + enough (H = Hx) as -> by reflexivity. apply path_ishprop.
    + enough (H = Hx) as -> by reflexivity. apply path_forall. by intros HP.
  - cbn. intros x. by destruct LEM.
Qed.

Definition ran {X Y : Type} (f : X -> Y) :=
  fun y => hexists (fun x => f x = y).

Lemma path_ran {X} {Y : HSet} (f : X -> Y) :
  IsInjective f -> sig (ran f) = X.
Proof.
  intros Hf. apply path_universe_uncurried. srapply equiv_adjointify.
  - intros [y H]. destruct (iota (fun x => f x = y) _) as [x Hx]; try exact x.
    split; try apply H. intros x x'. cbn. intros Hy Hy'. rewrite <- Hy' in Hy. by apply Hf.
  - intros x. exists (f x). apply tr. exists x. reflexivity.
  - cbn. intros x. destruct iota as [x' H]. by apply Hf.
  - cbn. intros [y x]. apply path_sigma_hprop. cbn.
    destruct iota as [x' Hx]. apply Hx.
Qed.


(** * Equivalences on infinite sets *)

Lemma path_infinite_unit (X : HSet) :
  infinite X -> Unit + X = X.
Proof.
  intros [f Hf]. rewrite (@path_pred_sum X (ran f)).
  rewrite (path_ran _ Hf). rewrite path_sum_assoc.
  rewrite path_unit_nat. reflexivity.
Qed.

Fact path_infinite_power (X : HSet) :
  infinite X -> (X -> HProp) + (X -> HProp) = (X -> HProp).
Proof.
  intros H. rewrite path_sum_bool. rewrite <- path_bool_subsingleton.
  rewrite path_sum_prod. by rewrite path_infinite_unit.
Qed.


(** * Variants of Cantors's theorem *)

(* For the second ingredient, we give a preliminary version (Cantor_path_inject) to see the idea, as well as a stronger refinement (Cantor_injects_injects) which is then a mere reformulation. *)

Context {PR : PropResizing}.

Lemma Cantor X (f : X -> X -> Type) :
  { p | forall x, f x <> p }.
Proof.
  exists (fun x => ~ f x x). intros x H.
  enough (Hx : f x x <-> ~ f x x).
  - apply Hx; apply Hx; intros H'; by apply Hx.
  - pattern (f x) at 1. rewrite H. reflexivity.
Qed.

Lemma hCantor {X} (f : X -> X -> HProp) :
  { p | forall x, f x <> p }.
Proof.
  exists (fun x => Build_HProp (f x x -> Empty)). intros x H.
  enough (Hx : f x x <-> ~ f x x).
  - apply Hx; apply Hx; intros H'; by apply Hx.
  - pattern (f x) at 1. rewrite H. reflexivity.
Qed.

Definition clean_sum {X Y Z} (f : X -> Y + Z) :
  (forall x y, f x <> inl y) -> forall x, { z | inr z = f x }.
Proof.
  intros Hf. enough (H : forall x a, a = f x -> {z : Z & inr z = f x}).
  - intros x. by apply (H x (f x)).
  - intros x a Hxa. specialize (Hf x). destruct (f x) as [y|z].
    + apply Empty_rect. by apply (Hf y).
    + by exists z.
Qed.

Fact Cantor_path_injection {X Y} :
  (X -> HProp) = (X + Y) -> (X + X) = X -> Injection (X -> HProp) Y.
Proof.
  intros H1 H2. assert (H : X + Y = (X -> HProp) * (X -> HProp)).
  - by rewrite <- H1, path_sum_prod, H2. 
  - apply equiv_path in H as [f [g Hfg Hgf _]].
    pose (f' x := fst (f (inl x))). destruct (hCantor f') as [p Hp].
    pose (g' q := g (p, q)). assert (H' : forall q x, g' q <> inl x).
    + intros q x H. apply (Hp x). unfold f'. rewrite <- H. unfold g'. by rewrite Hfg.
    + exists (fun x => proj1 (clean_sum _ H' x)). intros q q' H. assert (Hqq' : g' q = g' q').
      * destruct clean_sum as [z <-]. destruct clean_sum as [z' <-]. cbn in H. by rewrite H.
      * unfold g' in Hqq'. change (snd (p, q) = snd (p, q')).
        rewrite <- (Hfg (p, q)), <- (Hfg (p, q')). by rewrite Hqq'.
Qed.

(* Version just requiring propositional injections *)

Lemma Cantor_rel X (R : X -> (X -> HProp) -> HProp) :
  (forall x p p', R x p -> R x p' -> merely (p = p')) -> { p | forall x, ~ R x p }.
Proof.
  intros HR. pose (pc x := Build_HProp (smalltype (forall p : X -> HProp, R x p -> ~ p x))).
  exists pc. intros x H. enough (Hpc : pc x <-> ~ pc x). 2: split.
  { apply Hpc; apply Hpc; intros H'; by apply Hpc. }
  - intros Hx. apply equiv_smalltype in Hx. by apply Hx.
  - intros Hx. apply equiv_smalltype. intros p Hp.
    eapply merely_destruct; try apply (HR _ _ _ Hp H). by intros ->.
Qed.

Lemma InjectsInto_power_morph X Y :
  InjectsInto X Y -> InjectsInto (X -> HProp) (Y -> HProp).
Proof.
  intros HF. eapply merely_destruct; try apply HF. intros [f Hf].
  apply tr. exists (fun p => fun y => hexists (fun x => p x /\ y = f x)).
  intros p q H. apply path_forall. intros x. apply equiv_path_iff_hprop. split; intros Hx.
  - assert (Hp : (fun y : Y => hexists (fun x : X => p x * (y = f x))) (f x)). { apply tr. exists x. split; trivial. }
    pattern (f x) in Hp. rewrite H in Hp. eapply merely_destruct; try apply Hp. by intros [x'[Hq <- % Hf]].
  - assert (Hq : (fun y : Y => hexists (fun x : X => q x * (y = f x))) (f x)). { apply tr. exists x. split; trivial. }
    pattern (f x) in Hq. rewrite <- H in Hq. eapply merely_destruct; try apply Hq. by intros [x'[Hp <- % Hf]].
Qed.

Fact Cantor_injects_injects {X Y : HSet} :
  InjectsInto (X -> HProp) (X + Y) -> InjectsInto (X + X) X -> InjectsInto (X -> HProp) Y.
Proof.
  intros H1 H2. assert (HF : InjectsInto ((X -> HProp) * (X -> HProp)) (X + Y)).
  - eapply InjectsInto_trans; try apply H1.
    eapply InjectsInto_trans; try apply InjectsInto_power_morph, H2.
    rewrite path_sum_prod. apply tr. reflexivity.
  - eapply merely_destruct; try apply HF. intros [f Hf].
    pose (R x p := hexists (fun q => f (p, q) = inl x)). destruct (@Cantor_rel _ R) as [p Hp].
    { intros x p p' H3 H4. eapply merely_destruct; try apply H3. intros [q Hq].
      eapply merely_destruct; try apply H4. intros [q' Hq']. apply tr.
      change p with (fst (p, q)). rewrite (Hf (p, q) (p', q')); trivial. by rewrite Hq, Hq'. }
    pose (f' q := f (p, q)). assert (H' : forall q x, f' q <> inl x).
    + intros q x H. apply (Hp x). apply tr. exists q. apply H.
    + apply tr. exists (fun x => proj1 (clean_sum _ H' x)). intros q q' H. assert (Hqq' : f' q = f' q').
      * destruct clean_sum as [z <-]. destruct clean_sum as [z' <-]. cbn in H. by rewrite H.
      * apply Hf in Hqq'. change q with (snd (p, q)). by rewrite Hqq'.
Qed.

End Preparation.


(** * Sierpinski's Theorem *)

Section Sierpinski.

Context {UA : Univalence}.
Context {EM : ExcludedMiddle}.
Context {PR : PropResizing}.

Definition powfix X :=
  forall n, (power_iterated X n + power_iterated X n) = (power_iterated X n).

Variable HN : HSet -> HSet.

Hypothesis HN_ninject : forall X, ~ InjectsInto (HN X) X.

Variable HN_bound : nat.
Hypothesis HN_inject : forall X, InjectsInto (HN X) (power_iterated X HN_bound).

(* This section then concludes the intermediate result that abstractly, any function HN behaving like the Hartogs number is tamed in the presence of GCH.  Morally we show that X <= HN(X) for all X, we just ensure that X is large enough by considering P(N + X). *)

Lemma InjectsInto_sum X Y X' Y' :
  InjectsInto X X' -> InjectsInto Y Y' -> InjectsInto (X + Y) (X' + Y').
Proof.
  intros H1 H2.
  eapply merely_destruct; try apply H1. intros [f Hf].
  eapply merely_destruct; try apply H2. intros [g Hg].
  apply tr. exists (fun z => match z with inl x => inl (f x) | inr y => inr (g y) end).
  intros [x|y] [x'|y'] H.
  - apply ap. apply Hf. apply path_sum_inl with Y'. apply H.
  - by apply inl_ne_inr in H.
  - by apply inr_ne_inl in H.
  - apply ap. apply Hg. apply path_sum_inr with X'. apply H.
Qed.

(* The main proof is by induction on the cardinality bound for HN.  As the Hartogs number is bounded by P^3(X), we'd actually just need finitely many instances of GCH. *)

Lemma Sierpinski_step (X : HSet) n :
  GCH -> infinite X -> powfix X -> InjectsInto (HN X) (power_iterated X n) -> InjectsInto X (HN X).
Proof.
  intros gch H1 H2 Hi. induction n.
  - by apply HN_ninject in Hi.
  - destruct (gch (Build_HSet (power_iterated X n)) (Build_HSet (power_iterated X n + HN X))) as [H|H].
    + by apply infinite_power_iterated.
    + apply tr. exists inl. intros x x'. apply path_sum_inl.
    + eapply InjectsInto_trans.
      * apply InjectsInto_sum; try apply Hi. apply tr, Injection_power. exact _.
      * cbn. specialize (H2 (S n)). cbn in H2. rewrite H2. apply tr, Injection_refl.
    + apply IHn. eapply InjectsInto_trans; try apply H. apply tr. exists inr. intros x y. apply path_sum_inr.
    + apply InjectsInto_trans with (power_iterated X (S n)); try apply tr, Injection_power_iterated.
      cbn. apply (Cantor_injects_injects H). rewrite (H2 n). apply tr, Injection_refl.
Qed.

Theorem GCH_injects' (X : HSet) :
  GCH -> infinite X -> InjectsInto X (HN (Build_HSet (X -> HProp))).
Proof.
  intros gch HX. eapply InjectsInto_trans; try apply tr, Injection_power; try apply X.
  apply (@Sierpinski_step (Build_HSet (X -> HProp)) HN_bound gch).
  - apply infinite_inject with X; trivial. apply Injection_power. apply X.
  - intros n. cbn. rewrite !power_iterated_shift. eapply path_infinite_power. cbn. by apply infinite_power_iterated.
  - apply HN_inject.
Qed.

Theorem GCH_injects (X : HSet) :
  GCH -> InjectsInto X (HN (Build_HSet (Build_HSet (nat + X) -> HProp))).
Proof.
  intros gch. eapply InjectsInto_trans with (nat + X).
  - apply tr. exists inr. intros x y. apply path_sum_inr.
  - apply GCH_injects'; trivial. exists inl. intros x y. apply path_sum_inl.
Qed.

End Sierpinski.

(* Main result: GCH implies AC *)

Theorem GCH_AC {UA : Univalence} {PR : PropResizing} {LEM : ExcludedMiddle} :
  GCH -> Choice_type.
Proof.
  intros gch.
  apply WO_AC. intros X. apply tr. exists (hartogs_number (Build_HSet (Build_HSet (nat + X) -> HProp))).
  unshelve eapply (@GCH_injects UA LEM PR hartogs_number _ 3 _ X gch).
  - intros Y. intros H. eapply merely_destruct; try apply H. apply hartogs_number_no_injection.
  - intros Y. apply tr. apply hartogs_number_injection.
Qed.

(* Note that the assumption of LEM is actually not necessary due to GCH_LEM. *)
