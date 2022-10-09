Require Import Basics Types.Sigma.

Record Box (A : SProp) : Type0 := box { unbox : A }.

#[export] Instance BoxSProp_IsHProp (A : SProp) : IsHProp (Box A).
Proof.
  intros x y.
  destruct x as [x'], y as [y']; change x' with y'.
  unshelve econstructor.
  - reflexivity.
  - intro y; 
      exact( match y with
           | idpath => idpath
             end ).
Defined.

Definition Equiv_of_SProp_iff (P : Type) `{IsHProp P} (Q : SProp) (F : P -> Q) (B : Q -> P) :
  Equiv P (Box Q) := @equiv_iff_hprop P _ (Box Q) _
                           (fun p => (box _ (F p)))
                           (fun q => match q with box q' => B q' end).
Print sig.

Local Unset Elimination Schemes.

Record Ssig {A:Type} (P:A->SProp) := Sexists { Spr1 : A; Spr2 : P Spr1 }.
Arguments Sexists {_} _ _ _.
Arguments Spr1 {_ _} _.
Arguments Spr2 {_ _} _.

Scheme Ssig_ind := Induction for Ssig Sort Type.
Scheme Ssig_rect := Induction for Ssig Sort Type. 
Scheme Ssig_rec := Minimality for Ssig Sort Type. Check Ssig_rect.
Scheme Ssig_sind := Minimality for Ssig Sort SProp.

Lemma Spr1_inj {A P} {a b : @Ssig A P} (e : Spr1 a = Spr1 b) : a = b.
  destruct a as [aval apf], b as [bval bpf].
  simpl in e.
  destruct e.
  reflexivity.
Defined.

Definition Sig_SSig_Equiv (A : Type) (P : A -> Type)
  `{forall a, IsHProp (P a)} (Q : A -> SProp)
  (F : forall a, P a -> Q a) (B : forall a, Q a -> P a) : Equiv { a : A & P a } (Ssig Q).
Proof.
  unshelve eapply Build_Equiv.
  - exact(fun a' => let (a, pfa) := a' in
              {| Spr1 := a; Spr2 := F a pfa |}).    
  - unshelve eapply Build_IsEquiv.
    + exact (fun b' => let (b, pfb) := b' in
                       {| proj1 := b ; proj2 := B b pfb |}).
    + exact(fun b => let (y, ypf) := b in
                     idpath _ ).
    + intro x; destruct x as [x xpf]; 
      by apply Sigma.path_sigma_hprop.
    + simpl. intro x. unfold Sigma.path_sigma_hprop, ap; simpl.
      destruct (center _); reflexivity.
Defined.

Inductive sEmpty : SProp :=.

Inductive sUnit : SProp := stt.

Scheme sEmpty_ind := Induction for sEmpty Sort Type.
Scheme sEmpty_rect := Induction for sEmpty Sort Type.
Scheme sEmpty_rec := Minimality for sEmpty Sort Type.
Scheme sEmpty_sind := Minimality for sEmpty Sort SProp.
