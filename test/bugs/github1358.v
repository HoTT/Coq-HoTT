From HoTT Require Import Basics.

Axiom A@{i} : Type@{i}.

Axiom foo@{i} : A@{i} <~> A@{i}.

Definition bar@{i} : A@{i} <~> A@{i}.
Proof.
  reflexivity.
Defined.

Definition bar'@{i} : A@{i} <~> A@{i}.
Proof.
  exact equiv_idmap.
Defined.

