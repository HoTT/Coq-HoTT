From HoTT Require Import Basics.Overture HIT.Interval HIT.Flattening Colimits.GraphQuotient
          Spaces.Torus.Torus Cubical.DPath.

(* Test that various higher inductive types are defined correctly.  If they are defined in the most naive way, two uses of the induction principle that are definitionally equal on the point constructors will be considered definitionally equal, which is inconsistent.  There is an idiom that must be used in order to force Coq to regard the supplementary data as being required as well.  See, for example, Colimits/GraphQuotient.v for the idiom. *)

Fail Definition test_interval (P : interval -> Type) (a : P zero) (b : P one)
  (p p' : seg # a = b) :
  interval_ind P a b p = interval_ind P a b p'
  := 1.

Fail Definition test_wtil {A B f g C D} (Q : Wtil A B f g C D -> Type)
  (cct' : forall a x, Q (cct a x))
  (ppt' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
  (ppt'' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
  : Wtil_ind Q cct' ppt' = Wtil_ind Q cct' ppt''
  := 1.

Section GraphQuotient_bug.
  Local Definition R : Unit -> Unit -> Type := fun x y => Unit.

  (* This should be the circle. *)
  Local Definition Q := GraphQuotient R.

  (* This is the identity map. *)
  Local Definition id : Q -> Q := GraphQuotient_rec gq (fun a b r => gqglue r).

  (* This is the constant map. *)
  Local Definition cst : Q -> Q.
  Proof.
    refine (GraphQuotient_rec gq _).
    intros [] [] r.
    reflexivity.
  Defined.

  Fail Definition test_graphquotient : id = cst := 1.
End GraphQuotient_bug.

Fail Definition test_torus (P : Torus -> Type) (pb : P tbase)
  (pla pla' : DPath P loop_a pb pb)
  (plb : DPath P loop_b pb pb)
  (ps : DPathSquare P surf pla pla plb plb)
  (ps' : DPathSquare P surf pla' pla' plb plb)
  : Torus_ind P pb pla plb ps = Torus_ind P pb pla' plb ps'
  := 1.
