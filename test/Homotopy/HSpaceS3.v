From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS3.

(** The exported structure is found without supplying a diamond or doubled associativity. *)
Example sphere_three_hspace `{Univalence} : IsHSpace (psphere 3) := _.
