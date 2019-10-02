Require Import Basics.
Require Import Types.
Require Import HoTT.Tactics.
Require Import Diagrams.CommutativeSquares.
Require Import Diagrams.Graph.

Local Open Scope path_scope.

(** This file contains the definition of diagrams, diagram maps and equivalences of diagrams. *)

(** * Diagrams *)

(** A [Diagram] over a graph [G] associates a type to each point of the graph and a function to each arrow. *)

Record Diagram (G : Graph) := {
  obj : G -> Type;
  arr {i j : G} : G i j -> obj i -> obj j
}.

Arguments obj [G] D i : rename.
Arguments arr [G] D [i j] g x : rename.

Coercion obj : Diagram >-> Funclass.
Notation "D '_f' g" := (arr D g).

Section Diagram.
  Context `{Funext} {G: Graph}.

  (** [path_diagram] says when two diagrams are equals (up to funext). *)

  Definition path_diagram_naive (D1 D2 : Diagram G)
    (P := fun D' => forall i j, G i j -> (D' i -> D' j))
    (path_obj : obj D1 = obj D2)
    (path_arr : transport P path_obj (arr D1) = arr D2)
    : D1 = D2 :=
    match path_arr in (_ = v1)
      return D1 = {|obj := obj D2; arr := v1 |}
    with
      | idpath => match path_obj in (_ = v0)
        return D1 = {|obj := v0; arr := path_obj # (arr D1) |}
      with
        | idpath => 1
      end
    end.

  Definition path_diagram (D1 D2 : Diagram G)
    (path_obj : forall i, D1 i = D2 i)
    (path_arr : forall i j (g : G i j) x,
      transport idmap (path_obj j) (D1 _f g x)
      = D2 _f g (transport idmap (path_obj i) x))
    : D1 = D2.
  Proof.
    serapply path_diagram_naive; funext i.
    1: apply path_obj.
    funext j g x.
    rewrite 3 transport_forall_constant, transport_arrow.
    transport_path_forall_hammer.
    refine (_ @ path_arr i j g (transport idmap (path_obj i)^ x) @ _).
    { do 3 f_ap.
      rewrite <- path_forall_V.
      funext y.
      by transport_path_forall_hammer. }
    f_ap.
    exact (transport_pV idmap _ x).
  Defined.

  (** * Diagram map *)

  (** A map between two diagrams is a family of maps between the types of the diagrams making commuting the squares formed with the arrows. *)

  Record DiagramMap (D1 D2 : Diagram G) := {
    DiagramMap_obj  :> forall i, D1 i -> D2 i;
    DiagramMap_comm :  forall i j (g: G i j) x,
          D2 _f g (DiagramMap_obj i x) = DiagramMap_obj j (D1 _f g x)
  }.

  Global Arguments DiagramMap_obj [D1 D2] m i x : rename.
  Global Arguments DiagramMap_comm  [D1 D2] m [i j] f x : rename.
  Global Arguments Build_DiagramMap [D1 D2] _ _.

  (** [path_DiagramMap] says when two maps are equals (up to funext). *)

  Definition path_DiagramMap {D1 D2 : Diagram G}
    {m1 m2 : DiagramMap D1 D2} (h_obj : forall i, m1 i == m2 i)
    (h_comm : forall i j (g : G i j) x,
      DiagramMap_comm m1 g x @ h_obj j (D1 _f g x)
      = ap (D2 _f g) (h_obj i x) @ DiagramMap_comm m2 g x)
    : m1 = m2.
  Proof.
    destruct m1 as [m1_obj m1_comm].
    destruct m2 as [m2_obj m2_comm].
    simpl in *.
    revert h_obj h_comm.
    set (E := (@equiv_functor_forall _
       G (fun i => m1_obj i = m2_obj i)
       G (fun i => m1_obj i == m2_obj i)
       idmap _
       (fun i => @apD10 _ _ (m1_obj i) (m2_obj i)))
       (fun i => isequiv_apD10 _ _ _ _)).
    equiv_intro E h_obj.
    revert h_obj.
    equiv_intro (@apD10 _ _ m1_obj m2_obj) h_obj.
    destruct h_obj; simpl.
    intros h_comm.
    assert (HH : m1_comm = m2_comm).
    { funext i j f x.
      apply (concatR (concat_1p _)).
      apply (concatR (h_comm _ _ _ _)).
      apply inverse, concat_p1. }
    destruct HH.
    reflexivity.
  Defined.

  (** ** Identity and composition for diagram maps. *)

  Definition diagram_idmap (D : Diagram G) : DiagramMap D D
    := Build_DiagramMap (fun _ => idmap) (fun _ _ _ _ => 1).

  Definition diagram_comp {D1 D2 D3 : Diagram G} (m2 : DiagramMap D2 D3)
             (m1 : DiagramMap D1 D2) : DiagramMap D1 D3.
  Proof.
    apply (Build_DiagramMap (fun i => m2 i o m1 i)).
    intros i j f.
    exact (comm_square_comp (DiagramMap_comm m1 f) (DiagramMap_comm m2 f)).
  Defined.

  (** * Diagram equivalences *)

  (** An equivalence of diagram is a diagram map whose functions are equivalences. *)

  Record diagram_equiv (D1 D2: Diagram G) :=
    { diag_equiv_map :> DiagramMap D1 D2;
      diag_equiv_isequiv : forall i, IsEquiv (diag_equiv_map i) }.

  Global Arguments diag_equiv_map [D1 D2] e : rename.
  Global Arguments diag_equiv_isequiv [D1 D2] e i : rename.
  Global Arguments Build_diagram_equiv [D1 D2] m H : rename.

  (** Inverse, section and retraction of equivalences of diagrams. *)

  Lemma diagram_equiv_inv {D1 D2 : Diagram G} (w : diagram_equiv D1 D2)
    : DiagramMap D2 D1.
  Proof.
    apply (Build_DiagramMap
             (fun i => (BuildEquiv _ _ _ (diag_equiv_isequiv w i))^-1)).
    intros i j f.
    apply (@comm_square_inverse _ _ _ _ _ _
                                (BuildEquiv _ _ _ (diag_equiv_isequiv w i))
                                (BuildEquiv _ _ _ (diag_equiv_isequiv w j))).
    intros x; apply DiagramMap_comm.
  Defined.

  Lemma diagram_inv_is_section {D1 D2 : Diagram G}
        (w : diagram_equiv D1 D2)
    : diagram_comp w (diagram_equiv_inv w) = diagram_idmap D2.
  Proof.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv _ _ _ (is_eq_w i)).
    simple refine (path_DiagramMap _ _).
    - exact (fun i => eisretr (we i)).
    - simpl.
      intros i j f x. apply (concatR (concat_p1 _)^).
      apply (comm_square_inverse_is_retr (we i) (we j) _ x).
  Defined.

  Lemma diagram_inv_is_retraction {D1 D2 : Diagram G}
        (w : diagram_equiv D1 D2)
    : diagram_comp (diagram_equiv_inv w) w = diagram_idmap D1.
  Proof.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv _ _ _ (is_eq_w i)).
    simple refine (path_DiagramMap _ _).
    - exact (fun i => eissect (we i)).
    - simpl.
      intros i j f x. apply (concatR (concat_p1 _)^).
      apply (comm_square_inverse_is_sect (we i) (we j) _ x).
  Defined.

  (** The equivalence of diagram is an equivalence relation. *)
  (** Those instances allows to use the tactics reflexivity, symmetry and transitivity. *)
  Global Instance reflexive_diagram_equiv : Reflexive diagram_equiv | 1
    := fun D => Build_diagram_equiv (diagram_idmap D) _.

  Global Instance symmetric_diagram_equiv : Symmetric diagram_equiv | 1
    := fun D1 D2 m => Build_diagram_equiv (diagram_equiv_inv m) _.

  Global Instance transitive_diagram_equiv : Transitive diagram_equiv | 1.
  Proof.
  simple refine (fun D1 D2 D3 m1 m2 =>
                   Build_diagram_equiv (diagram_comp m2 m1) _).
  simpl. intros i; apply isequiv_compose';[apply m1 | apply m2].
  Defined.
End Diagram.

Notation "D1 ~d~ D2" := (diagram_equiv D1 D2).

