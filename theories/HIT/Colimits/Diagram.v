Require Import HoTT.Basics HoTT.Types HoTT.Tactics.
Require Import Colimits.CommutativeSquares.
Local Open Scope path_scope.

Context `{Funext}.

Record graph :=
  { graph0 : Type;
    graph1 : graph0 -> graph0 -> Type }.

Coercion graph0 : graph >-> Sortclass.
Coercion graph1 : graph >-> Funclass.

Record diagram (G : graph) :=
  { diagram0 : G -> Type;
    diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.

Arguments diagram0 [G] D i : rename.
Arguments diagram1 [G] D [i j] g x : rename.

Coercion diagram0 : diagram >-> Funclass.
Notation "D '_f' g" := (diagram1 D g) (at level 10).

Section Diagram.
  Context {G: graph}.

  (** Definition of path_diagram *)
  
  Definition path_diagram_naive (D1 D2: diagram G)
             (P := fun D' => forall i j, G i j -> (D' i -> D' j))
             (eq0 : diagram0 D1 = diagram0 D2)
             (eq1 : transport P eq0 (diagram1 D1) = diagram1 D2)
    : D1 = D2 :=
    match eq1 in (_ = v1) return D1 = {|diagram0 := diagram0 D2; diagram1 := v1 |} with
    | idpath =>
      match eq0 in (_ = v0) return D1 = {|diagram0 := v0; diagram1 := eq0 # (diagram1 D1) |} with
      | idpath => 1
      end
    end.


  Definition path_diagram (D1 D2: diagram G)
             (eq1 : forall i, D1 i = D2 i)
             (eq2 : forall i j (g : G i j) x,
                 transport idmap (eq1 j) (D1 _f g x)
                 = D2 _f g (transport idmap (eq1 i) x))
    : D1 = D2.
    serapply path_diagram_naive.
    funext i. apply eq1.
    funext i j g x.
    rewrite !transport_forall_constant.
    rewrite transport_arrow.
    transport_path_forall_hammer.
    refine (_ @ eq2 i j g (transport idmap (eq1 i)^ x) @ _).
    - f_ap. f_ap. f_ap.
      rewrite <- path_forall_V. funext y.
      transport_path_forall_hammer. reflexivity.
    - f_ap. exact (transport_pV idmap _ x).
  Defined.


  (** Definition of maps between diagram. *)

  Record diagram_map (D1 D2 : diagram G) :=
    { diagram_map_obj :> forall i, D1 i -> D2 i;
      diagram_map_comm: forall i j (g: G i j) x,
          D2 _f g (diagram_map_obj i x) = diagram_map_obj j (D1 _f g x) }.
  
  Global Arguments diagram_map_obj [D1 D2] m i x : rename.
  Global Arguments diagram_map_comm  [D1 D2] m [i j] f x : rename.
  Global Arguments Build_diagram_map [D1 D2] _ _.
  
  Definition path_diagram_map {D1 D2: diagram G}
             {m1 m2: diagram_map D1 D2}
             (h_obj: forall i, m1 i == m2 i)
             (h_comm: forall (i j: G) (g: G i j) (x: D1 i),
                 diagram_map_comm m1 g x @ h_obj j (D1 _f g x) =
                 ap (D2 _f g) (h_obj i x) @ diagram_map_comm m2 g x)
    : m1 = m2.
    destruct m1 as [m1_obj m1_comm].
    destruct m2 as [m2_obj m2_comm].
    simpl in *. revert h_obj h_comm.
    set (E := (@equiv_functor_forall _
                                     G (fun i => m1_obj i = m2_obj i)
                                     G (fun i => m1_obj i == m2_obj i)
                                     idmap _
                                     (fun i => @apD10 _ _ (m1_obj i) (m2_obj i)))
                (fun i => isequiv_apD10 _ _ _ _)).
    equiv_intro E h_obj.
    revert h_obj.
    equiv_intro (@apD10 _ _ m1_obj m2_obj) h_obj.
    destruct h_obj. simpl.
    intros h_comm.
    assert (HH : m1_comm = m2_comm). {
      funext i j f x.
      apply (concatR (concat_1p _)).
      apply (concatR (h_comm _ _ _ _)).
      apply inverse, concat_p1. }
    destruct HH. reflexivity.
  Defined.

  Definition diagram_idmap (D : diagram G) : diagram_map D D
    := Build_diagram_map (fun _ => idmap) (fun _ _ _ _ => 1).

  Definition diagram_comp {D1 D2 D3 : diagram G} (m2 : diagram_map D2 D3)
             (m1 : diagram_map D1 D2) : diagram_map D1 D3.
    apply (Build_diagram_map (fun i => m2 i o m1 i)).
    intros i j f.
    exact (comm_square_comp (diagram_map_comm m2 f) (diagram_map_comm m1 f)).
  Defined.

  Record diagram_equiv (D1 D2: diagram G) :=
    { diag_equiv_map :> diagram_map D1 D2;
      diag_equiv_isequiv : forall i, IsEquiv (diag_equiv_map i) }.

  Global Arguments diag_equiv_map [D1 D2] e : rename.
  Global Arguments diag_equiv_isequiv [D1 D2] e i : rename.
  Global Arguments Build_diagram_equiv [D1 D2] m H : rename.
  
  Lemma diagram_equiv_inv {D1 D2 : diagram G} (w : diagram_equiv D1 D2)
    : diagram_map D2 D1.
    apply (Build_diagram_map
             (fun i => (BuildEquiv _ _ _ (diag_equiv_isequiv w i))^-1)).
    intros i j f.
    apply (@comm_square_inverse _ _ _ _ _ _
                                (BuildEquiv _ _ _ (diag_equiv_isequiv w i))
                                (BuildEquiv _ _ _ (diag_equiv_isequiv w j))).
    intros x; apply diagram_map_comm.
  Defined.

  Lemma diagram_inv_is_section {D1 D2 : diagram G}
        (w : diagram_equiv D1 D2)
    : diagram_comp w (diagram_equiv_inv w) = diagram_idmap D2.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv _ _ _ (is_eq_w i)).
    simple refine (path_diagram_map _ _).
    exact (fun i => eisretr (we i)). simpl.
    intros i j f x. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_retr (we i) (we j) _ x).
  Defined.

  Lemma diagram_inv_is_retraction {D1 D2 : diagram G}
        (w : diagram_equiv D1 D2)
    : diagram_comp (diagram_equiv_inv w) w = diagram_idmap D1.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv _ _ _ (is_eq_w i)).
    simple refine (path_diagram_map _ _).
    exact (fun i => eissect (we i)). simpl.
    intros i j f x. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_sect (we i) (we j) _ x).
  Defined.

  Instance reflexive_diagram_equiv : Reflexive diagram_equiv
    := fun D => Build_diagram_equiv (diagram_idmap D) _.

  Instance symmetric_diagram_equiv : Symmetric diagram_equiv
    := fun D1 D2 m => Build_diagram_equiv (diagram_equiv_inv m) _.

  Instance transitive_diagram_equiv : Transitive diagram_equiv.
  simple refine (fun D1 D2 D3 m1 m2 =>
                   Build_diagram_equiv (diagram_comp m2 m1) _).
  simpl. intros i; apply isequiv_compose'. apply m1. apply m2.
  Defined.
End Diagram.

Notation "D1 ~d~ D2" := (diagram_equiv D1 D2) (at level 65).