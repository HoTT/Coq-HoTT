(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics Types.
Require Import SuccessorStructure.
Require Import WildCat.
Require Import Pointed.
Require Import ReflectiveSubuniverse Modality Modalities.Identity Modalities.Descent.
Require Import Truncations.
Require Import HFiber.

Local Open Scope succ_scope.
Open Scope pointed_scope.

(** * Exact sequences *)

(** ** Very short complexes *)

(** A (very short) complex is a pair of pointed maps whose composite is the zero map. *)
Definition IsComplex {F X Y} (i : F ->* X) (f : X ->* Y)
  := (f o* i ==* pconst).

(** This induces a map from the domain of [i] to the fiber of [f]. *)
Definition cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
           (cx : IsComplex i f)
  : F ->* pfiber f.
Proof.
  srapply Build_pMap.
  - intros x; exact (i x ; cx x).
  - cbn. refine (path_sigma' _ (point_eq i) _); cbn.
    refine (transport_paths_Fl _ _ @ _).
    apply moveR_Vp.
    exact ((concat_p1 _)^ @ point_htpy cx).
Defined.

(** ...whose composite with the projection [pfib : pfiber i -> X] is [i].  *)
Definition pfib_cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
           (cx : IsComplex i f)
  : pfib f o* cxfib cx ==* i.
Proof.
  srapply Build_pHomotopy.
  - intros u; reflexivity.
  - cbn.
    rewrite ap_pr1_path_sigma; hott_simpl.
Defined.

(** Truncation preserves complexes. *)
Definition iscomplex_ptr (n : trunc_index)
       {F X Y : pType} (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (ptr_functor n i) (ptr_functor n f).
Proof.
  refine ((ptr_functor_pmap_compose n i f)^* @* _).
  refine (_ @* ptr_functor_pconst n).
  apply ptr_functor_homotopy; assumption.
Defined.

(** Loopspaces preserve complexes. *)
Definition iscomplex_loops
       {F X Y : pType} (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (loops_functor i) (loops_functor f).
Proof.
  refine ((loops_functor_compose f i)^* @* _ @* loops_functor_pconst).
  apply loops_2functor; assumption.
Defined.

Definition iscomplex_iterated_loops
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           (cx : IsComplex i f) (n : nat)
  : IsComplex (iterated_loops_functor n i) (iterated_loops_functor n f).
Proof.
  induction n as [|n IHn]; [ exact cx | ].
  apply iscomplex_loops; assumption.
Defined.  

(** Passage across homotopies preserves complexes. *)
Definition iscomplex_homotopic_i {F X Y : pType}
           {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex i' f.
Proof.
  exact (pmap_postwhisker f ii @* cx).
Defined.

Definition iscomplex_homotopic_f {F X Y : pType}
           (i : F ->* X) {f f' : X ->* Y} (ff : f' ==* f) (cx : IsComplex i f)
  : IsComplex i f'.
Proof.
  exact (pmap_prewhisker i ff @* cx).
Defined.

Definition iscomplex_cancelR {F X Y Y' : pType}
           (i : F ->* X) (f : X ->* Y) (e : Y <~>* Y') (cx : IsComplex i (e o* f))
  : IsComplex i f :=
  (compose_V_hh e (f o* i))^$ $@ 
    cat_postwhisker _ ((cat_assoc _ _ _)^$ $@ cx) $@ precompose_pconst _.

(** And likewise passage across squares with equivalences *)
Definition iscomplex_equiv_i {F F' X X' Y : pType}
           (i : F ->* X) (i' : F' ->* X')
           (g : F' <~>* F) (h : X' <~>* X) (p : Square g h i' i)
           (f : X ->* Y)
           (cx: IsComplex i f)
  : IsComplex i' (f o* h).
Proof.
  refine (pmap_compose_assoc _ _ _ @* _).
  refine (pmap_postwhisker f p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker g cx @* _).
  apply postcompose_pconst.
Defined.


(** ** Very short exact sequences and fiber sequences *)

(** A complex is n-exact if the induced map [cxfib] is n-connected.  *)
Class IsExact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y) :=
{
  cx_isexact : IsComplex i f ;
  conn_map_isexact : IsConnMap n (cxfib cx_isexact)
}.

Global Existing Instance conn_map_isexact.

(** Passage across homotopies preserves exactness. *)
Definition isexact_homotopic_i n  {F X Y : pType}
           {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y)
           `{IsExact n F X Y i f}
  : IsExact n i' f.
Proof.
  exists (iscomplex_homotopic_i ii f cx_isexact).
  refine (conn_map_homotopic n (cxfib cx_isexact) _ _ _).
  intros u; cbn.
  refine (path_sigma' _ (ii u)^ _).
  exact (transport_paths_Fl _ _ @ ((inverse2 (ap_V _ _) @ inv_V _) @@ 1)).
Defined.  

Definition isexact_homotopic_f n  {F X Y : pType}
           (i : F ->* X) {f f' : X ->* Y} (ff : f' ==* f) 
           `{IsExact n F X Y i f}
  : IsExact n i f'.
Proof.
  exists (iscomplex_homotopic_f i ff cx_isexact).
  pose (e := equiv_hfiber_homotopic _ _ ff (point _)).
  nrefine (cancelR_isequiv_conn_map n _ e).
  1: apply equiv_isequiv.
  refine (conn_map_homotopic n (cxfib (cx_isexact)) _ _ _).
  intro u. simpl. srapply path_hfiber.
  1: reflexivity.
  refine (concat_1p _ @ concat_V_pp _ _)^.
Defined.

(** And also passage across squares with equivalences. *)
Definition isexact_equiv_i n  {F F' X X' Y : pType}
           (i : F ->* X) (i' : F' ->* X')
           (g : F' <~>* F) (h : X' <~>* X) (p : Square g h i' i)
           (f : X ->* Y)
           `{IsExact n F X Y i f}
  : IsExact n i' (f o* h).
Proof.
  exists (iscomplex_equiv_i i i' g h p f cx_isexact); cbn.
  snrefine (cancelR_equiv_conn_map n (C := pfiber f) _ _).
  - exact (@equiv_functor_hfiber _ _ _ _ (f o h) f h equiv_idmap
             (fun x => 1%path) (point Y)).
  - cbn; unfold functor_hfiber, functor_sigma; cbn.
    refine (conn_map_homotopic n (@cxfib _ _ _ i f cx_isexact o g) _ _ _).
    intros u; cbn.
    refine (path_sigma' _ (p u)^ _).
    abstract (
        rewrite transport_paths_Fl, ap_V, inv_V,
        !concat_1p, concat_p1, ap_idmap;
        reflexivity
      ).
Defined.

(** An equivalence of short sequences preserves exactness. *)
Definition isexact_square_if n  {F F' X X' Y Y' : pType}
           {i : F ->* X} {i' : F' ->* X'}
           {f : X ->* Y} {f' : X' ->* Y'}
           (g : F' <~>* F) (h : X' <~>* X) (k : Y' <~>* Y) 
           (p : Square g h i' i)
           (q : Square h k f' f)
           `{IsExact n F X Y i f}
  : IsExact n i' f'.
Proof.
  pose (I := isexact_equiv_i n i i' g h p f).
  pose (I2 := isexact_homotopic_f n i' q).
  exists (iscomplex_cancelR i' f' k cx_isexact).
  pose (e := (pequiv_pfiber (id_cate _) k (cat_idr _)^$ : pfiber f' <~>* pfiber (k o* f'))).
  nrefine (cancelR_isequiv_conn_map n _ e). 1: apply pointed_isequiv.
  refine (conn_map_homotopic n (cxfib (cx_isexact)) _ _ _).
  intro u. srapply path_hfiber.
  { reflexivity. }
  cbn. unfold moveR_equiv_V. rewrite !concat_1p, !concat_p1, ap_pp_p, ap_pp, (ap_pp k _ (eissect k (point Y'))), ap_V, <- !eisadj. 
  rewrite <- !ap_compose, concat_pp_p. 
  rewrite (concat_A1p (eisretr k)), concat_pV_p.
  rewrite (concat_A1p (eisretr k)), concat_V_pp. reflexivity.
Defined.

(** When [n] is the identity modality [oo], so that [cxfib] is an equivalence, we get simply a fiber sequence.  In particular, the fiber of a given map yields an oo-exact sequence. *)

Definition iscomplex_pfib {X Y} (f : X ->* Y)
  : IsComplex (pfib f) f.
Proof.
  srapply Build_pHomotopy.
  - intros [x p]; exact p.
  - cbn. exact (concat_p1 _ @ concat_1p _)^.
Defined.

Global Instance isexact_pfib {X Y} (f : X ->* Y)
  : IsExact oo (pfib f) f.
Proof.
  exists (iscomplex_pfib f).
  exact _.
Defined.    

(** Fiber sequences can alternatively be defined as an equivalence to the fiber of some map. *)
Definition FiberSeq (F X Y : pType) := { f : X ->* Y & F <~>* pfiber f }.

Definition i_fiberseq {F X Y} (fs : FiberSeq F X Y)
  : F ->* X
  := pfib fs.1 o* fs.2.

Global Instance isexact_oo_fiberseq {F X Y : pType} (fs : FiberSeq F X Y)
  : IsExact oo (i_fiberseq fs) fs.1.
Proof.
  srapply Build_IsExact; [ srapply Build_pHomotopy | ].
  - intros u; cbn. 
    exact ((fs.2 u).2).
  - apply moveL_pV. cbn.
    refine (concat_p1 _ @ _).
    apply moveL_Mp.
    refine (_ @ (point_eq fs.2)..2).
    refine (_ @ (transport_paths_Fl _ _)^).
    apply whiskerR, inverse2, ap, concat_p1.
  - intros [x p].
    apply contr_map_isequiv.
    change (IsEquiv fs.2); exact _.
Defined.

Definition pequiv_cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
           `{IsExact oo F X Y i f}
  : F <~>* pfiber f.
Proof.
  refine (Build_pEquiv _ _ (cxfib cx_isexact) _).
  apply isequiv_contr_map; intros u. 
  rapply conn_map_isexact.
Defined.

Definition fiberseq_isexact_oo {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : FiberSeq F X Y
  := (f ; pequiv_cxfib).

(** It's easier to show that loops preserve fiber sequences than that they preserve oo-exact sequences. *)
Definition fiberseq_loops {F X Y} (fs : FiberSeq F X Y)
  : FiberSeq (loops F) (loops X) (loops Y).
Proof.
  exists (loops_functor fs.1).
  refine (_ o*E pequiv_loops_functor fs.2).
  exact ((pfiber_loops_functor fs.1)^-1* ).
Defined.

(** Now we can deduce that they preserve oo-exact sequences.  The hardest part is modifying the first map back to [loops_functor i]. *)
Global Instance isexact_loops {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : IsExact oo (loops_functor i) (loops_functor f).
Proof.
  refine (@isexact_homotopic_i
            oo _ _ _ _ (loops_functor i) _ (loops_functor f)
            (isexact_oo_fiberseq (fiberseq_loops (fiberseq_isexact_oo i f)))).
  transitivity (loops_functor (pfib f) o* loops_functor (cxfib cx_isexact)).
  - refine (_ @* loops_functor_compose _ _).
    apply loops_2functor.
    symmetry; apply pfib_cxfib.
  - refine (_ @* pmap_compose_assoc _ _ _).
    refine (pmap_prewhisker (loops_functor (cxfib cx_isexact)) _).
    apply moveR_pequiv_fV.
    apply pr1_pfiber_loops_functor.
Defined.

Global Instance isexact_iterated_loops {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f} (n : nat)
  : IsExact oo (iterated_loops_functor n i) (iterated_loops_functor n f).
Proof.
  induction n as [|n IHn]; [ assumption | apply isexact_loops; assumption ].
Defined.

(** (n.+1)-truncation preserves n-exactness. *)
Global Instance isexact_ptr `{Univalence} (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact (Tr n) F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  exists (iscomplex_ptr n.+1 i f cx_isexact).
  simple notypeclasses refine
    (cancelR_conn_map (Tr n) (@tr n.+1 F) 
      (@cxfib _ _ _ (ptr_functor n.+1 i) (ptr_functor n.+1 f) _)).
  { intros x; rapply isconnected_pred. }
  nrapply conn_map_homotopic.
  2:nrapply (conn_map_compose _ (cxfib _)
               (functor_hfiber (fun y => (to_O_natural (Tr n.+1) f y)^)
                               (point Y))).
  3:pose @O_lex_leq_Tr; rapply (OO_conn_map_functor_hfiber_to_O).
  - intros x; refine (path_sigma' _ 1 _); cbn.
    (* This is even simpler than it looks, because for truncations [to_O_natural n.+1 := 1], [to n.+1 := tr], and [cx_const := H]. *)
    exact (1 @@ (concat_p1 _)^).
  - exact _.
Defined.

(** In particular, (n.+1)-truncation takes fiber sequences to n-exact ones. *)
Global Instance isexact_ptr_oo `{Univalence} (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y) `{IsExact oo F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  rapply isexact_ptr.
  exists cx_isexact.
  intros z; apply isconnected_contr.
  exact (conn_map_isexact (f := f) (i := i) z).
Defined.

(** ** Connecting maps *)

(** It's useful to see [pfib_cxfib] as a degenerate square. *)
Definition square_pfib_pequiv_cxfib
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : Square (pequiv_cxfib) (pequiv_pmap_idmap) i (pfib f).
Proof.
  unfold Square.
  refine (pmap_postcompose_idmap _ @* _).
  symmetry; apply pfib_cxfib.
Defined.

(** The connecting maps for the long exact sequence of loop spaces, defined as an extension to a fiber sequence. *)
Definition connect_fiberseq {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : FiberSeq (loops Y) F X.
Proof.
  exists i.
  exact (((pfiber2_loops f) o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f)))^-1*).
Defined.

Definition connecting_map {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : loops Y ->* F
  := i_fiberseq (connect_fiberseq i f).

Global Instance isexact_connect_R {F X Y} (i : F ->* X) (f : X ->* Y)
       `{IsExact oo F X Y i f}
  : IsExact oo (loops_functor f) (connecting_map i f).
Proof.
  refine (isexact_equiv_i (Y := F) oo
          (pfib (pfib i)) (loops_functor f)
          (((loops_inv X) o*E
            (pfiber2_loops (pfib f)) o*E
           (pequiv_pfiber _ _ (square_pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f))))^-1*)
          (((pfiber2_loops f) o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f)))^-1*)
          _ (pfib i)).
  refine (vinverse 
            ((loops_inv X) o*E
             (pfiber2_loops (pfib f)) o*E
             (pequiv_pfiber _ _ (square_pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f))))
            ((pfiber2_loops f) o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f))) _).
  refine (vconcat (f03 := loops_inv X o* pfiber2_loops (pfib f))
                  (f01 := pequiv_pfiber _ _ (square_pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f)))
                  (f23 := pfiber2_loops f)
                  (f21 := pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f)) _ _).
  - exact (square_pequiv_pfiber _ _ (square_pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f))).
  - exact (pfiber2_loops_functor f).
Defined.


(** ** Long exact sequences *)

Record LongExactSequence (k : Modality) (N : SuccStr) : Type :=
{
  les_carrier : N -> pType;
  les_fn : forall n, les_carrier n.+1 ->* les_carrier n;
  les_isexact : forall n, IsExact k (les_fn n.+1) (les_fn n)
}.

Coercion les_carrier : LongExactSequence >-> Funclass.
Arguments les_fn {k N} S n : rename.
Global Existing Instance les_isexact.

(** Long exact sequences are preserved by truncation. *)
Definition trunc_les `{Univalence} (k : trunc_index) {N : SuccStr}
           (S : LongExactSequence oo N)
  : LongExactSequence (Tr k) N
  := Build_LongExactSequence
       (Tr k) N (fun n => pTr k.+1 (S n))
       (fun n => ptr_functor k.+1 (les_fn S n)) _.


(** ** LES of loop spaces and homotopy groups *)

Definition loops_carrier (F X Y : pType) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Empty_ind _ x
  | (n, inl (inl (inr tt))) => iterated_loops n Y
  | (n, inl (inr tt)) => iterated_loops n X
  | (n, inr tt) => iterated_loops n F
  end.

(** Starting from a fiber sequence, we can obtain a long oo-exact sequence of loop spaces. *)
Definition loops_les {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : LongExactSequence oo (N3).
Proof.
  srefine (Build_LongExactSequence oo (N3) (loops_carrier F X Y) _ _).
  all:intros [n [[[[]|[]]|[]]|[]]]; cbn.
  { exact (iterated_loops_functor n f). }
  { exact (iterated_loops_functor n i). }
  { exact (connecting_map (iterated_loops_functor n i)
                          (iterated_loops_functor n f)). }
  all:exact _.
Defined.

(** And from that, a long exact sequence of homotopy groups (though for now it is just a sequence of pointed sets). *)
Definition Pi_les `{Univalence} {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : LongExactSequence (Tr (-1)) (N3)
  := trunc_les (-1) (loops_les i f).
