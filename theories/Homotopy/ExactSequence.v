From HoTT Require Import Basics Types.
Require Import SuccessorStructure.
From HoTT.WildCat Require Import Core PointedCat Square Equiv.
From HoTT.Pointed Require Import Core pMap pEquiv pFiber pTrunc Loops.
Require Import Modalities.Identity Modalities.Descent.
Require Import Truncations.
Require Import HFiber.
Require Import ObjectClassifier.

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
  - exact (fun x => (i x; cx x)).
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
  - reflexivity.
  - cbn. rewrite ap_pr1_path_sigma; hott_simpl.
Defined.

(** Truncation preserves complexes. *)
Definition iscomplex_ptr (n : trunc_index) {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (fmap (pTr n) i) (fmap (pTr n) f).
Proof.
  refine ((fmap_comp (pTr n) i f)^* @* _).
  refine (_ @* ptr_functor_pconst n).
  tapply (fmap2 (pTr _)); assumption.
Defined.

(** Loop spaces preserve complexes. *)
Definition iscomplex_loops {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (fmap loops i) (fmap loops f).
Proof.
  refine ((fmap_comp loops i f)^$ $@ _ $@ fmap_zero_morphism _).
  tapply (fmap2 loops); assumption.
Defined.

Definition iscomplex_iterated_loops {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f) (n : nat)
  : IsComplex (fmap (iterated_loops n) i) (fmap (iterated_loops n) f).
Proof.
  induction n as [|n IHn]; [ exact cx | ].
  apply iscomplex_loops; assumption.
Defined.

(** Passage across homotopies preserves complexes. *)
Definition iscomplex_homotopic_i {F X Y : pType}
  {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex i' f := pmap_postwhisker f ii @* cx.

Definition iscomplex_homotopic_f {F X Y : pType}
  (i : F ->* X) {f f' : X ->* Y} (ff : f' ==* f) (cx : IsComplex i f)
  : IsComplex i f'
  := pmap_prewhisker i ff @* cx.

Definition iscomplex_cancelL {F X Y Y' : pType}
  (i : F ->* X) (f : X ->* Y) (e : Y <~>* Y') (cx : IsComplex i (e o* f))
  : IsComplex i f.
Proof.
  refine (_ @* precompose_pconst e^-1*).
  refine ((compose_V_hh e (f o* i))^$ $@ _).
  refine (cat_postwhisker e^-1* _).
  refine ((cat_assoc _ _ _)^$ $@ _).
  exact cx.
Defined.

(** And likewise passage across squares with equivalences *)
Definition iscomplex_equiv_i {F F' X X' Y : pType}
  (i : F ->* X) (i' : F' ->* X')
  (g : F' <~>* F) (h : X' <~>* X) (p : h o* i' ==* i o* g)
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

(** A special version with only an equivalence on the fiber. *)
Definition iscomplex_equiv_fiber {F F' X Y : pType}
  (i : F ->* X) (f : X ->* Y) (phi : F' <~>* F)
  `{cx : IsComplex i f}
  : IsComplex (i o* phi) f.
Proof.
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker _ cx @* _).
  apply postcompose_pconst.
Defined.

(** Any pointed map induces a trivial complex. *)
Definition iscomplex_trivial {X Y : pType} (f : X ->* Y)
  : IsComplex (@pconst pUnit X) f.
Proof.
  srapply Build_pHomotopy.
  - intro x; cbn.
    exact (point_eq f).
  - cbn; symmetry.
    exact (concat_p1 _ @ concat_1p _).
Defined.

(** If [Y] is a set, then [IsComplex] is an [HProp]. *)
Instance ishprop_iscomplex_hset `{Funext} {F X Y : pType} `{IsHSet Y}
  (i : F ->* X) (f : X ->* Y)
  : IsHProp (IsComplex i f) := _.

(** ** Very short exact sequences and fiber sequences *)

(** A complex is [n]-exact if the induced map [cxfib] is [n]-connected.  *)
Cumulative Class IsExact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y) :=
{
  cx_isexact : IsComplex i f ;
  conn_map_isexact :: IsConnMap n (cxfib cx_isexact)
}.

Definition issig_isexact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y)
  : _ <~> IsExact n i f := ltac:(issig).

(** If [Y] is a set, then [IsExact] is an [HProp]. *)
Instance ishprop_isexact_hset `{Univalence} {F X Y : pType} `{IsHSet Y}
  (n : Modality) (i : F ->* X) (f : X ->* Y)
  : IsHProp (IsExact n i f).
Proof.
  rapply (transport (fun A => IsHProp A) (x := { cx : IsComplex i f & IsConnMap n (cxfib cx) })).
  2: exact _.
  apply path_universe_uncurried; issig.
Defined.

(** With exactness we can choose preimages. *)
Lemma isexact_preimage (O : Modality) {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact O _ _ _ i f}
  (x : X) (p : f x = point Y)
  : O (hfiber i x).
Proof.
  rapply (O_functor O (A:=hfiber (cxfib cx_isexact) (x; p))).
  - intros [z q].
    exact (z; ap pr1 q).
  - apply center, conn_map_isexact.
Defined.

(** Bundled version of the above. *)
Lemma isexact_preimage_hfiber (O : Modality) {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact O _ _ _ i f}
  (x : hfiber f pt)
  : O (hfiber i x.1).
Proof.
  srapply isexact_preimage; exact x.2.
Defined.

(** If the base is contractible, then [i] is [O]-connected. *)
Definition isconnmap_O_isexact_base_contr (O : Modality@{u}) {F X Y : pType}
  `{Contr Y} (i : F ->* X) (f : X ->* Y)
  `{IsExact@{_ _ u u u} O _ _ _ i f}
  : IsConnMap O i
  := conn_map_compose@{u _ u _} O (cxfib@{u u _ _} cx_isexact) pr1.

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
  pose (e := equiv_hfiber_homotopic _ _ ff pt).
  nrefine (cancelL_isequiv_conn_map n _ e).
  1: apply equiv_isequiv.
  refine (conn_map_homotopic n (cxfib (cx_isexact)) _ _ _).
  intro u. simpl. srapply path_hfiber.
  1: reflexivity.
  exact (concat_1p _ @ concat_V_pp _ _)^.
Defined.

(** And also passage across squares with equivalences. *)
Definition isexact_equiv_i n  {F F' X X' Y : pType}
  (i : F ->* X) (i' : F' ->* X')
  (g : F' <~>* F) (h : X' <~>* X) (p : h o* i' ==* i o* g)
  (f : X ->* Y) `{IsExact n F X Y i f}
  : IsExact n i' (f o* h).
Proof.
  exists (iscomplex_equiv_i i i' g h p f cx_isexact); cbn.
  snrefine (cancelL_equiv_conn_map n (C := pfiber f) _ _).
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

(** In particular, we can transfer exactness across equivalences of the total space. *)
Definition moveL_isexact_equiv n {F X X' Y : pType}
  (i : F ->* X) (f : X' ->* Y) (phi : X <~>* X')
  `{IsExact n _ _ _ (phi o* i) f}
  : IsExact n i (f o* phi).
Proof.
  rapply (isexact_equiv_i _ _ _ pequiv_pmap_idmap phi); cbn.
  exact (pmap_precompose_idmap _)^*.
Defined.

(** Similarly, we can cancel equivalences on the fiber. *)
Definition isexact_equiv_fiber n {F F' X Y : pType}
  (i : F ->* X) (f : X ->* Y) (phi : F' <~>* F)
  `{E : IsExact n _ _ _ i f}
  : IsExact n (i o* phi) f.
Proof.
  snapply Build_IsExact.
  1: apply iscomplex_equiv_fiber, cx_isexact.
  apply (conn_map_homotopic _ (cxfib cx_isexact o* phi)).
  { intro x; cbn.
    by rewrite concat_p1, concat_1p. }
  exact _.
Defined.

(** An equivalence of short sequences preserves exactness. *)
Definition isexact_square_if n  {F F' X X' Y Y' : pType}
  {i : F ->* X} {i' : F' ->* X'}
  {f : X ->* Y} {f' : X' ->* Y'}
  (g : F' <~>* F) (h : X' <~>* X) (k : Y' <~>* Y)
  (p : h o* i' ==* i o* g) (q : k o* f' ==* f o* h)
  `{IsExact n F X Y i f}
  : IsExact n i' f'.
Proof.
  pose (I := isexact_equiv_i n i i' g h p f).
  pose (I2 := isexact_homotopic_f n i' q).
  exists (iscomplex_cancelL i' f' k cx_isexact).
  epose (e := (pequiv_pfiber pequiv_pmap_idmap k (pmap_precompose_idmap (k o* f'))^*
    : pfiber f' <~>* pfiber (k o* f'))).
  nrefine (cancelL_isequiv_conn_map n _ e).
  1: apply pointed_isequiv.
  refine (conn_map_homotopic n (cxfib (cx_isexact)) _ _ _).
  intro u. srapply path_hfiber.
  { reflexivity. }
  cbn. unfold moveR_equiv_V. rewrite !concat_1p, !concat_p1, ap_pp_p, ap_pp, (ap_pp k _ (eissect k (point Y'))), ap_V, <- !eisadj. 
  rewrite <- !ap_compose, concat_pp_p. 
  rewrite (concat_A1p (eisretr k)), concat_pV_p.
  rewrite (concat_A1p (eisretr k)), concat_V_pp. reflexivity.
Defined.

(** If a complex [F -> E -> B] is [O]-exact, the map [F -> B] is [O]-local, and path types in [Y] are [O]-local, then the induced map [cxfib] is an equivalence. *)
Instance isequiv_cxfib {O : Modality} {F X Y : pType} {i : F ->* X} {f : X ->* Y}
  `{forall y y' : Y, In O (y = y')} `{MapIn O _ _ i} (ex : IsExact O i f)
  : IsEquiv (cxfib cx_isexact).
Proof.
  rapply isequiv_conn_ino_map.
  1: apply ex.
  rapply (cancelL_mapinO _ _ pr1).
Defined.

Definition equiv_cxfib {O : Modality} {F X Y : pType} {i : F ->* X} {f : X ->* Y}
  `{forall y y' : Y, In O (y = y')} `{MapIn O _ _ i} (ex : IsExact O i f)
  : F <~>* pfiber f
  := Build_pEquiv _ (isequiv_cxfib ex).

Proposition equiv_cxfib_beta {F X Y : pType} {i : F ->* X} {f : X ->* Y}
  `{forall y y' : Y, In O (y = y')} `{MapIn O _ _ i} (ex : IsExact O i f)
  : i o pequiv_inverse (equiv_cxfib ex) == pfib _.
Proof.
  rapply equiv_ind.
  1: exact (isequiv_cxfib ex).
  intro x.
  exact (ap (fun g => i g) (eissect _ x)).
Defined.

(** A purely exact sequence is [O]-exact for any modality [O]. *)
Definition isexact_purely_O {O : Modality} {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely _ _ _ i f}
  : IsExact O i f.
Proof.
  srapply Build_IsExact.
  1: exact cx_isexact.
  exact _.
Defined.

(** When [n] is the identity modality [purely], so that [cxfib] is an equivalence, we get simply a fiber sequence.  In particular, the fiber of a given map yields an purely-exact sequence. *)

Definition iscomplex_pfib {X Y} (f : X ->* Y)
  : IsComplex (pfib f) f.
Proof.
  srapply Build_pHomotopy.
  - intros [x p]; exact p.
  - cbn. exact (concat_p1 _ @ concat_1p _)^.
Defined.

Instance isexact_pfib {X Y} (f : X ->* Y)
  : IsExact purely (pfib f) f.
Proof.
  exists (iscomplex_pfib f).
  exact _.
Defined.

(** Fiber sequences can alternatively be defined as an equivalence to the fiber of some map. *)
Definition FiberSeq (F X Y : pType) := { f : X ->* Y & F <~>* pfiber f }.

Definition i_fiberseq {F X Y} (fs : FiberSeq F X Y)
  : F ->* X
  := pfib fs.1 o* fs.2.

Instance isexact_purely_fiberseq {F X Y : pType} (fs : FiberSeq F X Y)
  : IsExact purely (i_fiberseq fs) fs.1.
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
  `{IsExact purely F X Y i f}
  : F <~>* pfiber f
  := Build_pEquiv (cxfib cx_isexact) _.

Definition fiberseq_isexact_purely {F X Y : pType} (i : F ->* X) (f : X ->* Y)
  `{IsExact purely F X Y i f} : FiberSeq F X Y
  := (f; pequiv_cxfib).

(** It's easier to show that [loops] preserves fiber sequences than that it preserves purely-exact sequences. *)
Definition fiberseq_loops {F X Y} (fs : FiberSeq F X Y)
  : FiberSeq (loops F) (loops X) (loops Y).
Proof.
  (** TODO: doesn't work?! *)
(*   exists (fmap loops fs.1). *)
  refine (fmap loops fs.1; _).
  refine (_ o*E emap loops fs.2).
  exact (pfiber_fmap_loops fs.1)^-1*.
Defined.

(** Now we can deduce that [loops] preserves purely-exact sequences. The hardest part is modifying the first map back to [fmap loops i]. *)
Instance isexact_loops {F X Y} (i : F ->* X) (f : X ->* Y)
  `{IsExact purely F X Y i f}
  : IsExact purely (fmap loops i) (fmap loops f).
Proof.
  refine (@isexact_homotopic_i purely _ _ _ _ (fmap loops i) _ (fmap loops f)
    (isexact_purely_fiberseq (fiberseq_loops (fiberseq_isexact_purely i f)))).
  transitivity (fmap loops (pfib f) o* fmap loops (cxfib cx_isexact)).
  - refine (_ @* fmap_comp loops _ _).
    tapply (fmap2 loops).
    symmetry; apply pfib_cxfib.
  - refine (_ @* pmap_compose_assoc _ _ _).
    refine (pmap_prewhisker (fmap loops (cxfib cx_isexact)) _).
    apply moveR_pequiv_fV.
    apply pr1_pfiber_fmap_loops.
Defined.

Instance isexact_iterated_loops {F X Y}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f} (n : nat)
  : IsExact purely (fmap (iterated_loops n) i) (fmap (iterated_loops n) f).
Proof.
  induction n as [|n IHn]; [ assumption | apply isexact_loops; assumption ].
Defined.

(** (n.+1)-truncation preserves n-exactness. *)
Instance isexact_ptr `{Univalence} (n : trunc_index)
  {F X Y : pType} (i : F ->* X) (f : X ->* Y)
  `{IsExact (Tr n) F X Y i f}
  : IsExact (Tr n) (fmap (pTr n.+1) i) (fmap (pTr n.+1) f).
Proof.
  exists (iscomplex_ptr n.+1 i f cx_isexact).
  srefine (cancelR_conn_map (Tr n) (@tr n.+1 F) 
    (@cxfib _ _ _ (fmap (pTr n.+1) i) (fmap (pTr n.+1) f) _)).
  { intros x; rapply isconnected_pred. }
  napply conn_map_homotopic.
  2:napply (conn_map_compose _ (cxfib _)
               (functor_hfiber (fun y => (to_O_natural (Tr n.+1) f y)^)
                               (point Y))).
  3:pose @O_lex_leq_Tr; rapply (OO_conn_map_functor_hfiber_to_O).
  - intros x; refine (path_sigma' _ 1 _); cbn.
    (* This is even simpler than it looks, because for truncations [to_O_natural n.+1 := 1], [to n.+1 := tr], and [cx_const := H]. *)
    exact (1 @@ (concat_p1 _)^).
  - exact _.
Defined.

(** In particular, (n.+1)-truncation takes fiber sequences to n-exact ones. *)
Instance isexact_ptr_purely `{Univalence} (n : trunc_index)
  {F X Y : pType} (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : IsExact (Tr n) (fmap (pTr n.+1) i) (fmap (pTr n.+1) f).
Proof.
  rapply isexact_ptr.
  exists cx_isexact.
  intros z; apply isconnected_contr.
  exact (conn_map_isexact (f := f) (i := i) z).
Defined.

(** ** Connecting maps *)

(** It's useful to see [pfib_cxfib] as a degenerate square. *)
Definition square_pfib_pequiv_cxfib {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : pequiv_pmap_idmap o* i ==* pfib f o* pequiv_cxfib.
Proof.
  refine (pmap_postcompose_idmap _ @* _).
  symmetry; apply pfib_cxfib.
Defined.

(** The connecting maps for the long exact sequence of loop spaces, defined as an extension to a fiber sequence. *)
Definition connect_fiberseq {F X Y}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : FiberSeq (loops Y) F X.
Proof.
  exists i.
  exact (((pfiber2_loops f) o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib i f)))^-1*).
Defined.

Definition connecting_map {F X Y}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : loops Y ->* F
  := i_fiberseq (connect_fiberseq i f).

Instance isexact_connect_R {F X Y}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : IsExact purely (fmap loops f) (connecting_map i f).
Proof.
  refine (isexact_equiv_i (Y := F) purely
          (pfib (pfib i)) (fmap loops f)
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
  - exact (pfiber2_fmap_loops f).
Defined.

(** The connecting map associated to a pointed family. *)
Definition connecting_map_family {Y : pType} (P : pFam Y)
  : loops Y ->* [P pt, dpoint P].
Proof.
  srapply Build_pMap.
  - intro l.
    apply (transport P l).
    apply P.
  - reflexivity.
Defined.

(** ** Long exact sequences *)

Record LongExactSequence (k : Modality) (N : SuccStr) : Type :=
{
  les_carrier : N -> pType;
  les_fn : forall n, les_carrier n.+1 ->* les_carrier n;
  les_isexact :: forall n, IsExact k (les_fn n.+1) (les_fn n)
}.

Coercion les_carrier : LongExactSequence >-> Funclass.
Arguments les_fn {k N} S n : rename.

(** Long exact sequences are preserved by truncation. *)
Definition trunc_les `{Univalence} (k : trunc_index) {N : SuccStr}
  (S : LongExactSequence purely N)
  : LongExactSequence (Tr k) N
  := Build_LongExactSequence
       (Tr k) N (fun n => pTr k.+1 (S n))
       (fun n => fmap (pTr k.+1) (les_fn S n)) _.


(** ** LES of loop spaces and homotopy groups *)

Definition loops_carrier (F X Y : pType) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Empty_ind _ x
  | (n, inl (inl (inr tt))) => iterated_loops n Y
  | (n, inl (inr tt)) => iterated_loops n X
  | (n, inr tt) => iterated_loops n F
  end.

(** Starting from a fiber sequence, we can obtain a long purely-exact sequence of loop spaces. *)
Definition loops_les {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : LongExactSequence purely (N3).
Proof.
  srefine (Build_LongExactSequence purely (N3) (loops_carrier F X Y) _ _).
  all:intros [n [[[[]|[]]|[]]|[]]]; cbn.
  { exact (fmap (iterated_loops n) f). }
  { exact (fmap (iterated_loops n) i). }
  { exact (connecting_map (fmap (iterated_loops n) i)
                          (fmap (iterated_loops n) f)). }
  all:exact _.
Defined.

(** And from that, a long exact sequence of homotopy groups (though for now it is just a sequence of pointed sets). *)
Definition Pi_les `{Univalence} {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely F X Y i f}
  : LongExactSequence (Tr (-1)) (N3)
  := trunc_les (-1) (loops_les i f).

(** * Classifying fiber sequences *)

(** Fiber sequences correspond to pointed maps into the universe. *)
Definition classify_fiberseq `{Univalence} {Y F : pType@{u}}
  : (Y ->* [Type@{u}, F]) <~> { X : pType@{u} & FiberSeq F X Y }.
Proof.
  refine (_ oE _).
  (** To apply [equiv_sigma_pfibration] we need to invert the equivalence on the fiber. *)
  { do 2 (rapply equiv_functor_sigma_id; intro).
    exact equiv_pequiv_inverse. }
  exact ((equiv_sigma_assoc _ _)^-1 oE equiv_sigma_pfibration).
Defined.
