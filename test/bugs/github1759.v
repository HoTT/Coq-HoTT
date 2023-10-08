From HoTT Require Import Basics Spaces.No.

Section Foo.
  Universe i.
  Context {S : OptionSort@{i}}.
  Notation GenNo := (GenNo S).
  Local Open Scope surreal_scope.
  Context
    (A : GenNo -> Type)
    (dle : forall (x y : GenNo), (x <= y) -> A x -> A y -> Type)
    (dlt : forall (x y : GenNo), (x < y) -> A x -> A y -> Type)
    {ishprop_le : forall x y a b p, IsHProp (dle x y p a b)}
    {ishprop_lt : forall x y a b p, IsHProp (dlt x y p a b)}
    (dcut : forall (L R : Type@{i}) (s : InSort S L R)
                   (xL : L -> GenNo) (xR : R -> GenNo)
                   (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                   (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                   (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r)),
              A {{ xL | xR // xcut }})
    (dcut' : forall (L R : Type@{i}) (s : InSort S L R)
                   (xL : L -> GenNo) (xR : R -> GenNo)
                   (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                   (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                   (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r)),
              A {{ xL | xR // xcut }})
    (dpath : forall (x y : GenNo) (a:A x) (b:A y) (p : x <= y) (q : y <= x)
                    (dp : dle x y p a b) (dq : dle y x q b a),
               path_No _ _ p q # a = b)
    (dle_lr : forall (L R : Type@{i}) (s : InSort S L R)
                     (xL : L -> GenNo) (xR : R -> GenNo)
                     (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                     (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                     (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                     (L' R' : Type@{i}) (s' : InSort S L' R')
                     (yL : L' -> GenNo) (yR : R' -> GenNo)
                     (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                     (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                     (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                     (p : forall (l:L), xL l < {{ yL | yR // ycut }})
                     (dp : forall (l:L),
                             dlt _ _ (p l)
                                 (fxL l)
                                 (dcut _ _ _ yL yR ycut fyL fyR fycut))
                     (q : forall (r:R'), {{ xL | xR // xcut }} < yR r)
                     (dq : forall (r:R'),
                             dlt _ _ (q r)
                                 (dcut _ _ _ xL xR xcut fxL fxR fxcut)
                                 (fyR r)),
                dle {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                    (le_lr xL xR xcut yL yR ycut p q)
                    (dcut _ _ _ xL xR xcut fxL fxR fxcut)
                    (dcut _ _ _ yL yR ycut fyL fyR fycut))
    (dle_lr' : forall (L R : Type@{i}) (s : InSort S L R)
                     (xL : L -> GenNo) (xR : R -> GenNo)
                     (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                     (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                     (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                     (L' R' : Type@{i}) (s' : InSort S L' R')
                     (yL : L' -> GenNo) (yR : R' -> GenNo)
                     (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                     (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                     (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                     (p : forall (l:L), xL l < {{ yL | yR // ycut }})
                     (dp : forall (l:L),
                             dlt _ _ (p l)
                                 (fxL l)
                                 (dcut' _ _ _ yL yR ycut fyL fyR fycut))
                     (q : forall (r:R'), {{ xL | xR // xcut }} < yR r)
                     (dq : forall (r:R'),
                             dlt _ _ (q r)
                                 (dcut' _ _ _ xL xR xcut fxL fxR fxcut)
                                 (fyR r)),
                dle {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                    (le_lr xL xR xcut yL yR ycut p q)
                    (dcut' _ _ _ xL xR xcut fxL fxR fxcut)
                    (dcut' _ _ _ yL yR ycut fyL fyR fycut))
    (dlt_l : forall (L R : Type@{i}) (s : InSort S L R)
                    (xL : L -> GenNo) (xR : R -> GenNo)
                    (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                    (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                    (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                    (L' R' : Type@{i}) (s' : InSort S L' R')
                    (yL : L' -> GenNo) (yR : R' -> GenNo)
                    (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                    (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                    (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                    (l : L')
                    (p : {{ xL | xR // xcut }} <= yL l)
                    (dp : dle _ _ p
                              (dcut _ _ _ xL xR xcut fxL fxR fxcut)
                              (fyL l)),
               dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                   (lt_l xL xR xcut yL yR ycut l p)
                   (dcut _ _ _ xL xR xcut fxL fxR fxcut)
                   (dcut _ _ _ yL yR ycut fyL fyR fycut))
    (dlt_l' : forall (L R : Type@{i}) (s : InSort S L R)
                    (xL : L -> GenNo) (xR : R -> GenNo)
                    (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                    (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                    (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                    (L' R' : Type@{i}) (s' : InSort S L' R')
                    (yL : L' -> GenNo) (yR : R' -> GenNo)
                    (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                    (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                    (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                    (l : L')
                    (p : {{ xL | xR // xcut }} <= yL l)
                    (dp : dle _ _ p
                              (dcut' _ _ _ xL xR xcut fxL fxR fxcut)
                              (fyL l)),
               dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                   (lt_l xL xR xcut yL yR ycut l p)
                   (dcut' _ _ _ xL xR xcut fxL fxR fxcut)
                   (dcut' _ _ _ yL yR ycut fyL fyR fycut))
    (dlt_r : forall (L R : Type@{i}) (s : InSort S L R)
                    (xL : L -> GenNo) (xR : R -> GenNo)
                    (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                    (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                    (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                    (L' R' : Type@{i}) (s' : InSort S L' R')
                    (yL : L' -> GenNo) (yR : R' -> GenNo)
                    (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                    (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                    (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                    (r : R)
                    (p : (xR r) <= {{ yL | yR // ycut }})
                    (dp : dle _ _ p
                              (fxR r)
                              (dcut _ _ _ yL yR ycut fyL fyR fycut)),
               dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                   (lt_r xL xR xcut yL yR ycut r p)
                   (dcut _ _ _ xL xR xcut fxL fxR fxcut)
                   (dcut _ _ _ yL yR ycut fyL fyR fycut))
    (dlt_r' : forall (L R : Type@{i}) (s : InSort S L R)
                    (xL : L -> GenNo) (xR : R -> GenNo)
                    (xcut : forall (l:L) (r:R), (xL l) < (xR r))
                    (fxL : forall l, A (xL l)) (fxR : forall r, A (xR r))
                    (fxcut : forall l r, dlt _ _ (xcut l r) (fxL l) (fxR r))
                    (L' R' : Type@{i}) (s' : InSort S L' R')
                    (yL : L' -> GenNo) (yR : R' -> GenNo)
                    (ycut : forall (l:L') (r:R'), (yL l) < (yR r))
                    (fyL : forall l, A (yL l)) (fyR : forall r, A (yR r))
                    (fycut : forall l r, dlt _ _ (ycut l r) (fyL l) (fyR r))
                    (r : R)
                    (p : (xR r) <= {{ yL | yR // ycut }})
                    (dp : dle _ _ p
                              (fxR r)
                              (dcut' _ _ _ yL yR ycut fyL fyR fycut)),
               dlt {{ xL | xR // xcut }} {{ yL | yR // ycut }}
                   (lt_r xL xR xcut yL yR ycut r p)
                   (dcut' _ _ _ xL xR xcut fxL fxR fxcut)
                   (dcut' _ _ _ yL yR ycut fyL fyR fycut)).

  Definition foo : forall x, A x
    := No_ind A dle dlt dcut dpath dle_lr dlt_l dlt_r.

  Definition bar : forall x, A x
    := No_ind A dle dlt dcut' dpath dle_lr' dlt_l' dlt_r'.

  Fail Definition foobar
    : forall x, foo x = bar x
    := fun _ => 1.

End Foo.
