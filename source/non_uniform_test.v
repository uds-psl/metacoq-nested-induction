(** tests the computes non-uniform parameter **)

Load non_uniform.


Compute (countOfCtor 1 100 (tApp (tRel 1) (tRel 0))).
Compute (countOfCtor 1 100 (tApp (tRel 100) (tApp (tRel 1) (tRel 0)))).
Compute (countOfCtor 1 100 (tApp (tVar "Not relevant"%string) (tApp (tRel 1) (tRel 0)))).
Compute (countOfCtor 1 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tRel 1) (tRel 0)))).
(* Compute (countOfCtor 1 1 (tApp (tApp (tRel 1) (tRel 0)) (tVar "N"%string))). *)
Compute (countOfCtor 2 2 (tApp (tApp (tRel 2) (tRel 1)) (tVar "N"%string))).
Compute (countOfCtor 2 100 (tApp (tApp (tRel 2) (tRel 1)) (tVar "N"%string))).
Compute (countOfCtor 2 100 (tApp (tApp (tRel 2) (tRel 0)) (tVar "N"%string))).
Compute (countOfCtor 2 100 (tApp (tApp (tRel 2) (tRel 1)) (tRel 0))).
Compute (countOfCtor 2 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 2) (tRel 1)) (tRel 0)))).
Compute (countOfCtor 2 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 2) (tRel 42)) (tRel 0)))).
Compute (countOfCtor 2 2 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 2) (tRel 42)) (tRel 1)))). (* Problem *)
Compute (countOfCtor 2 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 2) (tRel 1)) (tRel 42)))).
Compute (countOfCtor 1 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 1) (tRel 42)) (tRel 42)))).
Compute (countOfCtor 1 100 (tApp
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                              (tApp (tApp (tRel 1) (tVar "N"%string)) (tVar "N"%string)))).

Compute (countOfCtor 1 100
(tApp
                                             (tInd
                                                {|
                                                inductive_mind := "Coq.Init.Datatypes.list";
                                                inductive_ind := 0 |} [])
                                             (tApp(tApp (tRel 1)
                                                (* (tApp *)
                                                (*    (tConstruct *)
                                                (*       {| *)
                                                (*       inductive_mind := "Coq.Init.Datatypes.nat"; *)
                                                (*       inductive_ind := 0 |} 1 []) (tRel 0)) *)
                                                (tConstruct
                                                  {|
                                                  inductive_mind := "Coq.Init.Datatypes.nat";
                                                  inductive_ind := 0 |} 0 [])
                                                  )
                                                (tConstruct
                                                  {|
                                                  inductive_mind := "Coq.Init.Datatypes.nat";
                                                  inductive_ind := 0 |} 0 [])
))
        ).



MetaCoq Run (getP <% nat %>). (* 0 *)
MetaCoq Run (getP <% list %>). (* 1 *)
MetaCoq Run (getP <% VectorDef.t %>). (* 1 *)
MetaCoq Run (getP <% le %>). (* 1 *)
MetaCoq Run (getP <% Acc %>). (* 2 *)


Definition t1 := Ast.tProd (nNamed "n"%string)
   (Ast.tInd
      {|
      inductive_mind := "Coq.Init.Datatypes.nat";
      inductive_ind := 0 |} [])
   (Ast.tApp (Ast.tRel 1)
      [Ast.tRel 0; Ast.tRel 0]).
Definition t2 := Ast.tProd (nNamed "n"%string)
    (Ast.tInd
       {|
       inductive_mind := "Coq.Init.Datatypes.nat";
       inductive_ind := 0 |} [])
    (Ast.tProd (nNamed "m"%string)
       (Ast.tInd
          {|
          inductive_mind := "Coq.Init.Datatypes.nat";
          inductive_ind := 0 |} [])
       (Ast.tProd nAnon
          (Ast.tApp 
             (Ast.tRel 2)
             [Ast.tRel 1; Ast.tRel 0])
          (Ast.tApp 
             (Ast.tRel 3)
             [Ast.tRel 2;
             Ast.tApp
               (Ast.tConstruct
               {|
               inductive_mind := "Coq.Init.Datatypes.nat";
               inductive_ind := 0 |} 1 [])
               [
               Ast.tRel 1]]))).

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Compute (countOfCtor 0 2 (trans t1)).
Compute (countOfCtor 0 2 (trans t2)).

MetaCoq Run (tmQuoteInductive ("le"%string) >>= tmPrint).

Definition vt1 :=
                                     Ast.tProd (nNamed "A"%string)
                                       (Ast.tSort
                                          (Universe.from_kernel_repr
                                             (Level.Level
                                                "Coq.Vectors.VectorDef.4",
                                             false) []))
                                       (Ast.tApp (Ast.tRel 1)
                                          [Ast.tRel 0;
                                          Ast.tConstruct
                                            {|
                                            inductive_mind := "Coq.Init.Datatypes.nat";
                                            inductive_ind := 0 |} 0 []]).

Definition vt2 :=
                                    Ast.tProd (nNamed "A"%string)
                                      (Ast.tSort
                                         (Universe.from_kernel_repr
                                            (Level.Level
                                               "Coq.Vectors.VectorDef.4",
                                            false) []))
                                      (Ast.tProd (nNamed "h"%string)
                                         (Ast.tRel 0)
                                         (Ast.tProd 
                                            (nNamed "n"%string)
                                            (Ast.tInd
                                               {|
                                               inductive_mind := "Coq.Init.Datatypes.nat";
                                               inductive_ind := 0 |} [])
                                            (Ast.tProd nAnon
                                               (Ast.tApp 
                                                 (Ast.tRel 3)
                                                 [Ast.tRel 2; Ast.tRel 0])
                                               (Ast.tApp 
                                                 (Ast.tRel 4)
                                                 [
                                                 Ast.tRel 3;
                                                 Ast.tApp
                                                 (Ast.tConstruct
                                                 {|
                                                 inductive_mind := "Coq.Init.Datatypes.nat";
                                                 inductive_ind := 0 |} 1 [])
                                                 [Ast.tRel 1]])))).

MetaCoq Run (tmQuoteInductive ("VectorDef.t"%string) >>= tmPrint).

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Compute (countOfCtor 0 2 (trans vt1)).
Compute (countOfCtor 0 2 (trans vt2)).


Print Coq.Init.Logic.eq_refl.

Inductive dep (X:Type) : nat -> forall (x:X), x=x -> Prop :=
| dep0 y : dep X 0 y (@Coq.Init.Logic.eq_refl _ y).
Inductive G (f:nat->bool) : nat -> Prop :=
  GI : forall n, (f n = false -> G f (S n)) -> G f n.
Inductive G3 (f:nat->bool) (n:nat) : Prop :=
  G3I : (f n = false -> G3 f (S n)) -> G3 f n.
Inductive G2 (f:nat->bool) : nat -> Prop :=
  G2I1 : forall n, (f n = false -> G2 f (S n)) -> (f n = true -> G2 f (S (S n))) -> G2 f n
| G2I2 : forall n, (f n = false -> G2 f (S n)) -> G2 f n.


MetaCoq Run (getP <% dep %>).
MetaCoq Run (getP <% G %>).
MetaCoq Run (getP <% G3 %>).
MetaCoq Run (getP <% G2 %>).


Inductive roseTreePI8 (n : nat) : nat -> Set :=  treePI8 : list (roseTreePI8 (S n) 0) -> roseTreePI8 n 1.

MetaCoq Run (tmQuoteInductive ("roseTreePI8"%string) >>= tmPrint).

MetaCoq Run (getP <% roseTreePI8 %>).
