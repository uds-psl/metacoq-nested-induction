
(** examples for nested types for testing **)

Inductive rtree A : Type :=
| Leaf (a:A)
| Node (l:list (rtree A)).

(* param, indices, dependent *)
Inductive roseTree := tree (xs:list roseTree).
Inductive roseTree2 X := tree2 (l:X) (xs:list (roseTree2 X)).
Inductive roseTree3 := tree3 (xs:list roseTree3) | node3 : nat -> roseTree3.
Inductive roseTree4 := tree4 (xs:0=0 -> list roseTree4).
Inductive roseTree5 : nat -> Prop :=
  tree5 (xs:list (roseTree5 1)): roseTree5 0.
Inductive roseTree6 : nat -> Type :=
  tree6 (xs:list (roseTree6 1)): roseTree6 0.

(* parameter and indices tests *)
Inductive roseTreePI1 (X Y:Type) : Type :=
  treePI1 (xs : list (roseTreePI1 X Y)).
Inductive roseTreePI2 : nat -> Type :=
  treePI2 : roseTreePI2 0 -> list (roseTreePI2 1)
            -> list (roseTreePI2 2)
            -> roseTreePI2 3.
Inductive roseTreePI3 : nat -> Type :=
  treePI3 n: roseTreePI3 n -> list (roseTreePI3 n)
            -> list (roseTreePI3 1)
            -> roseTreePI3 (S n).
Inductive roseTreePI4 : nat -> Type :=
  treePI4 n: list (roseTreePI4 n)
            -> roseTreePI4 (S n).
Inductive roseTreePI5 : nat -> bool -> Type :=
  treePI5 n: roseTreePI5 1 false ->
             list (roseTreePI5 (S n) true) ->
             roseTreePI5 n false.
Inductive roseTreePI6 : nat -> bool -> Type :=
  treePI6 : list (roseTreePI6 1 false) ->
            roseTreePI6 0 true.
Inductive roseTreePI7 (n:nat) : nat -> Type :=
  treePI7 : list (roseTreePI7 n 0) ->
            roseTreePI7 n n.
Inductive roseTreePI8 (n:nat) : nat -> Type :=
  treePI8 : list (roseTreePI8 (S n) 0) ->
            roseTreePI8 n 1.

(* multiple nested *)
Inductive roseTreeNN1 :=
  treeNN1 (a:roseTreeNN1) (b:list roseTreeNN1).
Inductive roseTreeNN2 :=
  treeNN2 (a:list roseTreeNN2) (b:list roseTreeNN2).
Inductive roseTreeNN3 :=
  treeNN3 (a:roseTreeNN3*nat).
Inductive roseTreeNN4 :=
  treeNN4 (a:nat*roseTreeNN4).
Inductive roseTreeNN5 :=
  treeNN5 (a:roseTreeNN5*roseTreeNN5).
Require Vector.
Print Vector.t.
Print nil.
Inductive roseTreeNN6 :=
  treeNN6 n (xs:Vector.t roseTreeNN6 n).
Inductive roseTreeNN7 :=
  treeNN7 (a:roseTreeNN7*(nat -> nat)).

(* deeply nested test *)
Inductive roseTreeDN1 :=
  treeDN1 (a:list(roseTreeDN1*nat)).
Inductive roseTreeDN2 :=
  treeDN2 (a:list(nat*roseTreeDN2)).
Inductive roseTreeDN3 :=
  treeDN3 (a:list(list roseTreeDN3)).
Inductive roseTreeDN4 :=
  treeDN4 (a:list(list(list roseTreeDN4))).
Inductive roseTreeDN5 :=
  treeDN5 (a:list(nat*(list roseTreeDN4))).
Inductive roseTreeDN6 :=
  treeDN6 (a:list(roseTreeDN6*(list roseTreeDN6))).
Inductive roseTreeDN7 :=
  treeDN7 (a:list(nat*(list roseTreeDN7))).

Inductive containerInd (n:nat) : Type -> Type :=
| c10 : containerInd n bool
(* | c1 X : containerInd n X -> containerInd n (forall (m:nat), X). *)
(* | c2 X : containerInd n (forall (Y:Type), X) -> containerInd n X. *)
(* | c2 X : containerInd n nat -> containerInd n X. *)
| c12 : containerInd n nat -> containerInd n nat.

Inductive containerInd2 (X:Type) : Type -> Type :=
  c20 : containerInd2 X bool.

Inductive containerInd3 (X:Type -> Type) : Type :=
  c3 : containerInd3 X.

(* test for typ in index positiion *)
Inductive roseTreeO1 :=
  treeO1 (x:containerInd2 roseTreeO1 nat).
(* TODO tests for is_* functions *)
Inductive roseTreeO2 (X:Type) :=
  treeO2 (x:X) (xs:list X).
Inductive roseTreeO3 (X:Type) :=
  treeO3 (x:X) (xs:list X) (xxs:roseTreeO3 X) (xsxs: list (roseTreeO3 X)).
(* test for pseudo type argument *)
(* TODO: how should the induction predicate look like *)
Inductive roseTreeO4 :=
  treeO4 (x:containerInd3 list).
Inductive roseTreeO5 :=
  treeO5 (x:containerInd3 (prod roseTreeO5)).
Inductive roseTreeO6 :=
  treeO6 (x:containerInd3 (prod (list roseTreeO6))).
Inductive roseTreeO7 :=
  treeO7 (n:nat) (x:prod (Vector.t bool n) roseTreeO7).
Inductive roseTreeO8 :=
  treeO8 (X:Type) (x:prod (Vector.t X 0) roseTreeO8).
Inductive roseTreeO9 :=
  treeO9 (n:nat) (X:Type) (x:prod (Vector.t X n) roseTreeO9).
Inductive roseTreeO10 :=
  treeO10 (n:nat) (x:prod (Vector.t roseTreeO10 n) roseTreeO10).
Inductive roseTreeO11 :=
  treeO11 (x:list (0=0 -> roseTreeO11)).

(* Print Acc. *)
(* Inductive roseTreeO12 := *)
(*   | baseO12: roseTreeO12 *)
(*   | treeO12 (x:Acc roseTreeO12 (fun _ _ => True) baseO12). *)


Inductive containerInd4 (b:bool) (X:Type) (n:nat) : Type :=
  c4 : containerInd4 b X n.

Inductive roseTreeO13 :=
  treeO13 (x:containerInd4 true roseTreeO13 0).

Variable Preds : Type.
Variable pred_ar : Preds -> nat.
Variable Funcs : Type.
Variable fun_ar : Funcs -> nat.

Inductive foterm : Type :=
  | var_foterm : (nat) -> foterm
  | Func : forall (f : Funcs), Vector.t foterm (fun_ar f) -> foterm .

Inductive form : Type :=
  | Fal : form
  | Top : form
  | Pred : forall (P : Preds), Vector.t foterm (pred_ar P) -> form
  | Impl : form -> form -> form
  | Conj : form -> form -> form
  | Disj : form -> form -> form
  | All : form -> form
  | Ex : form -> form.
