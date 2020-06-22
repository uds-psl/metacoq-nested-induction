
Require Import List.
Import ListNotations.

Inductive PTree (A:Type) :=
| PLeaf (a:A)
| PNode (h:PTree (A*A)).

Print PTree_rect.

(* Inductive GForest f A :=
FEmpty
| FNode (a:A) (h:f(GForest f A)). *)

(* Inductive bush (A:Type) :=
BNil
| BCons (a:A) (h:bush (bush A)). *)

Inductive Lam (A:Type) :=
Var (a:A)
| App (h:Lam A) (h2:Lam A)
| Abs (h:Lam (option A)).

Print Lam_rect.