

Definition nat_caset :=
fun (P : nat -> Type) (f : P 0)
  (f0 : forall n : nat, P (S n)) =>
fix F (n : nat) {struct n} : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | S n0 => f0 n0
  end.


(* Scheme nat_caset := Elimination for nat Sort Type. *)
(* Print nat_caset. *)



Inductive nat := O | S (m:nat).








Scheme Case for list Sort Prop.
Scheme Case for list Sort Type.
Print list_case_nodep.
Scheme Elimination for list Sort Prop.
Scheme Elimination for list Sort Type.
Print list_case.
Print list_caset.
Scheme Minimality for list Sort Prop.
Scheme Induction for list Sort Prop.
Scheme Minimality for list Sort Type.
Scheme Induction for list Sort Type.

Print list_rect.
Print list_caset.
Print list_ind.
Print list_case.

Print list_case_nodep.
Print list_ind_nodep.
Print list_caset_nodep.
Print list_rect_nodep.

Scheme Case for nat Sort Prop.
Print nat_case_nodep.
Print nat_case.
Scheme Elimination for nat Sort Prop.
Print nat_case.



Scheme Elimination for le Sort Prop.
Scheme Induction for le Sort Prop.

Print le_case_dep.
Print le_ind_dep.

Test Nonrecursive Elimination Schemes.
Set Nonrecursive Elimination Schemes.
Test Nonrecursive Elimination Schemes.



Inductive roseTree := tree (xs:list roseTree).
Print roseTree_rect.
(* Scheme Induction for roseTree Sort Type. *)






Inductive nat := O | S (n:nat).
Inductive nat2 := O2 | S2 (n:nat2).
Print nat_rec.

Scheme  for nat Sort Prop.


Scheme Equality for nat Sort Prop.
Scheme Induction for nat Sort Prop.
Scheme Rewrite for nat Sort Prop.
Case Analysis Scheme for nat Sort Prop.
