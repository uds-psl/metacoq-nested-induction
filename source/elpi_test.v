(** test the elpi plugin by tassi on nested inductive types **)

From elpi Require Import derive.

Elpi derive nat.
Elpi derive list.

Print list_is_list.
Print list_is_list_full. (* is proof *)
Print list_is_list_trivial.
Print list_induction.

(* Goal forall A (xs:list A), xs=nil.
Proof.
    intros A xs.
    elim xs using list_induction.
    eapply list_induction.
    induction xs using list_induction. *)

(*
Comment = could not be generated
there were many universe errors
and some principles took very look

TODO:
compare rT5 with PI2
compare PI2 with PI3
 *)
Require Import nested_datatypes.


Inductive brtree A : nat -> Type :=
| Leaf (a : A) : brtree A 0
| Node (n : nat) (l : list (brtree A n)) : brtree A (S n).

Elpi derive brtree.
Check brtree_is_brtree.
(* Check brtree_is_brtree_full. *)
(* Check brtree_is_brtree_trivial. *)
Check brtree_induction.

Print rtree.
Elpi derive rtree.
Check rtree_is_rtree.
Check rtree_is_rtree_full.
Check rtree_is_rtree_trivial.
Check rtree_induction.

Print roseTree.
Elpi derive roseTree.
Check roseTree_is_roseTree.
Check roseTree_is_roseTree_full.
Check roseTree_is_roseTree_trivial.
Check roseTree_induction.

Print roseTree2.
Elpi derive roseTree2.
Check roseTree2_is_roseTree2.
Check roseTree2_is_roseTree2_full.
Check roseTree2_is_roseTree2_trivial.
Check roseTree2_induction.

Print roseTree3.
Elpi derive roseTree3.
Check roseTree3_is_roseTree3.
Check roseTree3_is_roseTree3_full.
Check roseTree3_is_roseTree3_trivial.
Check roseTree3_induction.

Elpi derive eq.

Print roseTree4.
Elpi derive roseTree4.
Check roseTree4_is_roseTree4.
Check roseTree4_is_roseTree4_full.
(* Check roseTree4_is_roseTree4_trivial. *)
Check roseTree4_induction.

Print roseTree5.
(* Elpi derive roseTree5. *)
(* Check roseTree5_is_roseTree5. *)
(* Check roseTree5_is_roseTree5_full. *)
(* Check roseTree5_is_roseTree5_trivial. *)
(* Check roseTree5_induction. *)

(* Elpi derive le. *)

Inductive Idx : nat -> Type :=
| C_I : Idx 0.
Print Idx_ind.

Elpi derive Idx.
Check Idx_is_Idx.
(* Check Idx_is_Idx_full. *)
(* Check Idx_is_Idx_trivial. *)
Check Idx_induction.

Elpi derive bool.
Check bool_induction.

(* Print VectorDef.t.
Elpi derive VectorDef.t.
Check t_is_t.
(* Check t_is_t_full. *)
(* Check t_is_t_trivial. *)
Check t_induction. *)

Print roseTree6.
Elpi derive roseTree6.
Check roseTree6_is_roseTree6.
(* Check roseTree6_is_roseTree6_full. *)
(* Check roseTree6_is_roseTree6_trivial. *)
Check roseTree6_induction.

(* Print le. *)
(* Elpi derive le. *)

Print roseTreePI1.
Elpi derive roseTreePI1.
Check roseTreePI1_is_roseTreePI1.
Check roseTreePI1_is_roseTreePI1_full.
Check roseTreePI1_is_roseTreePI1_trivial.
Check roseTreePI1_induction.

Print roseTreePI2.
Elpi derive roseTreePI2.
Check roseTreePI2_is_roseTreePI2.
(* Check roseTreePI2_is_roseTreePI2_full. *)
(* Check roseTreePI2_is_roseTreePI2_trivial. *)
Check roseTreePI2_induction.

Print roseTreePI3.
Elpi derive roseTreePI3.
Check roseTreePI3_is_roseTreePI3.
(* Check roseTreePI3_is_roseTreePI3_full. *)
(* Check roseTreePI3_is_roseTreePI3_trivial. *)
Check roseTreePI3_induction.

Print roseTreePI4.
Elpi derive roseTreePI4.
Check roseTreePI4_is_roseTreePI4.
(* Check roseTreePI4_is_roseTreePI4_full. *)
(* Check roseTreePI4_is_roseTreePI4_trivial. *)
Check roseTreePI4_induction.



Print roseTreePI5.
Elpi derive roseTreePI5.
(* Check roseTreePI5_is_roseTreePI5. *)
(* Check roseTreePI5_is_roseTreePI5_full. *)
(* Check roseTreePI5_is_roseTreePI5_trivial. *)
Check roseTreePI5_induction.

Print roseTreePI6.
Elpi derive roseTreePI6.
(* Check roseTreePI6_is_roseTreePI6. *)
(* Check roseTreePI6_is_roseTreePI6_full. *)
(* Check roseTreePI6_is_roseTreePI6_trivial. *)
Check roseTreePI6_induction.

Print roseTreePI7.
Elpi derive roseTreePI7.
Check roseTreePI7_is_roseTreePI7.
(* Check roseTreePI7_is_roseTreePI7_full. *)
(* Check roseTreePI7_is_roseTreePI7_trivial. *)
Check roseTreePI7_induction.

Print roseTreePI8.
Elpi derive roseTreePI8.
Check roseTreePI8_is_roseTreePI8.
(* Check roseTreePI8_is_roseTreePI8_full. *)
(* Check roseTreePI8_is_roseTreePI8_trivial. *)
Check roseTreePI8_induction.

Print roseTreeNN1.
Elpi derive roseTreeNN1.
Check roseTreeNN1_is_roseTreeNN1.
Check roseTreeNN1_is_roseTreeNN1_full.
Check roseTreeNN1_is_roseTreeNN1_trivial.
Check roseTreeNN1_induction.

Print roseTreeNN2.
Elpi derive roseTreeNN2.
Check roseTreeNN2_is_roseTreeNN2.
Check roseTreeNN2_is_roseTreeNN2_full.
Check roseTreeNN2_is_roseTreeNN2_trivial.
Check roseTreeNN2_induction.

Elpi derive prod.
Print prod_is_prod.
Elpi derive VectorDef.t.
Print t_is_t.
Print t_induction.

Print roseTreeNN3.
Elpi derive roseTreeNN3.
Check roseTreeNN3_is_roseTreeNN3.
Check roseTreeNN3_is_roseTreeNN3_full.
Check roseTreeNN3_is_roseTreeNN3_trivial.
Check roseTreeNN3_induction.

Print roseTreeNN4.
Elpi derive roseTreeNN4.
Check roseTreeNN4_is_roseTreeNN4.
Check roseTreeNN4_is_roseTreeNN4_full.
Check roseTreeNN4_is_roseTreeNN4_trivial.
Check roseTreeNN4_induction.

Print roseTreeNN5.
Elpi derive roseTreeNN5.
Check roseTreeNN5_is_roseTreeNN5.
Check roseTreeNN5_is_roseTreeNN5_full.
Check roseTreeNN5_is_roseTreeNN5_trivial.
(* Check roseTreeNN5_induction. *)

Print roseTreeNN6.
Elpi derive roseTreeNN6.
Check roseTreeNN6_is_roseTreeNN6.
(* Check roseTreeNN6_is_roseTreeNN6_full. *)
(* Check roseTreeNN6_is_roseTreeNN6_trivial. *)
Check roseTreeNN6_induction.

Print roseTreeDN1.
Elpi derive roseTreeDN1.
Check roseTreeDN1_is_roseTreeDN1.
Check roseTreeDN1_is_roseTreeDN1_full.
Check roseTreeDN1_is_roseTreeDN1_trivial.
Check roseTreeDN1_induction.

Print roseTreeDN2.
Elpi derive roseTreeDN2.
Check roseTreeDN2_is_roseTreeDN2.
Check roseTreeDN2_is_roseTreeDN2_full.
Check roseTreeDN2_is_roseTreeDN2_trivial.
Check roseTreeDN2_induction.

Print roseTreeDN3.
Elpi derive roseTreeDN3.
Check roseTreeDN3_is_roseTreeDN3.
Check roseTreeDN3_is_roseTreeDN3_full.
Check roseTreeDN3_is_roseTreeDN3_trivial.
Check roseTreeDN3_induction.

Print roseTreeDN4.
(* takes a long time *)
Elpi derive roseTreeDN4.
Check roseTreeDN4_is_roseTreeDN4.
Check roseTreeDN4_is_roseTreeDN4_full.
Check roseTreeDN4_is_roseTreeDN4_trivial.
Check roseTreeDN4_induction.

Print roseTreeDN5.
Elpi derive roseTreeDN5.
Check roseTreeDN5_is_roseTreeDN5.
Check roseTreeDN5_is_roseTreeDN5_full.
Check roseTreeDN5_is_roseTreeDN5_trivial.
Check roseTreeDN5_induction.

Print roseTreeDN6.
(* takes a long time *)
Elpi derive roseTreeDN6.
Check roseTreeDN6_is_roseTreeDN6.
Check roseTreeDN6_is_roseTreeDN6_full.
Check roseTreeDN6_is_roseTreeDN6_trivial.
Check roseTreeDN6_induction.

Print containerInd.
Print containerInd2.
Print containerInd3.

Elpi derive containerInd.
Elpi derive containerInd2.
Elpi derive containerInd3.

Print roseTreeO1.
Elpi derive roseTreeO1.
(* Check roseTreeO1_is_roseTreeO1. *)
(* Check roseTreeO1_is_roseTreeO1_full. *)
(* Check roseTreeO1_is_roseTreeO1_trivial. *)
Check roseTreeO1_induction.

Print roseTreeO2.
Elpi derive roseTreeO2.
Check roseTreeO2_is_roseTreeO2.
Check roseTreeO2_is_roseTreeO2_full.
Check roseTreeO2_is_roseTreeO2_trivial.
Check roseTreeO2_induction.

Print roseTreeO3.
Elpi derive roseTreeO3.
Check roseTreeO3_is_roseTreeO3.
Check roseTreeO3_is_roseTreeO3_full.
Check roseTreeO3_is_roseTreeO3_trivial.
Check roseTreeO3_induction.

Print roseTreeO4.
Elpi derive roseTreeO4.
Check roseTreeO4_is_roseTreeO4.
(* Check roseTreeO4_is_roseTreeO4_full. *)
(* Check roseTreeO4_is_roseTreeO4_trivial. *)
Check roseTreeO4_induction.

Print roseTreeO5.
Elpi derive roseTreeO5.
Check roseTreeO5_is_roseTreeO5.
(* Check roseTreeO5_is_roseTreeO5_full. *)
(* Check roseTreeO5_is_roseTreeO5_trivial. *)
(* Check roseTreeO5_induction. *)

Print roseTreeO6.
Elpi derive roseTreeO6.
Check roseTreeO6_is_roseTreeO6.
(* Check roseTreeO6_is_roseTreeO6_full. *)
(* Check roseTreeO6_is_roseTreeO6_trivial. *)
(* Check roseTreeO6_induction. *)

Print roseTreeO7.
Elpi derive roseTreeO7.
(* Check roseTreeO7_is_roseTreeO7. *)
(* Check roseTreeO7_is_roseTreeO7_full. *)
(* Check roseTreeO7_is_roseTreeO7_trivial. *)
Check roseTreeO7_induction.

Print roseTreeO8.
Elpi derive roseTreeO8.
Check roseTreeO8_is_roseTreeO8.
(* Check roseTreeO8_is_roseTreeO8_full. *)
(* Check roseTreeO8_is_roseTreeO8_trivial. *)
(* Check roseTreeO8_induction. *)

Print roseTreeO9.
Elpi derive roseTreeO9.
Check roseTreeO9_is_roseTreeO9.
(* Check roseTreeO9_is_roseTreeO9_full. *)
(* Check roseTreeO9_is_roseTreeO9_trivial. *)
(* Check roseTreeO9_induction. *)

Print roseTreeO10.
Elpi derive roseTreeO10.
Check roseTreeO10_is_roseTreeO10.
(* Check roseTreeO10_is_roseTreeO10_full. *)
(* Check roseTreeO10_is_roseTreeO10_trivial. *)
Check roseTreeO10_induction.

(* Print Acc. *)
(* Elpi derive Acc. *)
(* Check Acc_induction. *)

Inductive outerGuard := Cog (h:nat -> outerGuard).
Inductive outNestGuard := Cong (h:nat -> list outNestGuard).
Inductive nestGuard := Cng (h:list (nat -> nestGuard)).

Elpi derive outerGuard.
Check outerGuard_induction.
Elpi derive outNestGuard.
Check outNestGuard_induction.
Elpi derive nestGuard.
(* Check nestGuard_induction. *)

Print roseTreeO11.
Elpi derive roseTreeO11.
(* Check roseTreeO11_is_roseTreeO11. *)
(* Check roseTreeO11_is_roseTreeO11_full. *)
(* Check roseTreeO11_is_roseTreeO11_trivial. *)
(* Check roseTreeO11_induction. *)

Inductive deep :=
| H (h:list(list(list(list deep)))).

(* Print Acc.
Elpi derive Acc.
Check Acc_induction. *)

(* Time Elpi derive deep. (* 372.5secs *)
Time Check deep_induction. *)