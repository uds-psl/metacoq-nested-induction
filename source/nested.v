(** tests induction principles for nested inductive types **)

Require Import MetaCoq.Template.All.
Require Import destruct_lemma.
Require Import MetaCoq.Template.Pretty.
Require Import List String.
Import ListNotations MonadNotation.

Require Import List.
Import ListNotations.

Require Import standardNested.
Require Import nested_datatypes.

Unset Strict Unquote Universe Mode.


MetaCoq Run (create roseTree4 true true). 
Print roseTree4_ind_MC.



Require Import Even.



Print roseTree.
MetaCoq Run (create roseTree true false).
MetaCoq Run (runElim roseTree true false None (Some <% Prop %>)).
MetaCoq Run (runElim roseTree true true None (Some <% Prop %>)).
Check roseTree_ind_MC.
Print roseTree_ind_MC.


Print roseTree2.
MetaCoq Run (create roseTree2 true false).
MetaCoq Run (runElim roseTree2 true true None (Some <% Prop %>)).
Check roseTree2_ind_MC.
Print roseTree2_ind_MC.

Print roseTree3.
MetaCoq Run (runElim roseTree3 true true None (Some <% Prop %>)).
Check roseTree3_ind_MC.
Print roseTree3_ind_MC.


Print roseTree4.
MetaCoq Run (create roseTree4 true false).
MetaCoq Run (runElim roseTree4 true true None (Some <% Prop %>)).
Check roseTree4_ind_MC.
Print roseTree4_ind_MC.


Print roseTree5.
MetaCoq Run (create roseTree5 true false).
MetaCoq Run (runElim roseTree5 true true None (Some <% Prop %>)).
Check roseTree5_ind_MC.
Print roseTree5_ind_MC.

Print roseTreePI1.
MetaCoq Run (create roseTreePI1 true false).
MetaCoq Run (runElim roseTreePI1 true true None (Some <% Prop %>)).
Print roseTreePI1_ind_MC.

Print roseTreePI2.
MetaCoq Run (create roseTreePI2 true false).
MetaCoq Run (runElim roseTreePI2 true true None (Some <% Prop %>)).
Print roseTreePI2_ind_MC.

Print roseTreePI3.
MetaCoq Run (create roseTreePI3 true false).
MetaCoq Run (runElim roseTreePI3 true true None (Some <% Prop %>)).
Print roseTreePI3_ind_MC.

Print roseTreePI4.
MetaCoq Run (create roseTreePI4 true false).
MetaCoq Run (runElim roseTreePI4 true true None (Some <% Prop %>)).
Print roseTreePI4_ind_MC.

Print roseTreePI5.
MetaCoq Run (create roseTreePI5 true false).
MetaCoq Run (runElim roseTreePI5 true true None (Some <% Prop %>)).
Print roseTreePI5_ind_MC.

Print roseTreePI6.
MetaCoq Run (create roseTreePI6 true false).
MetaCoq Run (runElim roseTreePI6 true true None (Some <% Prop %>)).
Print roseTreePI6_ind_MC.

Print roseTreePI7.
MetaCoq Run (create roseTreePI7 true false).
MetaCoq Run (runElim roseTreePI7 true true None (Some <% Prop %>)).
Print roseTreePI7_ind_MC.

Print roseTreePI8.
MetaCoq Run (create roseTreePI8 true false).
MetaCoq Run (runElim roseTreePI8 true true None (Some <% Prop %>)).
Print roseTreePI8_ind_MC.



Print rtree.
MetaCoq Run (create rtree true false).
MetaCoq Run (runElim rtree true true None (Some <% Type %>)).
Print rtree_ind_MC.
Print is_list.

Print is_list_rect.




Print roseTreeNN4.
Print prodAssumption.

(* need implementation of pair *)

Print roseTreeNN1.
MetaCoq Run (create roseTreeNN1 true false).
MetaCoq Run (runElim roseTreeNN1 true true None (Some <% Prop %>)).
Print roseTreeNN1_ind_MC.

Print roseTreeNN2.
MetaCoq Run (create roseTreeNN2 true false).
MetaCoq Run (runElim roseTreeNN2 true true None (Some <% Prop %>)).
Print roseTreeNN2_ind_MC.

Print roseTreeNN3.
MetaCoq Run (create roseTreeNN3 true false).
MetaCoq Run (runElim roseTreeNN3 true true None (Some <% Prop %>)).
Print roseTreeNN3_ind_MC.

Print roseTreeNN4.
MetaCoq Run (create roseTreeNN4 true false).
MetaCoq Run (runElim roseTreeNN4 true true None (Some <% Prop %>)).
Print roseTreeNN4_ind_MC.

Print roseTreeNN5.
MetaCoq Run (create roseTreeNN5 true false).
MetaCoq Run (runElim roseTreeNN5 true true None (Some <% Prop %>)).
Print roseTreeNN5_ind_MC.



Print roseTreeNN6.
MetaCoq Run (create roseTreeNN6 true false).
MetaCoq Run (runElim roseTreeNN6 true true None (Some <% Prop %>)).
Print roseTreeNN6_ind_MC.


Print roseTreeNN7.
MetaCoq Run (create roseTreeNN7 true false).
MetaCoq Run (runElim roseTreeNN7 true true None (Some <% Prop %>)).
Print roseTreeNN7_ind_MC.


(* nested nested induction *)

Print roseTreeDN3.
MetaCoq Run (create roseTreeDN3 true false).
MetaCoq Run (runElim roseTreeDN3 true true None (Some <% Prop %>)).
Print roseTreeDN3_ind_MC.

Print roseTreeDN1.
MetaCoq Run (create roseTreeDN1 true false).
MetaCoq Run (runElim roseTreeDN1 true true None (Some <% Prop %>)).
Print roseTreeDN1_ind_MC.

Print roseTreeDN2.
MetaCoq Run (create roseTreeDN2 true false).
MetaCoq Run (runElim roseTreeDN2 true true None (Some <% Prop %>)).
Print roseTreeDN2_ind_MC.

Print roseTreeDN4.
MetaCoq Run (create roseTreeDN4 true false).
MetaCoq Run (runElim roseTreeDN4 true true None (Some <% Prop %>)).
Print roseTreeDN4_ind_MC.

Print roseTreeDN5.
MetaCoq Run (create roseTreeDN5 true false).
MetaCoq Run (runElim roseTreeDN5 true true None (Some <% Prop %>)).
Print roseTreeDN5_ind_MC.


Print roseTreeDN7.
MetaCoq Run (create roseTreeDN7 true false).
MetaCoq Run (runElim roseTreeDN7 true true None (Some <% Prop %>)).
Print roseTreeDN7_ind_MC.

Print roseTreeDN6.
MetaCoq Run (create roseTreeDN6 true false).
MetaCoq Run (runElim roseTreeDN6 true true None (Some <% Prop %>)).
Print roseTreeDN6_ind_MC.

Print term.
MetaCoq Run (create term true false).
MetaCoq Run (runElim term true true None (Some <% Prop %>)).
Print term_ind_MC.


(* MetaCoq Run (runElim is_list true true None (Some <% Prop %>)). *)
(* Print is_list_ind_MC. *)


Print roseTreeO1.
(* MetaCoq Run (create roseTreeO1 true false). *)
(* MetaCoq Run (runElim roseTreeO1 true true None (Some <% Prop %>)). *)
(* Print roseTreeO1_ind_MC. *)

Print roseTreeO2.
MetaCoq Run (create roseTreeO2 true false).
MetaCoq Run (runElim roseTreeO2 true true None (Some <% Prop %>)).
Print roseTreeO2_ind_MC.

Print roseTreeO3.
MetaCoq Run (create roseTreeO3 true false).
MetaCoq Run (runElim roseTreeO3 true true None (Some <% Prop %>)).
Print roseTreeO3_ind_MC.

Print roseTreeO4.
(* MetaCoq Run (create roseTreeO4 true false). *)
(* MetaCoq Run (runElim roseTreeO4 true true None (Some <% Prop %>)). *)
(* Print roseTreeO4_ind_MC. *)

Print roseTreeO5.
(* MetaCoq Run (create roseTreeO5 true false). *)
(* MetaCoq Run (runElim roseTreeO5 true true None (Some <% Prop %>)). *)
(* Print roseTreeO5_ind_MC. *)

Print roseTreeO6.
(* MetaCoq Run (create roseTreeO6 true false). *)
(* MetaCoq Run (runElim roseTreeO6 true true None (Some <% Prop %>)). *)
(* Print roseTreeO6_ind_MC. *)

Print roseTreeO7.
MetaCoq Run (create roseTreeO7 true false).
MetaCoq Run (runElim roseTreeO7 true true None (Some <% Prop %>)).
Print roseTreeO7_ind_MC.

Print roseTreeO8.
MetaCoq Run (create roseTreeO8 true false).
MetaCoq Run (runElim roseTreeO8 true true None (Some <% Prop %>)).
Print roseTreeO8_ind_MC.

Print roseTreeO9.
MetaCoq Run (create roseTreeO9 true false).
MetaCoq Run (runElim roseTreeO9 true true None (Some <% Prop %>)).
Print roseTreeO9_ind_MC.

Print roseTreeO10.
MetaCoq Run (create roseTreeO10 true false).
MetaCoq Run (runElim roseTreeO10 true true None (Some <% Prop %>)).
Print roseTreeO10_ind_MC.

Print roseTreeO11.
MetaCoq Run (create roseTreeO11 true false).
MetaCoq Run (runElim roseTreeO11 true true None (Some <% Prop %>)).
Print roseTreeO11_ind_MC.


Print roseTreeO13.
MetaCoq Run (create roseTreeO13 true false).
(* MetaCoq Run (runElim roseTreeO13 true true None (Some <% Prop %>)). *)
(* Print roseTreeO13_ind_MC. *)




Print roseTreeNN6.

Print foterm.
MetaCoq Run (create foterm true false).
MetaCoq Run (runElim foterm true true None (Some <% Prop %>)).
Print foterm_ind_MC.

Print form.
MetaCoq Run (create form true false).
MetaCoq Run (runElim form true true None (Some <% Prop %>)).
Print form_ind_MC.


