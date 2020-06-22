
(** second test of the unary parametricity translation **)

From MetaCoq Require Import Template.All.
Require Import List String.
Import ListNotations MonadNotation.
Require Import MetaCoq.Template.Pretty.


From MetaCoq.Checker Require Import All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

(* MetaCoq Run (Translate emptyTC "list"). *)

Inductive btree (A B:Type) := Node (h:(btree A B)*(btree A B)).
MetaCoq Run (TranslateRec emptyTC btree).
Print btreeᵗ.
Inductive btree' (A B:Type) := Node' (h:list (btree' A B)).
(* MetaCoq Run (TranslateRec emptyTC btree'). *)

Print VectorDef.t.
MetaCoq Run (TranslateRec emptyTC VectorDef.t).
Print tᵗ.

(* MetaCoq Run (TranslateRec emptyTC nat >>= tmPrint). *)
(* Print natᵗ. *)

(* Inductive roseTree := tree (h:list roseTree). *)
(* MetaCoq Run (TranslateRec emptyTC roseTree >>= tmPrint). *)
(* Print roseTreeᵗ. *)


(* MetaCoq Run (TranslateRec emptyTC list). *)
(* Print listᵗ. *)

MetaCoq Run (TranslateRec emptyTC Acc).
Print Accᵗ.


Check TranslateRec.
Search "tsl_table".



MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
Print list_TC.
Print listᵗ.
(* Print listᵗ_ind. *)

MetaCoq Run (TC <- Translate list_TC "listᵗ" ;;
                tmDefinition "listt_TC" TC ).
Print listᵗ.
Print listᵗᵗ.

(* From MetaCoq.Translations Require Import param_binary. *)
(* MetaCoq Run (TC <- Translate emptyTC "list" ;; *)
(*                 tmDefinition "list_TC" TC ). *)
(* Print listᵗ. *)
