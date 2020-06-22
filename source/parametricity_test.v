(** test of the unary parametricity translation **)

From MetaCoq Require Import Template.All.
Require Import List String.
Import ListNotations MonadNotation.
Require Import MetaCoq.Template.Pretty.


From MetaCoq.Checker Require Import All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.

(* Import VectorDef. *)

(* Section Vector. *)
(*   Require Import Vector. *)
(*   MetaCoq Run (TC <- Translate nat_TC "t" ;; *)
(*                   tmDefinition "vec_TC" TC ). *)
(*   Print tᵗ. *)
(*   Print natᵗ. *)
(*   Print Oᵗ. *)
(*   Print Sᵗ. *)
(* End Vector. *)


(* MetaCoq Run (Translate emptyTC "list"). *)

MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
Print list_TC.
Print listᵗ.
Print listᵗ_ind.

Inductive AllI {A : Type} (P : A -> Type) : list A -> Type :=
    All_nil : AllI P []
  | All_cons : forall (x : A) (l : list A), P x -> AllI P l -> AllI P (x :: l).
(* Print All_Forall.All. *)
(* Definition all_ind := @All_Forall.All. *)
(* Print all_ind. *)

MetaCoq Run (tmQuoteInductive "AllI" >>= tmPrint).

Unset Strict Unquote Universe Mode. 

(* MetaCoq Run (TC <- Translate list_TC "AllI" ;; *)
(*                 tmDefinition "All_TC" TC ). *)


Require Import nested_datatypes.

Inductive roseTreeO3P (X:Type) : Prop :=
  treeO3P (x:X) (xs:list X) (xxs:roseTreeO3P X) (xsxs: list (roseTreeO3P X)).

MetaCoq Run (TC <- Translate list_TC "roseTreeO3P" ;;
                tmDefinition "roseTreeO3P_TC" TC ).
Print roseTreeO3Pᵗ.

(* need Prop for max universe *)
Inductive rtreeProp A : Prop :=
| LeafProp (a:A)
| NodeProp (l:list (rtreeProp A)).


(* Inductive rtreePropᵗ (A : Type) (Aᵗ : A -> Type) : rtreeProp A -> Prop := *)
(*     LeafPropᵗ : forall a : A, Aᵗ a -> rtreePropᵗ A Aᵗ (LeafProp A a) *)
(*   | NodePropᵗ : forall l : list (rtreeProp A), *)
(*       listᵗ (rtreeProp A) (rtreePropᵗ A Aᵗ) l -> rtreePropᵗ A Aᵗ (NodeProp A l). *)
(* Print rtreePropᵗ_ind. *)

MetaCoq Run (TC <- Translate list_TC "rtreeProp" ;;
                tmDefinition "rtreeProp_TC" TC ).
Print rtreePropᵗ.
Print rtreePropᵗ_ind.
(*
this weak principle is nearly the wanted induction
difference:
listᵗ (rtreeProp A) (rtreePropᵗ A Aᵗ) l
instead of
listᵗ (rtreeProp A) P l
inside the constructor case
 *)
Print rtreeProp_ind.

MetaCoq Run (Translate rtreeProp_TC "rtreeProp_ind").
Print rtreeProp_indᵗ.


MetaCoq Run (TC <- Translate emptyTC "prod" ;;
                tmDefinition "prod_TC" TC ).
Print prodᵗ.


(* Definition vec := VectorDef.t. *)
(* Print VectorDef.t. *)
Inductive vec (A : Type) : nat -> Type :=
    vecnil : vec A 0
  | veccons : A ->
           forall n : nat,
             vec A n -> vec A (S n).
MetaCoq Run (TC <- Translate nat_TC "vec" ;;
                tmDefinition "vec_TC" TC ).
Print vecᵗ.

Inductive G (f:nat->bool) : nat -> Prop :=
  GI : forall n, (f n = false -> G f (S n)) -> G f n.

(* MetaCoq Run (TC <- TranslateRec emptyTC "G" ;; *)
(*                 tmDefinition "G_TC" TC ). *)

MetaCoq Run (TC <- TranslateRec emptyTC G ;;
                tmDefinition "TC" TC).
Print Gᵗ.



(* MetaCoq Run (TC <- Translate bool_TC "eq" ;; *)
(*                 tmDefinition "eq_TC" TC ). *)
(* (* Print G_TC. *) *)
(* MetaCoq Run (TC <- Translate eq_TC "G" ;; *)
(*                 tmDefinition "G2_TC" TC ). *)
(* Print Gᵗ. *)

Print Acc.
MetaCoq Run (TranslateRec emptyTC Acc).
Print Accᵗ.


MetaCoq Run (TranslateRec bool_TC containerInd4).
Print containerInd4ᵗ.

Print boolᵗ.
Print natᵗ.


