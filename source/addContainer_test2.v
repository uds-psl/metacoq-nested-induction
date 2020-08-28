
(** a test for the derivation of new container types **)
Inductive or2 (A B : Prop) : Type :=
	or2_introl : A -> or2 A B | or2_intror : B -> or2 A B.

Load addContainer.


(* MetaCoq Run (addType or). *)
(* MetaCoq Run (addType sum). *)

(* MetaCoq Run (addType or2). *)
(* Next Obligation. *)
(*   induction H. *)

(*   induction H eqn: X. *)
(*   dependent induction H. *)
(*   induction H. *)
(*   destruct H. *)
(*   - now constructor. *)
(*   - now constructor. *)
(* Defined. *)



MetaCoq Run (addType list).
Next Obligation.
  induction X.
  - constructor.
  - constructor.
    + apply AH.
    + apply IHX.
Defined.
Print list_inst.
(* Next Obligation. *)
(* apply True. *)
(* Defined. *)
(* Next Obligation. *)
(* apply I. *)
(* Defined. *)


Print All_Forall.All.

Inductive All2 {A : Type} (P : A -> Type) : list A -> Type :=
    All2_nil : All2 P []
  | All2_cons : forall (x : A) (l : list A), P x -> All2 P l -> All2 P (x :: l).

(* MetaCoq Run (addType (@All2)). *)



Inductive t2 (A : Type) : nat -> Type :=
    nilt2 : t2 A 0
  | const2 : A -> forall n : nat, t2 A n -> t2 A (S n).

(* Obligation Tactic := idtac. *)

MetaCoq Run (addType t2).
Next Obligation.
  induction X.
  - constructor.
  - constructor.
    + apply AH.
    + apply IHX.
Defined.

Print t2_inst.
Print t2ᵗ0.
Print t2ᵗ.

(* Next Obligation. *)
(* cbn.  intros. *)
(* apply True. *)
(* Defined. *)
(* Next Oblgiation. *)

