(** test script for removal of unneeded arguments **)


Load removeNonAug.

Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
    nilᵗ : listᵗ A Aᵗ []
  | consᵗ : forall H : A,
            Aᵗ H -> forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0).


Inductive boolᵗ : bool -> Set :=
  trueᵗ : boolᵗ true | falseᵗ : boolᵗ false.
Inductive natᵗ : nat -> Set :=
    Oᵗ : natᵗ 0
  | Sᵗ : forall H : nat, natᵗ H -> natᵗ (S H).

Definition vec := VectorDef.t.

Inductive
vecᵗ (A : Type) (Aᵗ : A -> Type)
  : forall H : nat, natᵗ H -> vec A H -> Type :=
    vecnilᵗ : vecᵗ A Aᵗ 0 Oᵗ (@Vector.nil A)
  | vecconsᵗ : forall H : A,
               Aᵗ H ->
               forall (n : nat) (nᵗ : natᵗ n)
                 (H0 : vec A n),
               vecᵗ A Aᵗ n nᵗ H0 ->
               vecᵗ A Aᵗ (S n) (Sᵗ n nᵗ)
                    (@Vector.cons A H n H0).


(* Inductive *)
(* vecᵗ' (A : Type) (Aᵗ : A -> Type) *)
(*   : forall H : nat, vec A H -> Type := *)
(*     vecnilᵗ' : vecᵗ' A Aᵗ 0 (@Vector.nil A) *)
(*   | vecconsᵗ' : forall H : A, *)
(*                Aᵗ H -> *)
(*                forall (n : nat) *) 
(*                (1* (nᵗ : natᵗ n) *1) *)
(*                  (H0 : vec A n), *)
(*                vecᵗ' A Aᵗ n H0 -> *)
(*                vecᵗ' A Aᵗ (S n) *)
(*                     (@Vector.cons A H n H0). *)





(*
Print vecᵗ.

Inductive
vecᵗ (A : Type) (Aᵗ : A -> Type)
  : forall H : nat, natᵗ H -> vec A H -> Type :=
    vecnilᵗ : vecᵗ A Aᵗ 0 Oᵗ (Vector.nil A)
  | vecconsᵗ : forall H : A,
               Aᵗ H ->
               forall (n : nat) (nᵗ : natᵗ n) (H0 : vec A n),
               vecᵗ A Aᵗ n nᵗ H0 ->
               vecᵗ A Aᵗ (S n) (Sᵗ n nᵗ) (Vector.cons A H n H0)
               *)

(* MetaCoq Run (cleanInd "vecᵗ" >>= tmMsg). *)
(* MetaCoq Run (cleanInd listᵗ >>= tmMsg). *)

(* Print vecᵗ0. *)
(* Print listᵗ0. *)

Print tmMkInductive.
Print mutual_inductive_entry.
Search mutual_inductive_entry.
Print mutual_inductive_body.
Print context_decl.

MetaCoq Run (tmQuoteInductive "vecᵗ" >>= tmPrint).


Compute (removeArgList (tApp (tRel 0) [tRel 1;tRel 2;tRel 3]) [1]).

About print_term.
Search global_env_ext.

(* MetaCoq Run ( *)
(* xp <- removeNonAugmentable <% forall(A : Type) (Aᵗ : A -> Type) *)
(*   , forall H : nat, natᵗ H -> vec A H -> Type %> 0 ;; *)
(* y <- tmEval all (xp);; *)
(* tmPrint y;; *)
(* tmMsg (print_term (empty_ext []) [] true y.1)). *)

(* MetaCoq Run ( *)
(* x <- removeNonAugmentable *) 
(*   <% *)
(* forall(A : Type) (Aᵗ : A -> Type), *)
(*                forall H : A, *)
(*                Aᵗ H -> *)
(*                forall (n : nat) (nᵗ : natᵗ n) *)
(*                  (H0 : vec A n), *)
(*                vecᵗ A Aᵗ n nᵗ H0 -> *)
(*                vecᵗ A Aᵗ (S n) (Sᵗ n nᵗ) *)
(*                     (@Vector.cons A H n H0) *)
(*   %> 0;; *)
(* y <- tmEval all (x);; *)
(* tmPrint y;; *)
(* tmMsg (print_term (empty_ext []) [] true y.1);; *)
(* tmMsg "";; *)
(* tmMsg "";; *)
(* tmMsg "";; *)
(* y2 <- tmEval all (removeArgList (y.1) [3]);; *)
(* tmPrint y2;; *)
(* tmMsg (print_term (empty_ext []) [] true y2) *)
(* ). *)

(*
1. remove Parameter after non augmentable inductive
2. delete parameter in recursive call

should the function look inside the arguments?
TODO: find examples like (T -> nat) or (nat -> T) in an argument
*)




