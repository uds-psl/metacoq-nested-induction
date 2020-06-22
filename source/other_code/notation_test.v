Require Import String.
From MetaCoq Require Import Template.All.
Export MonadNotation.

Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x ;; match t with tLambda (nNamed na) _ _ => ret na | _ => ret "" end.

Notation name_of n := (ltac:(let k x := exact x in run_template_program (getName (fun n : nat => 0)) k)).

Compute (name_of n).
Compute (name_of m).
     (* = "n" *)
     (* : string *)

Notation "'Scheme' name ':=' 'Case' 'Analysis' 'for' T 'Sort' 'Type'" := (makeSchemeType (get_name name) T). 

MetaCoq Run Scheme nat_destr := Case Analysis on nat Sort Type.

