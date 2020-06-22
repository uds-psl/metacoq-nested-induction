Require Import destruct_lemma.
Require Import nested_datatypes.
Unset Strict Unquote Universe Mode.
Require Import standardNested.
Require Import addContainer.
Require Import Modes.


Require Import MetaCoq.Template.All.
Import MonadNotation.
Require Import String.



Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x;;
  match t with 
  | Ast.tLambda (nNamed na) _ _ => tmReturn na
  | _ => tmReturn "" 
  end.

Notation name_of n := (ltac:(let k x := exact x in run_template_program (getName (fun n : nat => 0)) k)).

Notation "'Scheme' 'Elimination' 'for' T" := (runElim T false true None None)(at level 8).
(* Notation "'Scheme' n ':=' 'Elimination' 'for' T" := ( *)
(*   name <- getName (fun n : nat => n);; *)
(*   runElim T false true (Some name) None *)
(* )(at level 8). *)

(* Notation "'Scheme' n ':=' 'Elimination' 'for' T 'Sort' ET" := (
  name <- getName (fun n : nat => n);;
  sortType <- tmQuote ET;;
  runElim T false true (Some name) (Some sortType)
)(at level 8). *)
Notation "'Scheme' 'Induction' 'for' T" := (runElim T true true None None)(at level 8).
Notation "'Scheme' n ':=' 'Induction' 'for' T" := (
  name <- getName (fun n : nat => n);;
  runElim T true true (Some name) None
)(at level 8).

Notation "'Set' 'Nested' 'Inductives'" := (
  changeMode helperGen.nestedMode true
  )(at level 8).
Notation "'Unset' 'Nested' 'Inductives'" := (
  changeMode helperGen.nestedMode false
  )(at level 8).

MetaCoq Run Unset Nested Inductives.


Notation "'Derive' 'Container' 'for' T" := (
  addType T
  )(at level 8).


Global Unset Strict Unquote Universe Mode.

Ltac ind_on_last :=
  lazymatch goal with
  | |- forall x y, ?H => intros ?;ind_on_last
  | |- forall y, ?H => 
      let inst := fresh "x" in
      intros inst;induction inst (* using database *)
  | _ => fail "not applicable"
  end.

Global Obligation Tactic := cbn;ind_on_last;econstructor;auto.

MetaCoq Run Set Nested Inductives.
