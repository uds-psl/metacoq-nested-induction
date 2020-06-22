(** implementation of a flag system in MetaCoq **)

Require Import MetaCoq.Template.All.
Require Import String.
Import MonadNotation.

Class mode (s:string) := { state: bool }.

Print tmExistingInstance.
Print global_reference.

Definition changeMode (m:string) (value:bool) : TemplateMonad unit :=
  ename <- tmEval all m;;
  name <- tmFreshName ename;;
  tmDefinition name ({| state := value |}:mode m);;
  tmExistingInstance name;;
  tmMsg (append (append "The mode " m) (append " was " (if value then "set" else "unset"))).

Definition getMode (m:string) : TemplateMonad bool :=
  v <- tmInferInstance None (mode m);;
  val <- tmEval all (
    match v with
      my_None => false
    | my_Some v' => @state _ v'
    end
  );;
  tmReturn val.


Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x;;
  match t with 
  | Ast.tLambda (nNamed na) _ _ => tmReturn na
  | _ => tmReturn "" 
  end.

Notation "'Set' n" := (
  name <- getName (fun n:nat => n);;
  changeMode name true
  )(at level 8).
Notation "'Unset' n" := (
  name <- getName (fun n:nat => n);;
  changeMode name false
  )(at level 8).


