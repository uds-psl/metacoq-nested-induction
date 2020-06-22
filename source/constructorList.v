(** a small plugin to derive a list of all constructors of an inductive type **)

Require Import MetaCoq.Template.All.

Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.

Require Import List String.
Open Scope string.

Unset Strict Unquote Universe Mode. 



Definition getCtorsSimpl {A} (ind:A) : TemplateMonad unit :=
  tm <- tmQuote ind;;
  match tm with
  | tInd (mkInd kername idx as induct) _ =>
      mbody <- tmQuoteInductive kername;;
      match nth_error mbody.(ind_bodies) idx with
      | Some ibody => 
          ctors <- monad_map
            (fun '(na,t,count) => 
              tmUnquoteTyped Type (subst10 tm t)
            ) 
            ibody.(ind_ctors);;
          tmPrint ctors
      | None => tmFail "the mutual inductive index was wrong" (* can't happen *)
      end
  | _ => tmFail "argument has to be an inductive type"
  end.


MetaCoq Run (getCtorsSimpl nat).
Fail MetaCoq Run (getCtorsSimpl list).

Definition listCtors : list ({ T : Type & T}).
  apply cons.
  2: apply cons.
  3: apply nil.
  - exists (forall (A:Type), list A).
    exact @nil.
  - exists (forall (A:Type), A -> list A -> list A).
    exact @cons.
Defined.

(* Set Printing Universes. *)
Print listCtors.
About listCtors.


Definition natCtors : list ({ T : Type & T}).
  apply cons.
  - exists nat.
    exact O.
  - apply cons.
    + exists (nat->nat).
      exact S.
    + apply nil.
Defined.

Print natCtors.


Definition getCtors {A} (ind:A) : TemplateMonad unit :=
  tm <- tmQuote ind;;
  match tm with
  | tInd (mkInd kername idx as induct) _ =>
      mbody <- tmQuoteInductive kername;;
      match nth_error mbody.(ind_bodies) idx with
      | Some ibody => 
          ctors <- monad_map_i
            (fun i '(na,t,count) => 
              ctorType <- tmUnquoteTyped Type (subst10 tm t);;
              ctor <- tmUnquoteTyped ctorType (tConstruct induct i []);;
              tmEval lazy ((ctorType;ctor):∑ T : Type, T)
            ) 
            ibody.(ind_ctors);;
          tmDefinition (append ibody.(ind_name) "_ctors") ctors;;
          tmPrint ctors
      | None => tmFail "the mutual inductive index was wrong" (* can't happen *)
      end
  | _ => tmFail "argument has to be an inductive type"
  end.

MetaCoq Run (getCtors nat).
Print nat_ctors.

MetaCoq Run (getCtors Acc).
MetaCoq Run (getCtors or).
MetaCoq Run (getCtors sig).
Print or_ctors.
Print sig_ctors.
MetaCoq Run (getCtors option).
MetaCoq Run (getCtors term).
(* MetaCoq Run (getCtorsSimpl list). *)

