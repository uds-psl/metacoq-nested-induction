(** a small plugin to add the contraposition of implications as axiom **)


Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.

Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.

Require Import List String.

Open Scope string.

Ltac addContrapos H :=
  match H with
    ?A -> ?B => assert (B->A) by admit
  | _ => fail "wrong structure"
  end.

Definition termNegType t := Ast.tProd nAnon t <% False %>.

Definition addContraposType {A:Type} (H:A) (name:ident) :TemplateMonad unit :=
  p <- tmQuote H;;
  match p with
  | Ast.tProd nAnon t1 t2 => 
    na <- tmFreshName name;;
    q <- tmUnquoteTyped Type (Ast.tProd nAnon (termNegType t2) (termNegType t1));;
    tmAxiomRed na None (q:Type);;
    tmPrint q;;
    tmMsg (append "was added to the environment as axiom " na)
  | Ast.tProd _ _ _ => tmFail "A non dependent implication is expected"
  | _ => tmFail "Invalid argument. Implication expected"
  end.

MetaCoq Run (addContraposType (True -> False) "Contra").
MetaCoq Run (addContraposType (bool -> nat) "Contra").

Definition H := True -> False.
MetaCoq Run (
  p <- tmAbout "H";;
  tmPrint p
).
MetaCoq Run (
  p <- tmQuote H;;
  tmPrint p
).
MetaCoq Run (
  p <- tmQuoteConstant "H" false;;
  q <- tmEval hnf p;;
  tmPrint q
).

Definition computeContrapos (t:Ast.term) (name:ident) : TemplateMonad unit :=
  match t with
  | Ast.tProd nAnon t1 t2 => 
    na <- tmFreshName name;;
    q1 <- tmUnquoteTyped Prop t1;;
    q2 <- tmUnquoteTyped Prop t2;;
    let q := ~q2 -> ~q1 in
    (
      tmAxiomRed na None q;;
      tmPrint q;;
      tmMsg (append "was added to the environment as axiom " na)
    )
  | Ast.tProd _ _ _ => tmFail "A non dependent implication is expected"
  | _ => tmFail "Invalid argument. Implication expected"
  end.


Definition addContrapos (H:Prop) (name:ident) :TemplateMonad unit :=
  p <- tmQuote H;;
  match p with
  | Ast.tConst qual _ => 
    q <- tmQuoteConstant qual false;;
    match Ast.cst_body q with
    | Some t => computeContrapos t name
    | None => tmFail "a constant with an opaque body is not a valid argument"
    end
  | _ => computeContrapos p name
  end.


MetaCoq Run (addContrapos (False -> True) "Contra").
Print Contra1.
MetaCoq Run (addContrapos H "Contra_H").
Print Contra_H.
Fail MetaCoq Run (addContrapos (bool -> nat) "Contra").
Fail MetaCoq Run (addContrapos 0).
Fail MetaCoq Run (addContrapos (forall (x:bool), nat)).

Print Contra1.



Axiom (H2:Type).

Definition H3:Type.
exact (True -> True).
Qed.

Fail MetaCoq Run (addContrapos H2 "T").
Fail MetaCoq Run (addContrapos H3 "T").
