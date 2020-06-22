(** test the generated nesting function and container lookup **)

Load helperGen. 

MetaCoq Run (changeMode nestedMode true).

Print inductive.
Print Ast.tInd.
About Ast.tInd.
About inductive.
Print nth_error.
Search one_inductive_body.

Definition testInd {A} (ind:A) : TemplateMonad unit :=
  indq <- tmQuote ind;;
  match indq with
  | Ast.tInd (mkInd mindN idx) _ => 
    mind <- tmQuoteInductive mindN;;
    match nth_error (Ast.ind_bodies mind) idx with
    | None => tmFail ""
    | Some oind => getInds (trans_one_ind_body oind) >>= print_nf
    end
  | _ => tmFail ""
  end.

Require Import nested_datatypes.

MetaCoq Run (testInd list).
MetaCoq Run (testInd rtree).
MetaCoq Run (testInd term).
