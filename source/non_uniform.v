(** computes the number of non-uniform parameters in an inductive type (syntactic check) **)


Require Import MetaCoq.Template.All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

Require Import List String.
Import ListNotations MonadNotation Nat.

(*
Map over
look for tRel 0
und  S a = b, S b = c bei tRel a [b;c;d]
Indices kommen später => Bruch?
min(ermittelt, ind_npars)
 *)

Open Scope nat_scope.


Fixpoint getMinChain k t cl max : option nat :=
  match t with
  | tRel n => if n =? k then
               Some 0
             else
               None
  | tApp t1 t2 =>
    m <- getMinChain k t1 (S cl) max;;
      match t2 with
      | tRel n =>
        if n =? k+cl-max then
          Some (S m)
        else
          Some m
      | _ => Some m
      end
  | _ => None
  end.

(* check correctness *)
Fixpoint countOfCtor (k:nat) (max:nat) (c:term) {struct c} : nat :=
  match c with
    tRel _ => max
  | tProd _ t1 t2 => min (countOfCtor k max t1) (countOfCtor (S k) max t2)
  | tApp t1 t2 =>
    min (
    match getMinChain k c 0 max with
      None => countOfCtor k max t1
    | Some x => x
    end)
          (countOfCtor k max t2)
  | _ => max
  end.



Fixpoint collect_prods (t:term) : list (context_decl) :=
  match t with
  | tProd n t1 t2 => (vass n t1)::collect_prods t2
  | _ => []
  end.
Definition count_prods (t : term) : nat := #|collect_prods t|.

Definition getParamCount (ind:one_inductive_body) (n0:nat) : nat :=
  fold_right (fun c m => min m (countOfCtor 0 (count_prods (ind.(ind_type))) (snd(fst c)))) n0 ind.(ind_ctors).

Definition getPCount (ind:mutual_inductive_body) (c:nat) : option nat :=
  match nth_error ind.(ind_bodies) c with
    None => None
  | Some b => Some (getParamCount b ind.(ind_npars))
  end.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.

Definition getP (tm : Ast.term)
  : TemplateMonad unit
  := match tm with
     | Ast.tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       c <- tmEval lazy (getPCount (trans_minductive_body decl) ind0.(inductive_ind));;
       tmPrint c
     | _ => tmFail "not inductive"
     end.


