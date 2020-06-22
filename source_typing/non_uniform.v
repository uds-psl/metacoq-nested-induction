Require Import MetaCoq.Template.All.
Require Import List String.
Import ListNotations MonadNotation Nat.

(*
Map over
look for tRel 0
und  S a = b, S b = c bei tRel a [b;c;d]
min(ermittelt, ind_npars)
 *)

Open Scope nat_scope.

Fixpoint getMinChain (r:nat) (c:nat) (xs:list term) : nat :=
  match xs with
  | tRel k :: ys => if (S k) =? r then getMinChain k (S c) ys else c
  | _ => c
  end.

Fixpoint countOfCtor (k:nat) (max:nat) (c:term) : nat :=
  match c with
    tRel _ => max
  | tProd _ t1 t2 => min (countOfCtor k max t1) (countOfCtor (S k) max t2)
  | tApp (tRel n) tl => if n =? k then
                         getMinChain n 0 tl
                       else fold_right min max (map (countOfCtor k max) tl)
  | tApp t tl => fold_right min (countOfCtor k max t) (map (countOfCtor k max) tl)
  | _ => max
  end.

Definition getParamCount (ind:one_inductive_body) (n0:nat) : nat :=
  fold_right (fun c m => min m (countOfCtor 0 n0 (snd(fst c)))) n0 ind.(ind_ctors).

Definition getPCount (ind:mutual_inductive_body) (c:nat) : option nat :=
  match nth_error ind.(ind_bodies) c with
    None => None
  | Some b => Some (getParamCount b ind.(ind_npars))
  end.

(* Print inductive. *)

Definition getP (tm : term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
            c <- tmEval lazy (getPCount decl ind0.(inductive_ind));;
            tmPrint c
     | _ => tmFail "not inductive"
     end.
