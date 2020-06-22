(** A completely interactive command with variable amount of obligations **)

Require Import MetaCoq.Template.All.

Require Import List String.
Import ListNotations MonadNotation Nat.

Fixpoint printer (n:nat) :=
match n with 
| O => tmMsg "All Done";;
       tmReturn 0
| S m => 
  name <- tmFreshName "tmp";;
  a <- tmLemma name nat;;
  ssum <- (printer m);;
  tmReturn (ssum + a)
end.


MetaCoq Run (n <- tmLemma "t1" nat;; 
n' <- tmEval all n;;
sum <- printer n';;
sumR <- tmEval all sum;;
tmPrint sumR).
Next Obligation.
  exact 2.
Defined.
Next Obligation.
  exact 3.
Defined.
Next Obligation.
  exact 4.
Defined.
