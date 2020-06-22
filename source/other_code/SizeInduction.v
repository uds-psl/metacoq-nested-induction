
Require Import MetaCoq.Template.All.

Print tmQuote.
Print typing.
About typing_spine.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICSize
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.


(* Require Import MetaCoq.Template.All. *)
Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.





Check size.

Require Import Lia.

Goal forall (P:nat->Prop),
  (forall n, (forall m, m<n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros P H n.
  apply H.

  induction n.
  - intros.
    lia.
  - intros.
    apply H.
    intros.
    apply IHn.
    lia.
Qed.


Lemma size_induction X (f:X->nat) (P:X->Type):
  (forall x, (forall y, f y<f x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros. apply X0.
  assert(forall n y, f y < n -> P y).
  {
    induction n.
    - lia.
    - intros.
      apply X0.
      intros.
      apply IHn.
      lia.
  }
  apply X1.
Defined.


Goal forall (P:term->Type),
  (forall t, (forall t2, size t2 < size t -> P t2) -> P t) ->
  forall t, P t.
Proof.
  apply size_induction.
Defined.


Print well_founded_induction.

(* Require Import Coq.Arith.Wf_nat. *) 
Require Import Coq.Wellfounded.Wellfounded. 

(* Print ltof. *)
(* Check (induction_ltof1 _ (@List.length term)). *)

(* Check (well_founded_induction *)
(*                      (wf_inverse_image _ nat _ (@List.length _) *)
(*                         PeanoNat.Nat.lt_wf_0)). *)


Definition term_size_ind := well_founded_induction
                     (wf_inverse_image _ nat _ (size)
                        PeanoNat.Nat.lt_wf_0).
Check term_size_ind.



Goal forall (P:term->Type),
  (forall t, (forall t2, size t2 < size t -> P t2) -> P t) ->
  forall t, P t.
Proof.
  apply size_induction.


  intros.
  apply X.
  
  induction t using term_forall_list_ind;simpl;intros.
  - assert(size t2=0) by lia.
    destruct t2;cbn in H0;congruence.
  - assert(size t2=0) by lia.
    destruct t2;cbn in H0;congruence.
  - admit.
  - 


























