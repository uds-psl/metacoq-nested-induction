
Inductive is_list A (PA:A->Type) : list A -> Type :=
| is_nil : is_list A PA nil
| is_cons a (pa: PA a) l (pl:is_list A PA l): is_list A PA (a::l).

(* Axiom list_induct :
forall (A:Type) (P:list A -> Prop) (Q:A -> Prop),
P nil -> (forall (x:A) (xs:list A), Q x -> P xs -> P (cons x xs)) ->
forall (xs:list A), is_list A Q xs -> P xs. *)

Check list_ind.
(*
list_ind
     : 
     ∀ (A : Type) (P : list A ⟶ Prop),
       P nil ⟶
       (∀ (a : A) (l : list A), P l ⟶ P (a :: l)%list) ⟶
       ∀ l : list A, P l
*)

Require Import List.

Definition isToSig A Q xs: is_list A Q xs -> list {x:A & Q x}.
Proof.
intros H.
induction H.
- exact nil.
- eapply cons.
  + econstructor. apply pa.
  + apply IHis_list.
Defined.


Goal (
    forall (A:Type) (P:list A -> Prop),
    P nil -> (forall (x:A) (xs:list A), P xs -> P (cons x xs)) ->
    forall (xs:list A), P xs
) ->
(
    forall (A:Type) (P:list A -> Prop) (Q:A -> Prop),
    P nil -> (forall (x:A) (xs:list A), Q x -> P xs -> P (cons x xs)) ->
    forall (xs:list A), is_list A Q xs -> P xs
).
Proof.
  intros H.
  intros A P Q.
  specialize (H ({x:A & Q x})).
  specialize (H 
    (fun (x:list {x:A & Q x}) => 
      P
      (map (@projT1 A Q) x)
    )).
    cbn in H.
  intros.
  enough (P (map (@projT1 A Q) (isToSig _ _ xs X))).
  {
    assert(map (@projT1 A Q) (isToSig A Q xs X)=xs). 
    {
      clear H2.
      induction X;trivial.
      cbn. f_equal.
      rewrite <- IHX.
      reflexivity.
    }
    now rewrite H3 in H2.
  }
  apply H;trivial.
  intros. 
  destruct x.
  specialize (H1 x (map (@projT1 A Q) xs0) q H2).
  apply H1.
Qed.