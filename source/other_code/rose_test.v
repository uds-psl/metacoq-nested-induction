Inductive roseTree := node (h:list roseTree).

Require Import List.
Import ListNotations.



Scheme nat_induct := Induction for nat Sort Type.
Print nat_induct.

Fixpoint maxList (xs:list nat) : nat :=
match xs with
| [] => 0
| y::ys => max y (maxList ys)
end.

Fixpoint depth (t:roseTree) : nat :=
match t with 
| node [] => 0
| node xs => 1+maxList(map depth xs)
end.

Fixpoint size (t:roseTree) : nat.
destruct t.
refine (S _).
induction h.
- exact 0.
- exact (size a + IHh).
Defined.

Definition ex :=
node [node []; node [node[];node[];node[]]].

Compute (depth ex).
Compute (size ex).

Definition roseTree_induct : 
forall (P:roseTree -> Prop),
(forall xs, (forall t, In t xs -> P t) -> P (node xs)) ->
forall r, P r.
Proof.
    intros P H.
    refine (fix f r := _).
    destruct r.
    apply H.
    induction h.
    - intros _ [].
    - intros t [<-|?].
        + apply f.
        + now apply IHh.
Defined.

Require Import Lia.
From Hammer Require Import Hammer.

Lemma depth_eq x xs: depth (node(x::xs)) = max (1+depth x) (depth (node xs)).
Proof.
    cbn [depth map maxList].
    destruct xs;cbn [map depth maxList];lia.
Qed.

Lemma size_eq x xs: size(node(x::xs)) = size(x) + size(node xs).
Proof.
    cbn;lia.
Qed.


Goal forall t, depth t < size t.
Proof.
    apply roseTree_induct.
    induction xs;intros.
    - cbn;lia.
    - 
    (* hammer. *)
    rewrite depth_eq, size_eq.
    assert(depth a < size a).
    {
        apply H;now left.
    }
    assert(depth (node xs) < size (node xs)).
    {
        apply IHxs;intros;apply H;now right.
    }
    lia.
Qed.



Goal forall t, 1+depth t <= size t.
Proof.
    induction t.
    induction h;trivial.
    - 
    destruct h;trivial.
    simpl.
Restart.
    apply roseTree_induct.
    intros [] H;trivial.
    simpl.