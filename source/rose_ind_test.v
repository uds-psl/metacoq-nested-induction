(** induction principles for rose tree **)

Require Import destruct_lemma.
Require Import nested_datatypes.
Unset Strict Unquote Universe Mode.
Require Import standardNested.
Require Import addContainer.
Require Import Modes.


Require Import MetaCoq.Template.All.
Import MonadNotation.
Require Import String.

Print roseTree.

Require Import List.

Goal forall (P:roseTree -> Prop), (forall xs, (forall x, In x xs -> P x) -> P (tree xs)) -> forall r, P r.
refine (
  fun P H =>
  fix f r :=
  match r with
  tree xs => H xs _
  end
).
induction xs.
- intros _ [].
- intros x [<- | ?%IHxs].
  + apply f.
  + apply H1.
  Show Proof.
Qed.


Goal forall (P:roseTree -> Prop), (forall xs, All P xs -> P (tree xs)) -> forall r, P r.
refine (
  fun P H =>
  fix f r :=
  match r with
  tree xs => H xs _
  end
).
induction xs;constructor.
- apply f.
- apply IHxs.
Show Proof.
Qed.
(*  *)
Print listInst.
(*  *)
Goal forall (P:roseTree -> Prop), (forall xs, @is_list roseTree P xs -> P (tree xs)) -> forall r, P r.
refine (
  fun P H =>
  fix f r :=
  match r with
  tree xs => H xs _
  end
).
induction xs;constructor.
- apply f.
- apply IHxs.
Show Proof.
Restart.
refine (
  fun P H =>
  fix f r :=
  match r with
  tree xs => H xs _
  end
).
now apply listProof2.
Show Proof.
Qed.
(*  *)
Scheme foterm_induct := Induction for foterm Sort Type.
Print foterm_induct.

(* Require Import MetaCoq.Template.All.
MetaCoq Run Scheme Induction for term.
Print term_ind_MC.
Scheme term_induct := Induction for term Sort Type.
Print term_induct. *)