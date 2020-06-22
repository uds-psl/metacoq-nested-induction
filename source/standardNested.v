
(** Register often used container types with helpful assumption and proof functions **)

Require Import helperGen.

Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.

From Equations Require Import Equations.
Require Import nested_datatypes.

Open Scope string_scope.


Print prod.
Print VectorDef.t.

(* list satisfy *)
Inductive is_list A (PA:A->Type) : list A -> Type :=
| is_nil : is_list A PA nil
| is_cons a (pa: PA a) l (pl:is_list A PA l): is_list A PA (a::l).

Definition listAssumption2 {X} (P:X->Type) (xs:list X) := is_list _ P xs.

Lemma is_list_in {X} (P:X->Prop) xs : is_list X P xs -> forall x, In x xs -> P x.
Proof.
  intros.
  induction X0.
  - now contradict H.
  - destruct H as [->|H].
    + apply pa.
    + apply IHX0, H.
Qed.

Definition listProof2 {X} (P:X->Type) (f:forall x, P x) (xs:list X) : listAssumption2 P xs.
Proof.
  unfold listAssumption2.
  induction xs.
  - constructor.
  - constructor.
    + apply f.
    + apply IHxs.
Defined.

Fixpoint F (n : nat) : nat := (fun _=> O)(F n).
Compute (F 2).

Definition prodAssumption X (Px:X->Type) Y (Py:Y->Type) (t:X*Y) : Type := let (x,y) := t in (Px x) * (Py y).
Definition prodProof X (Px:X->Type) (fx:forall x, Px x) Y (Py:Y->Type) (fy:forall y, Py y) (t:X*Y) : prodAssumption _ Px _ Py t.
Proof.
  destruct t.
  cbn. split;[apply fx | apply fy].
Defined.

Compute (forall T p pd t,prodAssumption T p nat pd t).


Definition listAssumption {X} (P:X->Prop) (xs:list X) := forall t, In t xs -> P t.

Definition listProof {X} (P:X->Prop) (f:forall x, P x) (xs:list X) : listAssumption P xs :=
(list_ind (fun xs0 : list X => listAssumption P xs0)
            (fun (t : X) (H0 : In t []) => match H0 return (P t) with
                                                  end)
            (fun (a : X) (xs0 : list X) (IHxs : listAssumption P xs0)
               (t : X) (H0 : In t (a :: xs0)) =>
             match H0 with
             | or_introl H1 => Coq.Init.Logic.eq_ind a (fun t0 : X => P t0) (f a) t H1
             | or_intror H1 => IHxs t H1
             end) xs).

(* invalid f only for smaller instances *)
(* Goal forall X (P:X->Prop) (f:forall x, P x) (xs:list X) , listAssumption P xs. *)
(* Proof. *)
(*   unfold listAssumption. *)
(*   intros. *)
(*   apply f. *)
(* Qed. *)




Inductive is_prod X Y (Px : X->Type) (Py: Y -> Type) : X*Y->Type :=
| is_pair x y (px:Px x) (py:Py y) : is_prod X Y Px Py (x,y).
Definition prodProof2 {X Y} (Px:X->Type) (Py:Y->Type) (fx:forall x, Px x) (fy:forall y, Py y) (t:X*Y) : is_prod _ _ Px Py t.
Proof.
  destruct t.
  cbn. split;[apply fx | apply fy].
Defined.

Definition vec:=Vector.t.

Inductive is_vec {X:Type} (Px: X->Type) : forall n, vec X n -> Type :=
| is_nilV : is_vec Px 0 (@Vector.nil _)
| is_consV (x:X) (px:Px x) n (xs:Vector.t X n) (pxs:is_vec Px n xs): is_vec Px (S n) (Vector.cons X x n xs).


Definition vecProof {X} (P:X->Type) (f:forall x, P x) n (xs:vec X n) : is_vec P n xs.
Proof.
  induction xs.
  - constructor.
  - constructor.
    + apply f.
    + apply IHxs.
Defined.

Definition rtree_ind_MC_Test
     : forall (A : Type) (p : rtree A -> Type),
       (forall a : A, p (Leaf A a)) ->
       (forall l : list (rtree A), is_list (rtree A) p l -> p (Node A l)) -> forall inst : rtree A, p inst :=
fun (A : Type) (p : rtree A -> Type) (H_Leaf : forall a : A, p (Leaf A a))
  (H_Node : forall l : list (rtree A), is_list (rtree A) p l -> p (Node A l)) =>
fix f (inst : rtree A) : p inst :=
  match inst as inst0 return (p inst0) with
  | @Leaf _ a => H_Leaf a
  | @Node _ l =>
      H_Node l
        ((fix F (l0 : list (rtree A)) : is_list (rtree A) p l0 :=
            match l0 as l1 return (is_list (rtree A) p l1) with
            | [] => is_nil (rtree A) p
            | y :: l1 => is_cons (rtree A) p y (f y) l1 (F l1)
            end) l)
  end.

Inductive is_rtree X (Px : X -> Type) : rtree X -> Type :=
| is_Leaf x (px: Px x) : is_rtree X Px (Leaf X x)
| is_Node xs (pxs: is_list (rtree X) (is_rtree X Px) xs) : is_rtree X Px (Node X xs).


Definition rtreeProof2 X (P:X->Type) (f:forall x, P x) (r:rtree X) : is_rtree X P r.
Proof.
  revert r.
  refine (fix IH r := _).
  destruct r.
  - constructor. apply f.
  - constructor.
    apply listProof2.
    apply IH.
Defined.

Definition rtreeProof X (P:X->Type) (f:forall x, P x) (r:rtree X) : is_rtree X P r.
Proof.
  induction r using rtree_ind_MC_Test.
  - constructor. apply f.
  - constructor. apply X0.
Defined.

Definition roseTreeO3_ind_MC := 
fun (X : Type) (p : roseTreeO3 X -> Prop)
  (H_treeO3 : forall (x : X) (xs : list X)
                (xxs : roseTreeO3 X),
              p xxs ->
              forall xsxs : list (roseTreeO3 X),
              is_list (roseTreeO3 X)
                (fun H : roseTreeO3 X => p H) xsxs ->
              p (treeO3 X x xs xxs xsxs)) =>
fix f (inst : roseTreeO3 X) : p inst :=
  match inst as inst0 return (p inst0) with
  | @treeO3 _ x xs xxs xsxs =>
      H_treeO3 x xs xxs (f xxs) xsxs
        ((fix F (l : list (roseTreeO3 X)) :
            is_list (roseTreeO3 X)
              (fun H : roseTreeO3 X => p H) l :=
            match
              l as l0
              return
                (is_list (roseTreeO3 X)
                   (fun H : roseTreeO3 X => p H) l0)
            with
            | [] =>
                is_nil (roseTreeO3 X)
                  (fun H : roseTreeO3 X => p H)
            | y :: l0 =>
                is_cons (roseTreeO3 X)
                  (fun H : roseTreeO3 X => p H) y
                  (f y) l0 (F l0)
            end) xsxs)
  end.

Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
    nilᵗ : listᵗ A Aᵗ [] | consᵗ : forall H : A, Aᵗ H -> forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0).

Inductive roseTreeO3ᵗ (X : Type) (Xᵗ : X -> Type) : roseTreeO3 X -> Prop :=
    treeO3ᵗ : forall x : X,
               Xᵗ x ->
               forall xs : list X,
               is_list X Xᵗ xs ->
               forall xxs : roseTreeO3 X,
               roseTreeO3ᵗ X Xᵗ xxs ->
               forall xsxs : list (roseTreeO3 X),
               is_list (roseTreeO3 X) (roseTreeO3ᵗ X Xᵗ) xsxs ->
               roseTreeO3ᵗ X Xᵗ (treeO3 X x xs xxs xsxs).

Definition rtreeO3Proof X (P:X->Type) (f:forall x, P x) (r:roseTreeO3 X) : roseTreeO3ᵗ X P r.
Proof.
  induction r using roseTreeO3_ind_MC.
  - constructor.
    + apply f.
    + apply listProof2.
      apply f.
    + apply IHr.
    + apply X0. (* alternative: listProof2 & IH explizit with fix *)
Restart.
  revert r.
  refine (fix IH r := _).
  destruct r.
  - constructor.
    + apply f.
    + apply listProof2.
      apply f.
    + apply IH.
    + apply listProof2.
      apply IH.
Qed.

Inductive Accᵗ (A : Type) (Aᵗ : A -> Type) (R : A -> A -> Prop)
(Rᵗ : forall H : A,
      Aᵗ H -> forall H0 : A, Aᵗ H0 -> R H H0 -> Prop)
(x : A) (xᵗ : Aᵗ x) : Acc R x -> Prop :=
    Acc_introᵗ : forall
                   H : forall y : A, R y x -> Acc R y,
                 (forall (y : A) (yᵗ : Aᵗ y)
                    (H0 : R y x),
                  Rᵗ y yᵗ x xᵗ H0 ->
                  Accᵗ A Aᵗ R Rᵗ y yᵗ (H y H0)) ->
                 Accᵗ A Aᵗ R Rᵗ x xᵗ (Acc_intro x H).

Definition AccProof (A : Type) (Aᵗ : A -> Type) (R : A -> A -> Prop)
(Rᵗ : forall H : A,
      Aᵗ H -> forall H0 : A, Aᵗ H0 -> R H H0 -> Prop)
(x : A) (xᵗ : Aᵗ x) (r : Acc R x) : Accᵗ A Aᵗ R Rᵗ x xᵗ r.
Proof.
  intros.
  revert x xᵗ r.
  refine (fix IH x xᵗ r := _).
  destruct r.
  constructor.
  intros.
  apply IH.
Defined.

Inductive boolᵗ : bool -> Set :=
  trueᵗ : boolᵗ true | falseᵗ : boolᵗ false.
Inductive natᵗ : nat -> Set :=
    Oᵗ : natᵗ 0
  | Sᵗ : forall H : nat, natᵗ H -> natᵗ (S H).

Inductive
containerInd4ᵗ (b : bool) (bᵗ : boolᵗ b)
(X : Type) (Xᵗ : X -> Type) (n : nat)
(nᵗ : natᵗ n)
  : containerInd4 b X n -> Prop :=
  c4ᵗ : containerInd4ᵗ b bᵗ X Xᵗ n nᵗ (c4 b X n).

Definition containerInd4Proof (b : bool) (bᵗ : boolᵗ b)
(X : Type) (Xᵗ : X -> Type) (n : nat)
(nᵗ : natᵗ n) (a:containerInd4 b X n) :
  containerInd4ᵗ b bᵗ X Xᵗ n nᵗ a.
Proof.
  destruct a.
  constructor.
Defined.

Inductive
vecᵗ (A : Type) (Aᵗ : A -> Type)
  : forall H : nat, natᵗ H -> vec A H -> Type :=
    vecnilᵗ : vecᵗ A Aᵗ 0 Oᵗ (@Vector.nil A)
  | vecconsᵗ : forall H : A,
               Aᵗ H ->
               forall (n : nat) (nᵗ : natᵗ n)
                 (H0 : vec A n),
               vecᵗ A Aᵗ n nᵗ H0 ->
               vecᵗ A Aᵗ (S n) (Sᵗ n nᵗ)
                    (@Vector.cons A H n H0).

Definition vecProof2
           (A : Type) (Aᵗ : A -> Type) (fA: forall a, Aᵗ a)
           (n : nat) (H:natᵗ n) (fn: forall n, natᵗ n)
           (a:vec A n) :
  vecᵗ A Aᵗ n H a.
Proof.
  induction a in H, fn |- *.
  - depelim H.
    constructor.
  - depelim H.
    constructor.
    + apply fA.
    + apply IHa.
      apply fn.
Qed.


Inductive
vecᵗ' (A : Type) (Aᵗ : A -> Type)
  : forall H : nat, vec A H -> Type :=
    vecnilᵗ' : vecᵗ' A Aᵗ 0 (@Vector.nil A)
  | vecconsᵗ' : forall H : A,
               Aᵗ H ->
               forall (n : nat) 
               (* (nᵗ : natᵗ n) *)
                 (H0 : vec A n),
               vecᵗ' A Aᵗ n H0 ->
               vecᵗ' A Aᵗ (S n)
                    (@Vector.cons A H n H0).

Definition vecProof2'
           (A : Type) (Aᵗ : A -> Type) (fA: forall a, Aᵗ a)
           (n : nat) 
           (* (fn: forall n, natᵗ n) *)
           (a:vec A n) :
  vecᵗ' A Aᵗ n a.
Proof.
  induction a.
  - constructor.
  - constructor.
    + apply fA.
    + apply IHa.
Qed.

Print mfixpoint.
Check list.

Print def.

Definition defAssumption {X} (P:X->Type) (x:def X) :=
  prod
    (P (dtype x))
    (P (dbody x)).
Definition defProof {X} (P:X->Type) (f:forall x, P x) (x:def X) : defAssumption P x.
  now constructor.
Defined.

Definition mfixpointAssumption {X} (P:X->Type) (x:mfixpoint X) := is_list _ (defAssumption P) x.
Definition mfixpointProof {X} (P:X->Type) (f:forall x, P x) (x:mfixpoint X) : mfixpointAssumption P x.
  now apply listProof2, defProof.
Defined.

Print All_Forall.All.
Print is_list.
Print listProof2.


Instance listInst : registered list := 
{|
    assumption := @listAssumption2;
    proof := @listProof2
|}.

Instance prodInst : registered prod := 
{|
    assumption := @prodAssumption;
    proof := @prodProof
|}.

Instance vecInst : registered VectorDef.t := 
{|
    assumption := @is_vec;
    proof := @vecProof
|}.

Instance rtreeInst : registered rtree := 
{|
    assumption := @is_rtree;
    proof := @rtreeProof
|}.

Instance containerInd4Inst : registered containerInd4 := 
{|
    assumption := @containerInd4ᵗ;
    proof := @containerInd4Proof
|}.

Instance defInst : registered def := 
{|
    assumption := @defAssumption;
    proof := @defProof
|}.

Instance mfixpointInst : registered mfixpoint := 
{|
    assumption := @mfixpointAssumption;
    proof := @mfixpointProof
|}.
