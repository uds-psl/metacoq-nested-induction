(** extensive tests with expected results for some nested types **)

(* Require Import nested. *)
(* Require Import destruct_lemma. *)
(* Require Import nested_datatypes. *)
Load nested.

Require Import Modes.

MetaCoq Run (
  changeMode helperGen.nestedMode true
).

MetaCoq Run (create roseTreeO11 true false).
MetaCoq Run (runElim roseTreeO11 true true None (Some <% Prop %>)).
Print roseTreeO11_ind_MC.

(* MetaCoq Run (x <- tmQuoteInductive "nat"  ;; tmPrint x). *)
(* MetaCoq Run (create nat true false). *)
(* MetaCoq Run (create nat true true). *)

Definition eq_ind {A} := @Coq.Init.Logic.eq_ind A.

(* Print roseTree. *)
(* MetaCoq Run (create roseTree true false). *)
(* MetaCoq Run (runElim roseTree true false None (Some <% Prop %>)). *)
(* MetaCoq Run (runElim roseTree true true None (Some <% Prop %>)). *)
(* Check roseTree_ind_MC. *)
(* Print roseTree_ind_MC. *)

Goal forall (P:roseTree -> Prop),
    (forall xs, (forall t, In t xs -> P t) -> P (tree xs)) ->
    forall r, P r.
Proof.
  intros P H.
  refine(
      fix f r : P r := _).
  destruct r.
  apply H.
  (* intros. *)
  (* apply f. *)

  induction xs.
  - intros _ [].
  - intros t [-> | H1].
    + apply f.
    + apply IHxs, H1.

Restart.
  intros p H.
  refine (fix f r := _).
  destruct r.

  apply H.
  induction xs.
  - intros t [].
  - intros t [<-|H1].
  (* - intros t [->|H1]. *)
    + apply f.
    + now apply IHxs.
      Show Proof.
      (*

(fun (p : roseTree -> Prop) (H : forall xs : list roseTree, (forall t : roseTree, In t xs -> p t) -> p (tree xs))
 =>
 fix f (r : roseTree) : p r :=
   match r as r0 return (p r0) with
   | tree xs =>
       H xs
         (list_ind (fun xs0 : list roseTree => forall t : roseTree, In t xs0 -> p t)
            (fun (t : roseTree) (H0 : In t []) => match H0 return (p t) with
                                                  end)
            (fun (a : roseTree) (xs0 : list roseTree) (IHxs : forall t : roseTree, In t xs0 -> p t) 
               (t : roseTree) (H0 : In t (a :: xs0)) =>
             match H0 with
             | or_introl H1 => eq_ind a (fun t0 : roseTree => p t0) (f a) t H1
             | or_intror H1 => IHxs t H1
             end) xs)
   end)

       *)
Qed.


Goal forall X (P:roseTree2 X -> Prop),
    (forall x xs, (forall t, In t xs -> P t) -> P (tree2 X x xs)) ->
    forall r, P r.
Proof.
  intros X p H.
  refine (fix f r := _).
  destruct r.

  apply H.
  induction xs.
  - intros t [].
  - intros t [<-|H1].
    + apply f.
    + now apply IHxs.
Qed.



Goal forall (P:roseTree3 -> Prop),
    (forall xs, (forall t, In t xs -> P t) -> P (tree3 xs)) ->
    (forall n, P (node3 n)) ->
    forall r, P r.
Proof.
  intros p H1 H2.
  refine (fix f r := _).
  destruct r.
  2: {
    apply H2.
  }

  apply H1.
  induction xs.
  - intros t [].
  - intros t [<-|H3].
    + apply f.
    + now apply IHxs.
Qed.


Goal forall (P:roseTree4 -> Prop),
    (forall f, (forall (H:0=0), forall t, In t (f H) -> P t) -> P (tree4 f)) ->
    forall r, P r.
Proof.
  intros p H.
  refine (fix f r := _).
  destruct r.

  apply H.
  intros H0.
  induction (xs H0).
  - intros t [].
  - intros t [<-|H3].
    + apply f.
    + now apply IHl.
Qed.


(* Print Coq.Default.eq_ind. *)

Definition listAssumptionTest {X} (P:X->Prop) (xs:list X) := forall t, In t xs -> P t.

(* Definition listProofTest {X} (P:X->Prop) (f:forall x, P x) (xs:list X) := *)
(* (list_ind (fun xs0 : list X => forall t : X, In t xs0 -> P t) *)
(*             (fun (t : X) (H0 : In t []) => match H0 return (P t) with *)
(*                                                   end) *)
(*             (fun (a : X) (xs0 : list X) (IHxs : forall t : X, In t xs0 -> P t) *)
(*                (t : X) (H0 : In t (a :: xs0)) => *)
(*              match H0 with *)
(*              | or_introl H1 => eq_ind a (fun t0 : X => P t0) (f a) t H1 *)
(*              | or_intror H1 => IHxs t H1 *)
(*              end) xs). *)


Definition listProofTest {X} (P:X->Prop) (f:forall x, P x) (xs:list X) : listAssumptionTest P xs :=
(list_ind (fun xs0 : list X => listAssumptionTest P xs0)
            (fun (t : X) (H0 : In t []) => match H0 return (P t) with
                                                  end)
            (fun (a : X) (xs0 : list X) (IHxs : listAssumptionTest P xs0)
               (t : X) (H0 : In t (a :: xs0)) =>
             match H0 with
             | or_introl H1 => eq_ind a (fun t0 : X => P t0) (f a) t H1
             | or_intror H1 => IHxs t H1
             end) xs).

(* Print listProofTest. *)

Goal forall (P:roseTree -> Prop),
    (forall xs, listAssumptionTest P xs -> P (tree xs)) ->
    forall r, P r.
Proof.
  refine (fun P H =>
            fix f r :=
            match r with
              | tree xs => _
            end
         ).
  apply H.
  apply (listProofTest P f xs).
Qed.

Goal forall X (P:roseTree2 X -> Prop),
    (forall x xs, listAssumptionTest P xs -> P (tree2 X x xs)) ->
    forall r, P r.
Proof.
  refine (fun X P H =>
            fix f r :=
            match r with
              | tree2 x xs => H x xs _
            end
         ).
  apply (@listProofTest (roseTree2 X) P f xs).
Qed.


Goal forall (P:roseTree4 -> Prop),
    (forall f, (forall (H:0=0), listAssumptionTest P (f H)) -> P (tree4 f)) ->
    forall r, P r.
Proof.
  refine (fun P H =>
            fix f r :=
            match r with
            | tree4 g =>
              H g (fun a => let xs := g a in _)
            end
         ).
  apply (listProofTest P f xs).
Qed.


Goal forall (P:forall n, roseTree5 n -> Prop),
    (forall xs, (listAssumptionTest (P 1) xs) -> P 0 (tree5 xs)) ->
    forall n r, P n r.
Proof.
  refine (fun P H =>
            fix f n r {struct r} :=
            match r with
            | tree5 xs =>
              H xs _
            end
         ).
  apply (listProofTest (P 1) (f 1) xs).
  (* Problem for different indices
     but this should not occur because
     parameters have type list (X ...)
     the index therefore does not change in a list
   *)
Qed.

Print O.




(* Inductive roseTreeNN7 := *)
(*   treeNN7 (xs:rtree roseTreeNN7). *)

Print trivialPred.
Print trivialProof.


MetaCoq Quote Definition roseInd :=
    (* forall (P:roseTree -> Prop), *)
    (* (forall xs, listAssumptionTest P xs -> P (tree xs)) -> *)
    (* forall r, P r := *)
  (fun P H =>
    fix f r :=
    match r with
      | tree xs => H xs (@listProofTest (roseTree) P f xs)
    end).



MetaCoq Run (p <- tmQuoteInductive "roseTree";;
               t <- tmEval lazy p;;
               tmPrint t).
MetaCoq Run (p <- tmQuoteInductive "list";;
               t <- tmEval lazy p;;
               tmPrint t).

Print even.
MetaCoq Run (p <- tmQuoteInductive "even";;
               t <- tmEval lazy p;;
               tmPrint t).
MetaCoq Run (p <- tmQuote even;;
               t <- tmEval lazy p;;
               tmPrint t).
MetaCoq Run (p <- tmQuote odd;;
               t <- tmEval lazy p;;
               tmPrint t).


(*
roseInd = 
tLambda (nNamed "P")
  (tProd nAnon (tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} [])
     (tSort (Universe.make'' (Level.lProp, false) [])))
  (tLambda (nNamed "H")
     (tProd (nNamed "x")
        (tApp (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
           [tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} []])
        (tProd (nNamed "x0")
           (tApp (tConst "Top.listAssumptionTest" [])
              [tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} []; tRel 1; tRel 0])
           (tApp (tRel 2)
              [tApp (tConstruct {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} 0 []) [tRel 1]])))
     (tFix
        [{|
         dname := nNamed "f";
         dtype := tProd (nNamed "r") (tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} [])
                    (tApp (tRel 2) [tRel 0]);
         dbody := tLambda (nNamed "r") (tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} [])
                    (tCase ({| inductive_mind := "Top.roseTree"; inductive_ind := 0 |}, 0)
                       (tLambda (nNamed "r") (tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} [])
                          (tApp (tRel 4) [tRel 0])) (tRel 0)
                       [(1,
                        tLambda (nNamed "xs")
                          (tApp (tInd {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} [])
                             [tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} []])
                          (tApp (tRel 3)
                             [tRel 0;
                             tApp (tConst "Top.listProofTest" [])
                               [tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} []; 
                               tRel 4; tRel 2; tRel 0]]))]);
         rarg := 0 |}] 0))
     : term
 *)

(*
tApp (tConst "Top.listProofTest" [])
  [tInd {| inductive_mind := "Top.roseTree"; inductive_ind := 0 |} []; 
  tRel 4; tRel 2; tRel 0]

listProofTest application argument
 *)
MetaCoq Run (p <- tmQuote (listProofTest);;
               t <- tmEval lazy p;;
               tmPrint t).


(* have *)
(*   λ (p : ∀ (inst : roseTree), Prop). *)
(* λ (H_tree : ∀ (xs : (list roseTree)), ∀ (IH_xs : (((destruct_lemma.listAssumption2 roseTree) λ (_ : roseTree). (R2 R0)) R0)), (R2 (tree R1))). *)
(* (fix f : ∀ (inst : roseTree), (R2 R0) :=  *)
(* λ (inst : roseTree).  *)
(* match (P:0) R0 return λ (inst : roseTree). (R4 R0) with *)
(*  | (1) λ (xs : (list roseTree)). ((R3 R0) ((((destruct_lemma.listAssumption2 roseTree) λ (_ : roseTree). (R5 R0)) λ (_ : roseTree). (R3 R0)) R0)) *)
(* end) *)


(* want *)
(* λ (p : ∀ (inst : roseTree), Prop). *)
(* λ (H_tree : ∀ (xs : (list roseTree)), ∀ (IH_xs : (((destruct_lemma.listAssumption2 roseTree) λ (_ : roseTree). (R2 R0)) R0)), (R2 (tree R1))). *)
(* (fix f : ∀ (inst : roseTree), (R2 R0) :=  *)
(* λ (inst : roseTree).  *)
(* match (P:0) R0 return λ (inst : roseTree). (R4 R0) with *)
(*  | (1) λ (xs : (list roseTree)). ((R3 R0) ((((destruct_lemma.listProof2 roseTree) λ (_ : roseTree). (R5 R0)) λ (_ : roseTree). (R3 R0)) R0)) *)
(* end) *)



MetaCoq Quote Definition roseInd4 :=
(* Goal forall (P:roseTree4 -> Prop), *)
(*     (forall f, (forall (H:0=0), forall t, In t (f H) -> P t) -> P (tree4 f)) -> *)
(*     forall r, P r. *)
  (fun P H =>
    fix f r :=
     match r with
      | tree4 g =>
        H g (fun a => @listProofTest (roseTree4) P f (g a))
        (* H g (fun a => let xs := g a in *)
        (*            @listProofTest (roseTree4) P f xs *)
        (*     ) *)
     end).
Print roseInd4.


MetaCoq Quote Definition roseInd5 :=
  (fun P H =>
    fix f n r :=
     match r with
      | tree5 xs =>
        H xs (@listProofTest (@roseTree5 1) (P 1) (f 1) xs)
     end).
Print roseInd5.


(* PI8 *)
(* λ (n : nat). *)
(* λ (p : (nat) -> ∀ (inst : ((roseTreePI8 R1) R0)), Ldestruct_lemma.447). *)
(* λ (H_treePI8 : ((list ((roseTreePI8 (S R1)) O))) -> ((((destruct_lemma.listAssumption2 ((roseTreePI8 (S R2)) O)) λ (_ : ((roseTreePI8 (S R2)) O)). ((R2 O) R0)) R0)) -> ((R2 (S O)) ((treePI8 R3) R1))). *)
(* (fix f : (nat) -> ∀ (inst : ((roseTreePI8 R3) R0)), ((R3 R1) R0) := *)
(* λ (_ : nat). λ (inst : ((roseTreePI8 R4) R0)). *)
(* match (P:1) R0 return λ (_ : nat). λ (inst : ((roseTreePI8 R6) R0)). ((R6 R1) R0) with *)
(*  | (1) λ (_ : (list ((roseTreePI8 (S R5)) O))). ((R4 R0) ((((destruct_lemma.listProof2 ((roseTreePI8 (S R6)) O)) λ (_ : ((roseTreePI8 (S R6)) O)). ((R6 O) R0)) λ (_ : ((roseTreePI8 (S R6)) O)). ((R4 O) R0)) R0)) *)
(* end) *)



Definition size (r:rtree True) : nat.
Proof.
  induction r as [|l IHl] using rtree_ind_MC.
  - exact 1.
  - destruct l.
    + exact 0.
    + inversion IHl;subst.
      exact (S pa).
Restart.
  induction r as [|l IHl] using rtree_ind_MC.
  - exact 1.
  - induction IHl.
    + exact 0.
    + exact (S IHIHl).
Restart. (* correct *)
  induction r as [|l IHl] using rtree_ind_MC.
  - exact 1.
  - induction l.
    + exact 0.
    + inversion IHl;subst.
      exact (pa+IHl0 pl).
Restart. (* correct *)
  refine(
      rtree_ind_MC
        _
        (fun _ => nat)
        (fun _ => 1)
        (fun xs H =>
           is_list_rect
             _
             (fun _ => nat)
             (fun _ _ => nat)
             0
             (fun _ tn _ _ rn => tn + rn)
             xs
             H
        )
        r
    ).
Defined.

Print size.
Compute (size (@Leaf True I)).
Compute (size (@Node True [])).
Compute (size (Node _ [Leaf _ I])).
Compute (size (Node _ [Leaf _ I;Leaf _ I])).
Compute (size (Node _ [Leaf _ I;Leaf _ I;Leaf _ I])).
Compute (size (Node _ [Leaf _ I;Leaf _ I;Leaf _ I;Leaf _ I])).
Compute (size (Node _ [Leaf _ I;Node _ []])).
Compute (size (Node _ [Leaf _ I;Node _ [Leaf _ I]])).
Compute (size (Node _ [Leaf _ I;Node _ [Leaf _ I;Leaf _ I]])).
Compute (size (Node _ [Leaf _ I;Node _ [Leaf _ I;Leaf _ I];Leaf _ I])).



Goal forall (P:roseTreeNN4->Prop)
       (H:forall (x:nat*roseTreeNN4), @prodAssumption nat (trivialPred nat) (roseTreeNN4) (P) x  -> P (treeNN4 x))
       (r:roseTreeNN4), P r.
Proof.
  intros P H.
  refine (fix f r := _).
  destruct r.
  apply H.
  apply prodProof.
  - apply trivialProof.
  - apply f.
Qed.


(* NN7 *)
(* (IH_a : (destruct_lemma.prodAssumption *)
(*            (roseTreeNN7) *)
(*            (λ (argObj : roseTreeNN7). (R2 (R0))) *)
(*            ((nat) -> nat) *)
(*            (λ (argObj : (nat) -> nat). *)
(*             (nat) -> *)
(*             ((destruct_lemma.trivialPred (nat) (R0))) -> (destruct_lemma.trivialPred (nat) ((R2 (R1))))) *)
(*            (R0))) *)
(*   (IH_a : (destruct_lemma.prodAssumption *)
(*              (roseTreeNN7) *)
(*              (λ (argObj : roseTreeNN7). (R2 (R0))) *)
(*              ((nat) -> nat) *)
(*              (λ (argObj : (nat) -> nat). *)
(*               (nat) -> *)
(*               (destruct_lemma.trivialPred (nat) ((R1 (R0))))) *)
(*              (R0))) *)



(* DN7 *)
(* λ (p : ∀ (inst : roseTreeDN5), Ldestruct_lemma.317). *)
(* λ (H_treeDN5 : ∀ (a : (list ((prod (nat) ((list (roseTreeDN4))))))), *)
(* (* useless *) *)
(*       ∀ (IH_a : (destruct_lemma.listAssumption2 *)
(*                    ((prod (nat) ((list (roseTreeDN4))))) *)
(*                    (λ (argObj : (prod (nat) ((list (roseTreeDN4))))). *)
(*                     (destruct_lemma.prodAssumption *)
(*                        (nat) *)
(*                        (λ (argObj : nat). (destruct_lemma.trivialPred (nat) (R0))) *)
(*                        ((list (roseTreeDN4))) *)
(*                        (λ (argObj : (list (roseTreeDN4))). *)
(*                         (destruct_lemma.listAssumption2 *)
(*                            (roseTreeDN4) *)
(*                            (λ (argObj : roseTreeDN4). (destruct_lemma.trivialPred (roseTreeDN4) (R0))) *)
(*                         (R0))) *)
(*                     (R0))) *)
(*                    (R0))), *)
(*         (R2 ((treeDN5 (R1))))). *)



(* (H_treeO11 : ∀ (x : (list (((eq (nat) (O) (O))) -> roseTreeO11))), *)
(*     ∀ (IH_x : (destruct_lemma.listAssumption2 *)
(*                  (((eq (nat) (O) (O))) -> roseTreeO11) *)
(*                  (λ (argObj : ((eq (nat) (O) (O))) -> roseTreeO11). *)
(*                   ((eq (nat) (O) (O))) -> (R3 ((R1 (R0)))) *)
(*                  ) *)
(*                  (R0) *)
(*       )) *)
(*     , (R2 ((treeO11 (R1))))) *)



Print listAssumption2.
Definition roseTreeO11Ind :
  forall (P:roseTreeO11 -> Prop)
    (H:forall f,
        @listAssumption2 (0=0 -> roseTreeO11) (fun h => (forall x, P (h x))) f ->
        P (treeO11 f) ) (r:roseTreeO11), P r.
  refine (
      fun P H =>
    fix f inst : P inst :=
    match inst with
      treeO11 f =>
      H f _
        (* (listProof2 (0=0 -> roseTreeO11) (fun h => forall x, P (h x)) (fun f => )) *)
    end).
  apply listProof2.
  intros.
  apply f0.
  Show Proof.
  (*
(fun (P : roseTreeO11 -> Prop)
   (H : forall f : list (0 = 0 -> roseTreeO11),
        listAssumption2 (fun h : 0 = 0 -> roseTreeO11 => forall x : 0 = 0, P (h x)) f -> P (treeO11 f)) =>
 fix f (inst : roseTreeO11) : P inst :=
   match inst as inst0 return (P inst0) with
   | treeO11 f0 =>
       H f0
         (listProof2 (fun h : 0 = 0 -> roseTreeO11 => forall x : 0 = 0, P (h x))
            (fun (x : 0 = 0 -> roseTreeO11) (x0 : 0 = 0) => f (x x0)) f0)
   end)
   *)
Defined.
Print roseTreeO11Ind.



(*
done
complete generalization:
H is P (constructor args)
each rec assumption is P (assumption args)
and for Type some nesting around
 *)


(* MetaCoq Run (create roseTreeO11 true false). *)
(* MetaCoq Run (runElim roseTreeO11 true true None (Some <% Prop %>)). *)
(* Print roseTreeO11_ind_MC. *)


(* λ (p : ∀ (inst : roseTreeO11), LTop.4049). *)
(* λ (H_treeO11 : ∀ (x : (list (((eq (nat) (O) (O))) -> roseTreeO11))), ∀ (IH_x : (Top.listAssumption2 (((eq (nat) (O) (O))) -> roseTreeO11) (R0))), (R2 ((treeO11 (R1))))). *)
(* (fix f : ∀ (inst : roseTreeO11), (R2 (R0)) := *)
(* λ (inst : roseTreeO11). *)
(* match (P:0) R0 return λ (inst : roseTreeO11). (R4 (R0)) with *)
(*  | (1) λ (x : (list (((eq (nat) (O) (O))) -> roseTreeO11))). (R3 (R0) ((Top.listProof2 (((eq (nat) (O) (O))) -> roseTreeO11) (R0)))) *)
(* end). *)




(* Variable Preds : Type. *)
(* Variable pred_ar : Preds -> nat. *)
(* Variable Funcs : Type. *)
(* Variable fun_ar : Funcs -> nat. *)

(* Inductive foterm : Type := *)
(*   | var_foterm : (nat) -> foterm *)
(*   | Func : forall (f : Funcs), Vector.t foterm (fun_ar f) -> foterm . *)

(* Inductive form : Type := *)
(*   | Fal : form *)
(*   | Top : form *)
(*   | Pred : forall (P : Preds), Vector.t foterm (pred_ar P) -> form *)
(*   | Impl : form -> form -> form *)
(*   | Conj : form -> form -> form *)
(*   | Disj : form -> form -> form *)
(*   | All : form -> form *)
(*   | Ex : form -> form. *)

(* have  *)
(* λ (p : ∀ (inst : foterm), Ldestruct_lemma.452). *)
(* λ (H_var_foterm : (nat) -> (R1 (var_foterm R0))). *)
(* λ (H_Func : ∀ (f : destruct_lemma.Funcs), (((t foterm) (destruct_lemma.fun_ar R0))) -> ((((((is_vec foterm) λ (_ : foterm). (R4 R0)) (destruct_lemma.fun_ar R1)) *)

(* λ (_ : (destruct_lemma.fun_ar R1)). ((destruct_lemma.trivialPred (destruct_lemma.fun_ar R2)) R0)) *)

(*                                                                                           R0)) -> (R4 ((Func R2) R1))). *)
(* (fix f : ∀ (inst : foterm), (R3 R0) := *)
(* λ (inst : foterm). *)
(* match (P:0) R0 return λ (inst : foterm). (R5 R0) with *)
(*  | (1) λ (_ : nat). (R4 R0) *)
(*  | (2) λ (f : destruct_lemma.Funcs). λ (_ : ((t foterm) (destruct_lemma.fun_ar R0))). (((R4 R1) R0) (((((((destruct_lemma.vecProof foterm) λ (_ : foterm). (R7 R0)) λ (_ : foterm). (R4 R0)) (destruct_lemma.fun_ar R1)) λ (_ : (destruct_lemma.fun_ar R1)). ((destruct_lemma.trivialPred (destruct_lemma.fun_ar R2)) R0)) λ (_ : (destruct_lemma.fun_ar R1)). ((destruct_lemma.trivialProof (destruct_lemma.fun_ar R2)) R0)) R0)) *)
(*  end) *)


(*   want *)
(*   λ (p : ∀ (inst : foterm), Ldestruct_lemma.452). *)
(* λ (H_var_foterm : (nat) -> (R1 (var_foterm R0))). *)
(* λ (H_Func : ∀ (f : destruct_lemma.Funcs), (((t foterm) (destruct_lemma.fun_ar R0))) -> (((((is_vec foterm) λ (_ : foterm). (R4 R0)) (destruct_lemma.fun_ar R1)) R0)) -> (R4 ((Func R2) R1))). *)
(* (fix f : ∀ (inst : foterm), (R3 R0) :=  *)
(* λ (inst : foterm).  *)
(* match (P:0) R0 return λ (inst : foterm). (R5 R0) with *)
(*  | (1) λ (_ : nat). (R4 R0) *)
(*  | (2) λ (f : destruct_lemma.Funcs). λ (_ : ((t foterm) (destruct_lemma.fun_ar R0))). (((R4 R1) R0) (((((destruct_lemma.vecProof foterm) λ (_ : foterm). (R7 R0)) λ (_ : foterm). (R4 R0)) (destruct_lemma.fun_ar R1)) R0)) *)
(* end)  *)

