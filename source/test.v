
(** A long script to test (non-nested) induction and case analysis **)

Require Import MetaCoq.Template.All.
Require Import destruct_lemma.
Require Import MetaCoq.Template.Pretty.
Require Import List String.
Import ListNotations MonadNotation.







(* Load destruct_lemma. *)
(* Require Import MetaCoq.Template.Pretty. *)


(* mutual inductive test *)

(* Inductive even : nat -> Prop := *)
(*   | even_O : even 0 *)
(*   | even_S : forall n, odd n -> even (S n) *)
(* with odd : nat -> Prop := *)
(*   odd_S : forall n, even n -> odd (S n). *)

(* Print even_ind. *)
(* Print odd_ind. *)

(* Goal forall n, even n -> exists k, n=2*k. *)
(* Proof. *)
(*   induction 1. *)
(*   - now exists 0. *)
(*   - destruct H. *)
(* Restart. *)
(*   induction n. *)
(*   - intros _. now exists 0. *)
(*   - destruct 1. *)
(*     + now exists 0. *)
(*     + destruct H. *)
(* Abort. *)

(* Print even_ind. *)
(* MetaCoq Run (create even true true). *)

Unset Strict Unquote Universe Mode.
MetaCoq Run (create nat true false).
MetaCoq Run (create nat true true).

Require Import de_bruijn_print.
(* MetaCoq TemplateCoq Pretty.v *)


Check fresh_name.
Print global_env_ext.
Print universes_decl.
Print ContextSet.t.
Search global_env_ext.
Print global_env.
Print tmPrint.
Print program.

MetaCoq Run (tmPrint <% nat %>).
(* MetaCoq Run (tmEval lazy (inductive_mind <% nat %>) >>= tmPrint). *)
MetaCoq Run (tmQuoteInductive "nat" >>= tmPrint).
MetaCoq Run (tmQuoteRec "nat" >>= tmPrint).
MetaCoq Run (p <- tmQuoteRec nat;;
               t <- tmEval lazy (p.2);;
               tmPrint t).

MetaCoq Run (tmPrint "A";;match true with true => tmPrint "B" | _ => tmPrint "C" end).

MetaCoq Run (p <- tmQuoteRec le;;
               t <- tmEval lazy (p.2);;
               tmPrint t).
(* MetaCoq Run (tmQuoteInductive <% nat %> >>= tmPrint). *)

MetaCoq Run (p <- tmQuoteRec nat;;
             n <- tmEval lazy (empty_ext( p.1));;
             tmPrint n).

(* Definition env := *)
(* ([InductiveDecl (* "Coq.Init.Datatypes.nat" *) *)
(*     {| *)
(*     ind_finite := Finite; *)
(*     ind_npars := 0; *)
(*     ind_params := []; *)
(*     ind_bodies := [{| *)
(*                    ind_name := "nat"; *)
(*                    ind_type := tSort (NEL.sing (Level.lSet, false)); *)
(*                    ind_kelim := [InProp; InSet; InType]; *)
(*                    ind_ctors := [("O", tRel 0, 0); ("S", tProd nAnon (tRel 0) (tRel 1), 1)]; *)
(*                    ind_projs := [] |}]; *)
(*     ind_universes := Monomorphic_ctx *)
(*                        ({| LevelSet.this := []; LevelSet.is_ok := LevelSet.Raw.empty_ok |}, *)
(*                        {| ConstraintSet.this := []; ConstraintSet.is_ok := ConstraintSet.Raw.empty_ok |}) |}], *)
(* Monomorphic_ctx *)
(*   ({| LevelSet.this := []; LevelSet.is_ok := LevelSet.Raw.empty_ok |}, *)
(*   {| ConstraintSet.this := []; ConstraintSet.is_ok := ConstraintSet.Raw.empty_ok |})) *)
(* . *)

(* Compute (fresh_name _ _ nAnon <% nat %>). *)
(* MetaCoq Quote Definition q := (fun n => S n). *)
(* MetaCoq Unquote Definition m := (tLambda nAnon <% nat %> <% nat %>). *)
(* MetaCoq Unquote Definition m2 := (tLambda nAnon <% nat %> (tApp <% S %> [tRel 0] )). *)
(* MetaCoq Unquote Definition m3 := (tLambda (nNamed "n") <% nat %> (tApp <% S %> [tRel 0] )). *)
(* (* Check Σ. *) *)
(* MetaCoq Unquote Definition m4 := (tLambda (fresh_name env [] nAnon <% nat %>) <% nat %> (tApp <% S %> [tRel 0] )). *)
(* MetaCoq Unquote Definition m5 := (tLambda (fresh_name env [] (nNamed "n") <% nat %>) <% nat %> (tApp <% S %> [tRel 0] )). *)
(* MetaCoq Unquote Definition m6 := (tLambda (fresh_name env [] nAnon <% bool %>) <% nat %> (tApp <% S %> [tRel 0] )). *)
(* MetaCoq Unquote Definition m7 := (tLambda (fresh_name env [] (nNamed "IH") <% nat %>) <% nat %> (tLambda (fresh_name env [] (nNamed "IH") <% nat %>) <% nat %> (tApp <% add %> [tRel 0;tRel 1] ))). *)
(* Definition m8 := (tLambda (fresh_name env [] (nNamed "IH") <% nat %>) <% nat %> (tLambda (fresh_name env [] (nNamed "IH") <% nat %>) <% nat %> (tApp <% add %> [tRel 0;tRel 1] ))). *)
(* Print m. *)
(* Print m2. *)
(* Print m3. *)
(* Print m4. *)
(* Print m5. *)
(* Print m6. *)
(* Print m7. *)
(* Print m8. *)
(* MetaCoq Run (tmEval lazy m8 >>= tmPrint). *)

Print term.


(* MetaCoq Quote Definition added := (fun (x:nat) => x+0). *)
(* Print added. *)

(* tLambda (nNamed "x") *)
(* (tInd {| *)
(*         inductive_mind := "nat"; *)
(*         inductive_ind := 0 *)
(*         |} *)
(*     []) *)
(* (tApp (tConst "add" []) *)
(*      [tRel 0; *)
(*      tConstruct {| *)
(*         inductive_mind := "nat"; *)
(*         inductive_ind := 0 *)
(*         |} *)
(*         0 *)
(*         [] *)
(*     ]) *)
(* tLambda (nNamed "x") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) *)
(*   (tApp (tConst "Coq.Init.Nat.add" []) *)
(*      [tRel 0; tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 []]) *)

(** non Uniform test **)

Inductive G3 (f:nat->bool) (n:nat) : Prop :=
  G3I : (f n = false -> G3 f (S n)) -> G3 f n.

Scheme Induction for G3 Sort Type.
Print G3_rect_dep.



MetaCoq Quote Definition I_G3 :=
  (
fun (f : nat -> bool) (P : forall n : nat, G3 f n -> Type)
  (f0 : forall (n : nat) (g : f n = false -> G3 f (S n)),
        (forall e : f n = false, P (S n) (g e)) -> P n (G3I f n g)) =>
fix F (n : nat) (g : G3 f n) {struct g} : P n g :=
  match g as g0 return (P n g0) with
  | @G3I _ _ g0 => f0 n g0 (fun e : f n = false => F (S n) (g0 e))
  end
  ).
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
MetaCoq Run (bruijn_print (trans I_G3)).

(*
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ((G3 (R1) (R0))) -> LTop.2132).
λ (f0 : ∀ (n : nat), ∀ (g : ((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))), (∀ (e : (eq (bool) ((R3 (R1))) (false))), (R3 ((S (R2))) ((R1 (R0))))) -> (R3 (R2) ((G3I (R4) (R2) (R1))))).
(fix F : ∀ (n : nat), ∀ (g : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (g : (G3 (R4) (R0))).
match (P:2) R0 return λ (g0 : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | (1) λ (g0 : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (e : (eq (bool) ((R6 (R2))) (false))). (R4 ((S (R3))) ((R1 (R0))))))
end)
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ((G3 (R1) (R0))) -> LTop.2446).
λ (f0 : ∀ (n : nat), ∀ (g : ((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))), (∀ (e : (eq (bool) ((R3 (R1))) (false))), (R3 ((S (R2))) ((R1 (R0))))) -> (R3 (R2) ((G3I (R4) (R2) (R1))))).
(fix F : ∀ (n : nat), ∀ (g : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (g : (G3 (R4) (R0))).
match (P:2) R0 return λ (g0 : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | (1) λ (g0 : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (e : (eq (bool) ((R6 (R2))) (false))). (R4 ((S (R3))) ((R1 (R0))))))
end)
*)

Print G3.
MetaCoq Run (create G3 true false).
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (inst : (G3 (R1) (R0))), LTop.1887).
λ (H_G3I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))) -> ∀ (IH : ((eq (bool) ((R3 (R1))) (false))) -> (R3 ((S (R2))) ((R1 (R0))))), (R3 (R2) ((G3I (R4) (R2) (R1))))).
(fix f : ∀ (n : nat), ∀ (inst : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (inst : (G3 (R4) (R0))).
match (P:2) R0 return λ (inst : (G3 (R5) (R1))). (R6 (R2) (R0)) with
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (_ : (eq (bool) ((R6 (R2))) (false))). (R4 ((S (R3))) ((R1 (R0))))))
end)
*)
(*
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (_ : (eq (bool) ((R6 (R2))) (false))). (R4 ((S (R3))) ((R1 (R0))))))
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (_ : (eq (bool) ((R7 (R2))) (false))). (R4 ((S (R3))) ((R1 (R0))))))
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (_ : (eq (bool) ((R2 (R0))) (false))). (R4 ((S (R1))) ((R1 (R0))))))
*)
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (inst : (G3 (R1) (R0))), LTop.230).
λ (H_G3I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))) -> ∀ (IH : ((eq (bool) ((R3 (R1))) (false))) -> (R3 ((S (R2))) ((R1 (R0))))), (R3 (R2) ((G3I (R4) (R2) (R1))))).
(fix f : ∀ (n : nat), ∀ (inst : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (inst : (G3 (R4) (R0))).
match (P:2) R0 return λ (inst : (G3 (R5) (R1))). (R5 (R2) (R0)) with
                                                                                                              !   !
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0) (λ (_ : (eq (bool) ((R5 (R0))) (false))). (R3 ((S (R1))) ((R1 (R0))))))
                 !       !
end)
 *)

(* have *)
(*   λ (f : (nat) -> bool). *)
(* λ (p : ∀ (n : nat), ∀ (inst : ((G3 R1) R0)), Ldestruct_lemma.447). *)
(* λ (H_G3I : ∀ (n : nat), (((((eq bool) (R2 R0)) false)) -> ((G3 R3) (S R1))) -> (((((eq bool) (R3 R1)) false)) -> ((R3 R4) (R1 R0))) -> ((R3 R4) (((G3I R4) R2) R1))). *)
(*                                                                                                             **                   ** *)
(* (fix f : ∀ (n : nat), ∀ (inst : ((G3 R3) R0)), ((R3 R1) R0) := *)
(* λ (n : nat). λ (inst : ((G3 R4) R0)). *)
(* match (P:2) R0 return λ (inst : ((G3 R5) R1)). ((R5 R2) R0) with *)
(*  | (1) λ (_ : ((((eq bool) (R5 R1)) false)) -> ((G3 R6) (S R2))). (((R4 R2) R0) λ (_ : (((eq bool) (R6 R2)) false)). ((R4 R7) (R1 R0))) *)
(* end) *)

(*   have 2 *)
(*   λ (f : (nat) -> bool). *)
(* λ (p : ∀ (n : nat), ∀ (inst : ((G3 R1) R0)), Ldestruct_lemma.447). *)
(* λ (H_G3I : ∀ (n : nat), (((((eq bool) (R2 R0)) false)) -> ((G3 R3) (S R1))) -> (((((eq bool) (R3 R1)) false)) -> ((R3 (S R2)) (R1 R0))) -> ((R3 R2) (((G3I R4) R2) R1))). *)
(* (fix f : ∀ (n : nat), ∀ (inst : ((G3 R3) R0)), ((R3 R1) R0) := *)
(* λ (n : nat). λ (inst : ((G3 R4) R0)). *)
(* match (P:2) R0 return λ (inst : ((G3 R5) R1)). ((R5 R2) R0) with *)
(*  | (1) λ (_ : ((((eq bool) (R5 R1)) false)) -> ((G3 R6) (S R2))). (((R4 R2) R0) λ (_ : (((eq bool) (R6 R2)) false)). ((R4 (S R3)) (R1 R0))) *)
(* end) *)

(* want *)
(* λ (f : (nat) -> bool). *)
(* λ (P : ∀ (n : nat), (((G3 R1) R0)) -> LTop.409). *)
(* λ (f0 : ∀ (n : nat), ∀ (g : ((((eq bool) (R2 R0)) false)) -> ((G3 R3) (S R1))), (∀ (e : (((eq bool) (R3 R1)) false)), ((R3 (S R2)) (R1 R0))) -> ((R3 R2) (((G3I R4) R2) R1))). *)
(* (fix F : ∀ (n : nat), ∀ (g : ((G3 R3) R0)), ((R3 R1) R0) := *)
(* λ (n : nat). λ (g : ((G3 R4) R0)). *)
(* match (P:2) R0 return λ (g0 : ((G3 R5) R1)). ((R5 R2) R0) with *)
(*  | (1) λ (g0 : ((((eq bool) (R5 R1)) false)) -> ((G3 R6) (S R2))). (((R4 R2) R0) λ (e : (((eq bool) (R6 R2)) false)). ((R4 (S R3)) (R1 R0))) *)
(* end) *)


MetaCoq Run (create G3 true true).


MetaCoq Quote Definition E_G3 := (fun (f : nat -> bool) (p : forall n : nat, G3 f n -> Type)
  (HG3I : forall (n : nat) (h : f n = false -> G3 f (S n)),
        p n (G3I f n h)) =>
fix F (n : nat) (g : G3 f n) {struct g} : p n g :=
  match g as g0 return (p n g0) with
  | @G3I _ _ h => HG3I n h
  end).

(* MetaCoq Run (bruijn_print E_G3). *)
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ((G3 (R1) (R0))) -> LTop.481).
λ (HG3I : ∀ (n : nat), ∀ (h : ((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))), (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix F : ∀ (n : nat), ∀ (g : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (g : (G3 (R4) (R0))).
match (P:2) R0 return λ (g0 : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | (1) λ (h : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0))
end)
 *)

MetaCoq Run (create G3 false false).
MetaCoq Run (create G3 false true).
Print G3_case_MC.
Print G3_case_MC.
(*
 | (1) λ (_ : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R6 (R1))) (false))) -> (G3 (R7) ((S (R2))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R4 (R0))) (false))) -> (G3 (R5) ((S (R1))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R1 (R0))) (false))) -> (G3 (R2) ((S (R1))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R5 (R4))) (false))) -> (G3 (R6) ((S (R5))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R5 (R4))) (false))) -> (G3 (R6) ((S (R5))))). (R4 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R5 (R4))) (false))) -> (G3 (R6) ((S (R5))))). (R3 (R2) (R0))
 | (1) λ (_ : ((eq (bool) ((R5 (R4))) (false))) -> (G3 (R6) ((S (R5))))). (R3 (R1) (R0))
 *)
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (inst : (G3 (R1) (R0))), LTop.230).
λ (H_G3I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))) -> (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix f : ∀ (n : nat), ∀ (inst : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (inst : (G3 (R4) (R0))).
match (P:2) R0 return λ (inst : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | (1) λ (_ : ((eq (bool) ((R5 (R4))) (false))) -> (G3 (R6) ((S (R5))))). (R3 (R0))
                                 !                                !         !!
end)
*)
(*
λ (f : (nat) -> bool). λ (p : ∀ (n : nat), ∀ (inst : (G3 (R1) (R0))), LTop.905). λ (H_G3I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))) -> (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix f : ∀ (n : nat), ∀ (inst : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (inst : (G3 (R4) (R0))).
match (P:2) R0 return λ (inst : (G3 (R5) (R0))). (R1 (R1) (R0)) with
 | R42
end)
*)
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (inst : (G3 (R1) (R0))), LTop.230).
λ (H_G3I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))) -> (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix f : ∀ (n : nat), ∀ (inst : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (inst : (G3 (R4) (R0))).
R42
)
*)


Inductive G4 (f:nat->bool) (n:nat) : nat -> Prop :=
  G4I : (f n = false -> G4 f (S n) 1) -> G4 f n 0.
MetaCoq Quote Definition E_G4 := (fun (f : nat -> bool) (p : forall (n m : nat), G4 f n m -> Type)
  (HG4I : forall (n : nat) (h : f n = false -> G4 f (S n) 1),
        p n 0 (G4I f n h)) =>
fix F (n : nat) (m:nat) (g : G4 f n m) {struct g} : p n m g :=
  match g in G4 _ _ m0 return (p n m0 g) with
  | @G4I _ _ h => HG4I n h
  end).
(* MetaCoq Run (bruijn_print E_G4). *)
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (m : nat), ((G4 (R2) (R1) (R0))) -> LTop.2226).
λ (HG4I : ∀ (n : nat), ∀ (h : ((eq (bool) ((R2 (R0))) (false))) -> (G4 (R3) ((S (R1))) ((S (O))))), (R2 (R1) (O) ((G4I (R3) (R1) (R0))))).
(fix F : ∀ (n : nat), ∀ (m : nat), ∀ (g : (G4 (R4) (R1) (R0))), (R4 (R2) (R1) (R0)) :=
λ (n : nat). λ (m : nat). λ (g : (G4 (R5) (R1) (R0))).
match (P:2) R0 return λ (m0 : nat). λ (g : (G4 (R7) (R3) (R0))). (R7 (R4) (R1) (R0)) with
 | (1) λ (h : ((eq (bool) ((R6 (R2))) (false))) -> (G4 (R7) ((S (R3))) ((S (O))))). (R5 (R3) (R0))
end)
*)
MetaCoq Run (create G4 false false).
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), (nat) -> ∀ (inst : (G4 (R2) (R1) (R0))), LTop.230).
λ (H_G4I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G4 (R3) ((S (R1))) ((S (O))))) -> (R2 (R1) (O) ((G4I (R3) (R1) (R0))))).
(fix f : ∀ (n : nat), (nat) -> ∀ (inst : (G4 (R4) (R1) (R0))), (R4 (R2) (R1) (R0)) :=
λ (n : nat). λ (_ : nat). λ (inst : (G4 (R5) (R1) (R0))).
match (P:2) R0 return λ (_ : nat). λ (inst : (G4 (R7) (R3) (R0))). (R6 (R4) (R1) (R0)) with
                                                                     !
 | (1) λ (_ : ((eq (bool) ((R6 (R2))) (false))) -> (G4 (R7) ((S (R3))) ((S (O))))). (R5 (R3) (R0))
end)
 *)
MetaCoq Run (create G4 false true).

Scheme Induction for G4 Sort Type.
Print G4_rect_dep.
MetaCoq Quote Definition I_G4 := (
fun (f : nat -> bool) (P : forall n n0 : nat, G4 f n n0 -> Type)
  (f0 : forall (n : nat) (g : f n = false -> G4 f (S n) 1),
        (forall e : f n = false, P (S n) 1 (g e)) -> P n 0 (G4I f n g)) =>
fix F (n n0 : nat) (g : G4 f n n0) {struct g} : P n n0 g :=
  match g as g0 in (G4 _ _ n1) return (P n n1 g0) with
  | @G4I _ _ g0 => f0 n g0 (fun e : f n = false => F (S n) 1 (g0 e))
  end
                        ).
(* MetaCoq Run (bruijn_print I_G4). *)
(*
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ∀ (n0 : nat), ((G4 (R2) (R1) (R0))) -> LTop.1150).
λ (f0 : ∀ (n : nat), ∀ (g : ((eq (bool) ((R2 (R0))) (false))) -> (G4 (R3) ((S (R1))) ((S (O))))), (∀ (e : (eq (bool) ((R3 (R1))) (false))), (R3 ((S (R2))) ((S (O))) ((R1 (R0))))) -> (R3 (R2) (O) ((G4I (R4) (R2) (R1))))).
(fix F : ∀ (n : nat), ∀ (n0 : nat), ∀ (g : (G4 (R4) (R1) (R0))), (R4 (R2) (R1) (R0)) :=
λ (n : nat). λ (n0 : nat). λ (g : (G4 (R5) (R1) (R0))).
match (P:2) R0 return λ (n1 : nat). λ (g0 : (G4 (R7) (R3) (R0))). (R7 (R4) (R1) (R0)) with
 | (1) λ (g0 : ((eq (bool) ((R6 (R2))) (false))) -> (G4 (R7) ((S (R3))) ((S (O))))). (R5 (R3) (R0) (λ (e : (eq (bool) ((R7 (R3))) (false))). (R5 ((S (R4))) ((S (O))) ((R1 (R0))))))
end)
*)

MetaCoq Run (create G4 true false).
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), (nat) -> ∀ (inst : (G4 (R2) (R1) (R0))), LTop.709).
λ (H_G4I : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G4 (R3) ((S (R1))) ((S (O))))) -> ∀ (IH : ((eq (bool) ((R3 (R1))) (false))) -> (R3 ((S (R2))) ((S (O))) ((R1 (R0))))), (R3 (R2) (O) ((G4I (R4) (R2) (R1))))).
(fix f : ∀ (n : nat), (nat) -> ∀ (inst : (G4 (R4) (R1) (R0))), (R4 (R2) (R1) (R0)) :=
λ (n : nat). λ (_ : nat). λ (inst : (G4 (R5) (R1) (R0))).
match (P:2) R0 return λ (_ : nat). λ (inst : (G4 (R7) (R3) (R0))). (R7 (R4) (R1) (R0)) with
 | (1) λ (_ : ((eq (bool) ((R6 (R2))) (false))) -> (G4 (R7) ((S (R3))) ((S (O))))). (R5 (R3) (R0) (λ (_ : (eq (bool) ((R8 (R3))) (false))). (R5 ((S (R4))) ((S (O))) ((R1 (R0))))))
        !                         !
end)
*)
MetaCoq Run (create G4 true true).



Inductive G5 (f:nat->bool) (n:nat) (n2:nat) : nat -> Prop :=
  G5I : (f n = false -> G5 f (S n) (2+n2) 1) -> G5 f n n2 0.
MetaCoq Run (create G5 false true).
Print G5_case_MC.
Scheme Induction for G5 Sort Type.
Print G5_rect_dep.
MetaCoq Quote Definition I_G5 := (
fun (f : nat -> bool) (P : forall n n2 n0 : nat, G5 f n n2 n0 -> Type)
  (f0 : forall (n n2 : nat) (g : f n = false -> G5 f (S n) (2 + n2) 1),
        (forall e : f n = false, P (S n) (2 + n2) 1 (g e)) -> P n n2 0 (G5I f n n2 g)) =>
fix F (n n2 n0 : nat) (g : G5 f n n2 n0) {struct g} : P n n2 n0 g :=
  match g as g0 in (G5 _ _ _ n1) return (P n n2 n1 g0) with
  | @G5I _ _ _ g0 => f0 n n2 g0 (fun e : f n = false => F (S n) (2 + n2) 1 (g0 e))
  end
                        ).
(* MetaCoq Run (bruijn_print I_G5). *)
(*
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ∀ (n2 : nat), ∀ (n0 : nat), ((G5 (R3) (R2) (R1) (R0))) -> LTop.6844).
λ (f0 : ∀ (n : nat), ∀ (n2 : nat), ∀ (g : ((eq (bool) ((R3 (R1))) (false))) -> (G5 (R4) ((S (R2))) ((Coq.Init.Nat.add ((S ((S (O))))) (R1))) ((S (O))))), (∀ (e : (eq (bool) ((R4 (R2))) (false))), (R4 ((S (R3))) ((Coq.Init.Nat.add ((S ((S (O))))) (R2))) ((S (O))) ((R1 (R0))))) -> (R4 (R3) (R2) (O) ((G5I (R5) (R3) (R2) (R1))))).
(fix F : ∀ (n : nat), ∀ (n2 : nat), ∀ (n0 : nat), ∀ (g : (G5 (R5) (R2) (R1) (R0))), (R5 (R3) (R2) (R1) (R0)) :=
λ (n : nat). λ (n2 : nat). λ (n0 : nat). λ (g : (G5 (R6) (R2) (R1) (R0))).
match (P:3) R0 return λ (n1 : nat). λ (g0 : (G5 (R8) (R4) (R3) (R0))). (R8 (R5) (R4) (R1) (R0)) with
 | (1) λ (g0 : ((eq (bool) ((R7 (R3))) (false))) -> (G5 (R8) ((S (R4))) ((Coq.Init.Nat.add ((S ((S (O))))) (R3))) ((S (O))))). (R6 (R4) (R3) (R0) (λ (e : (eq (bool) ((R8 (R4))) (false))). (R6 ((S (R5))) ((Coq.Init.Nat.add ((S ((S (O))))) (R4))) ((S (O))) ((R1 (R0))))))
end)
*)
MetaCoq Run (create G5 true false).
(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ∀ (n2 : nat), (nat) -> ∀ (inst : (G5 (R3) (R2) (R1) (R0))), LTop.6376).
λ (H_G5I : ∀ (n : nat), ∀ (n2 : nat), (((eq (bool) ((R3 (R1))) (false))) -> (G5 (R4) ((S (R2))) ((Coq.Init.Nat.add ((S ((S (O))))) (R1))) ((S (O))))) -> ∀ (IH : ((eq (bool) ((R4 (R2))) (false))) -> (R4 ((S (R3))) ((Coq.Init.Nat.add ((S ((S (O))))) (R2))) ((S (O))) ((R1 (R0))))), (R4 (R3) (R2) (O) ((G5I (R5) (R3) (R2) (R1))))).
(fix f : ∀ (n : nat), ∀ (n2 : nat), (nat) -> ∀ (inst : (G5 (R5) (R2) (R1) (R0))), (R5 (R3) (R2) (R1) (R0)) := 
λ (n : nat). λ (n2 : nat). λ (_ : nat). λ (inst : (G5 (R6) (R2) (R1) (R0))). 
match (P:3) R0 return λ (_ : nat). λ (inst : (G5 (R8) (R4) (R3) (R0))). (R8 (R5) (R4) (R1) (R0)) with
 | (1) λ (_ : ((eq (bool) ((R7 (R3))) (false))) -> (G5 (R8) ((S (R4))) ((Coq.Init.Nat.add ((S ((S (O))))) (R3))) ((S (O))))). (R6 (R4) (R3) (R0) (λ (_ : (eq (bool) ((R9 (R4))) (false))). (R6 ((S (R5))) ((Coq.Init.Nat.add ((S ((S (O))))) (R4))) ((S (O))) ((R1 (R0))))))
                                                   !
end)
*)
(* MetaCoq Run (create G5 true true). *)







Inductive indexIndTest : nat -> Type :=
  | Ct0 : indexIndTest 0 -> indexIndTest 1.
(* MetaCoq Run (create indexIndTest true). *)
(* Print indexIndTest_case_MC. *)
(* Print indexIndTest_ind. *)

MetaCoq Quote Definition EindexIndTest :=
  (fun (p:forall n, indexIndTest n -> Type)
    HCt0 =>
    (* (HCt0: forall (H:indexIndTest 0), p 0 H -> p 1 (Ct0 H)) => *)
    fix f (n:nat) (x:indexIndTest n) :=
    match x in indexIndTest m return p m x with
      Ct0 H => HCt0 H (f 0 H)
    end).

(* MetaCoq Run (bruijn_print EindexIndTest). *)
(*
λ (p : ∀ (n : nat), ((indexIndTest (R0))) -> LTop.415).
λ (HCt0 : ∀ (x : (indexIndTest (O))), ∀ (x0 : (R1 (O) (R0))), (R2 ((S (O))) ((Ct0 (R1))))).
(fix f : ∀ (n : nat), ∀ (x : (indexIndTest (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (x : (indexIndTest (R0))).
match R0 return λ (m : nat). λ (x : (indexIndTest (R0))). (R6 (R1) (R0)) with
 | λ (H : (indexIndTest (O))). (R4 (R0) ((R3 (O) (R0))))
end)
 *)
MetaCoq Run (create indexIndTest true true).
Print indexIndTest_ind_MC.
Print indexIndTest_ind_MC.

(*
λ (p : (nat) -> ∀ (inst : (indexIndTest (R0))), LTop.2303).
λ (H_Ct0 : ((indexIndTest (O))) -> ∀ (IH : (R1 (O) (R0))), (R2 ((S (O))) ((Ct0 (R1))))).
(fix f : (nat) -> ∀ (inst : (indexIndTest (R0))), (R3 (R1) (R0)) :=
λ (_ : nat). λ (inst : (indexIndTest (R0))).
match R0 return λ (_ : nat). λ (inst : (indexIndTest (R0))). (R6 (R1) (R0)) with
 | λ (_ : (indexIndTest (O))). (R4 (R0) ((R3 (O) (R0))))
end) *)

(** Tests **)
(** Complex with Universes **)

MetaCoq Run (create term false true).
Print term_case_MC.
Print TemplateMonad.
MetaCoq Run(tmPrint <% nat %>).
MetaCoq Run(tmQuote nat >>= tmPrint).
MetaCoq Run(tmQuoteRec nat >>= tmPrint).
MetaCoq Run(tmQuoteInductive "nat" >>= tmPrint).
MetaCoq Run(tmQuoteRec TemplateMonad >>= tmPrint).
MetaCoq Run(tmQuoteInductive "TemplateMonad" >>= tmPrint).
(* MetaCoq Run (create TemplateMonad true). *)


Print term_ind.
(* MetaCoq Quote Definition E_term := *)
(* (fun (P : term -> Prop) (f : forall n : nat, P (tRel n)) (f0 : forall id : ident, P (tVar id)) *)
(*   (f1 : forall (ev : nat) (args : list term), P (tEvar ev args)) (f2 : forall s : universe, P (tSort s)) *)
(*   (f3 : forall t : term, P t -> forall (kind : cast_kind) (v : term), P v -> P (tCast t kind v)) *)
(*   (f4 : forall (na : name) (ty : term), P ty -> forall body : term, P body -> P (tProd na ty body)) *)
(*   (f5 : forall (na : name) (ty : term), P ty -> forall body : term, P body -> P (tLambda na ty body)) *)
(*   (f6 : forall (na : name) (def : term), *)
(*         P def -> forall def_ty : term, P def_ty -> forall body : term, P body -> P (tLetIn na def def_ty body)) *)
(*   (f7 : forall f7 : term, P f7 -> forall args : list term, P (tApp f7 args)) *)
(*   (f8 : forall (c : kername) (u : universe_instance), P (tConst c u)) *)
(*   (f9 : forall (ind : inductive) (u : universe_instance), P (tInd ind u)) *)
(*   (f10 : forall (ind : inductive) (idx : nat) (u : universe_instance), P (tConstruct ind idx u)) *)
(*   (f11 : forall (ind_and_nbparams : inductive × nat) (type_info : term), *)
(*          P type_info -> *)
(*          forall discr : term, *)
(*          P discr -> forall branches : list (nat × term), P (tCase ind_and_nbparams type_info discr branches)) *)
(*   (f12 : forall (proj : projection) (t : term), P t -> P (tProj proj t)) *)
(*   (f13 : forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx)) *)
(*   (f14 : forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx)) => *)
(* fix F (t : term) : P t := *)
(*   match t as t0 return (P t0) with *)
(*   | tRel n => f n *)
(*   | tVar id => f0 id *)
(*   | tEvar ev args => f1 ev args *)
(*   | tSort s => f2 s *)
(*   | tCast t0 kind v => f3 t0 (F t0) kind v (F v) *)
(*   | tProd na ty body => f4 na ty (F ty) body (F body) *)
(*   | tLambda na ty body => f5 na ty (F ty) body (F body) *)
(*   | tLetIn na def def_ty body => f6 na def (F def) def_ty (F def_ty) body (F body) *)
(*   | tApp f15 args => f7 f15 (F f15) args *)
(*   | tConst c u => f8 c u *)
(*   | tInd ind u => f9 ind u *)
(*   | tConstruct ind idx u => f10 ind idx u *)
(*   | tCase ind_and_nbparams type_info discr branches => *)
(*       f11 ind_and_nbparams type_info (F type_info) discr (F discr) branches *)
(*   | tProj proj t0 => f12 proj t0 (F t0) *)
(*   | tFix mfix idx => f13 mfix idx *)
(*   | tCoFix mfix idx => f14 mfix idx *)
(*   end *)
(* ). *)
(* MetaCoq Run (bruijn_print E_term). *)
(*
λ (P : (term) -> Prop).
λ (f : ∀ (n : nat), (R1 ((tRel (R0))))).
λ (f0 : ∀ (id : MetaCoq.Template.BasicAst.ident), (R2 ((tVar (R0))))).
λ (f1 : ∀ (ev : nat), ∀ (args : (list (term))), (R4 ((tEvar (R1) (R0))))).
λ (f2 : ∀ (s : MetaCoq.Template.Universes.universe), (R4 ((tSort (R0))))).
λ (f3 : ∀ (t : term), ((R5 (R0))) -> ∀ (kind : cast_kind), ∀ (v : term), ((R8 (R0))) -> (R9 ((tCast (R4) (R2) (R1))))).
λ (f4 : ∀ (na : name), ∀ (ty : term), ((R7 (R0))) -> ∀ (body : term), ((R9 (R0))) -> (R10 ((tProd (R4) (R3) (R1))))).
λ (f5 : ∀ (na : name), ∀ (ty : term), ((R8 (R0))) -> ∀ (body : term), ((R10 (R0))) -> (R11 ((tLambda (R4) (R3) (R1))))).
λ (f6 : ∀ (na : name), ∀ (def : term), ((R9 (R0))) -> ∀ (def_ty : term), ((R11 (R0))) -> ∀ (body : term), ((R13 (R0))) -> (R14 ((tLetIn (R6) (R5) (R3) (R1))))).
λ (f7 : ∀ (f7 : term), ((R9 (R0))) -> ∀ (args : (list (term))), (R11 ((tApp (R2) (R0))))).
λ (f8 : ∀ (c : MetaCoq.Template.BasicAst.kername), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R11 ((tConst (R1) (R0))))).
λ (f9 : ∀ (ind : inductive), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R12 ((tInd (R1) (R0))))).
λ (f10 : ∀ (ind : inductive), ∀ (idx : nat), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R14 ((tConstruct (R2) (R1) (R0))))).
λ (f11 : ∀ (ind_and_nbparams : (prod (inductive) (nat))), ∀ (type_info : term), ((R14 (R0))) -> ∀ (discr : term), ((R16 (R0))) -> ∀ (branches : (list ((prod (nat) (term))))), (R18 ((tCase (R5) (R4) (R2) (R0))))).
λ (f12 : ∀ (proj : MetaCoq.Template.BasicAst.projection), ∀ (t : term), ((R15 (R0))) -> (R16 ((tProj (R2) (R1))))).
λ (f13 : ∀ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))), ∀ (idx : nat), (R16 ((tFix (R1) (R0))))). λ (f14 : ∀ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))), ∀ (idx : nat), (R17 ((tCoFix (R1) (R0))))).
(fix F : ∀ (t : term), (R17 (R0)) :=
λ (t : term).
match R0 return λ (t0 : term). (R19 (R0)) with
 | λ (n : nat). (R18 (R0))
 | λ (id : MetaCoq.Template.BasicAst.ident). (R17 (R0))
 | λ (ev : nat). λ (args : (list (term))). (R17 (R1) (R0))
 | λ (s : MetaCoq.Template.Universes.universe). (R15 (R0))
 | λ (t0 : term). λ (kind : cast_kind). λ (v : term). (R16 (R2) ((R4 (R2))) (R1) (R0) ((R4 (R0))))
 | λ (na : name). λ (ty : term). λ (body : term). (R15 (R2) (R1) ((R4 (R1))) (R0) ((R4 (R0))))
 | λ (na : name). λ (ty : term). λ (body : term). (R14 (R2) (R1) ((R4 (R1))) (R0) ((R4 (R0))))
 | λ (na : name). λ (def : term). λ (def_ty : term). λ (body : term). (R14 (R3) (R2) ((R5 (R2))) (R1) ((R5 (R1))) (R0) ((R5 (R0))))
 | λ (f15 : term). λ (args : (list (term))). (R11 (R1) ((R3 (R1))) (R0))
 | λ (c : MetaCoq.Template.BasicAst.kername). λ (u : MetaCoq.Template.Universes.universe_instance). (R10 (R1) (R0))
 | λ (ind : inductive). λ (u : MetaCoq.Template.Universes.universe_instance). (R9 (R1) (R0))
 | λ (ind : inductive). λ (idx : nat). λ (u : MetaCoq.Template.Universes.universe_instance). (R9 (R2) (R1) (R0))
 | λ (ind_and_nbparams : (prod (inductive) (nat))). λ (type_info : term). λ (discr : term). λ (branches : (list ((prod (nat) (term))))). (R9 (R3) (R2) ((R5 (R2))) (R1) ((R5 (R1))) (R0))
 | λ (proj : MetaCoq.Template.BasicAst.projection). λ (t0 : term). (R6 (R1) (R0) ((R3 (R0))))
 | λ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))). λ (idx : nat). (R5 (R1) (R0))
 | λ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))). λ (idx : nat). (R4 (R1) (R0))
end)
*)
MetaCoq Run (create term true false).
(*
λ (p : ∀ (inst : term), LTop.2491).
λ (H_tRel : ∀ (n : nat), (R1 ((tRel (R0))))).
λ (H_tVar : ∀ (id : MetaCoq.Template.BasicAst.ident), (R2 ((tVar (R0))))).
λ (H_tEvar : ∀ (ev : nat), ∀ (args : (list (term))), ∀ (IH_args : (R4 (R5) (R0))), (R5 ((tEvar (R2) (R1))))).
λ (H_tSort : ∀ (s : MetaCoq.Template.Universes.universe), (R4 ((tSort (R0))))).
λ (H_tCast : ∀ (t : term), ∀ (kind : cast_kind), ∀ (v : term), ∀ (IH_t : (R7 (R2))), ∀ (IH_v : (R8 (R1))), (R9 ((tCast (R4) (R3) (R2))))).
λ (H_tProd : ∀ (na : name), ∀ (ty : term), ∀ (body : term), ∀ (IH_ty : (R8 (R1))), ∀ (IH_body : (R9 (R1))), (R10 ((tProd (R4) (R3) (R2))))).
λ (H_tLambda : ∀ (na : name), ∀ (ty : term), ∀ (body : term), ∀ (IH_ty : (R9 (R1))), ∀ (IH_body : (R10 (R1))), (R11 ((tLambda (R4) (R3) (R2))))).
λ (H_tLetIn : ∀ (na : name), ∀ (def : term), ∀ (def_ty : term), ∀ (body : term), ∀ (IH_def : (R11 (R2))), ∀ (IH_def_ty : (R12 (R2))), ∀ (IH_body : (R13 (R2))), (R14 ((tLetIn (R6) (R5) (R4) (R3))))).
λ (H_tApp : ∀ (f : term), ∀ (args : (list (term))), ∀ (IH_f : (R10 (R1))), ∀ (IH_args : (R11 (R12) (R1))), (R12 ((tApp (R3) (R2))))).
λ (H_tConst : ∀ (c : MetaCoq.Template.BasicAst.kername), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R11 ((tConst (R1) (R0))))).
λ (H_tInd : ∀ (ind : inductive), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R12 ((tInd (R1) (R0))))).
λ (H_tConstruct : ∀ (ind : inductive), ∀ (idx : nat), ∀ (u : MetaCoq.Template.Universes.universe_instance), (R14 ((tConstruct (R2) (R1) (R0))))).
λ (H_tCase : ∀ (ind_and_nbparams : (prod (inductive) (nat))), ∀ (type_info : term), ∀ (discr : term), ∀ (branches : (list ((prod (nat) (term))))), ∀ (IH_type_info : (R16 (R2))), ∀ (IH_discr : (R17 (R2))), ∀ (IH_branches : (R18 ((prod (nat) (R19))) (R2))), (R19 ((tCase (R6) (R5) (R4) (R3))))). λ (H_tProj : ∀ (proj : MetaCoq.Template.BasicAst.projection), ∀ (t : term), ∀ (IH_t : (R15 (R0))), (R16 ((tProj (R2) (R1))))). λ (H_tFix : ∀ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))), ∀ (idx : nat), ∀ (IH_mfix : (R16 (R17) (R1))), (R17 ((tFix (R2) (R1))))). λ (H_tCoFix : ∀ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))), ∀ (idx : nat), ∀ (IH_mfix : (R17 (R18) (R1))), (R18 ((tCoFix (R2) (R1))))).
(fix f : ∀ (inst : term), (R17 (R0)) :=
λ (inst : term).
match R0 return λ (inst : term). (R19 (R0)) with
 | λ (n : nat). (R18 (R0))
 | λ (id : MetaCoq.Template.BasicAst.ident). (R17 (R0))
 | λ (ev : nat). λ (args : (list (term))). (R17 (R1) (R0) ((R3 (R21) (R0))))
 | λ (s : MetaCoq.Template.Universes.universe). (R15 (R0))
 | λ (t : term). λ (kind : cast_kind). λ (v : term). (R16 (R2) (R1) (R0) ((R4 (R2))) ((R4 (R0))))
 | λ (na : name). λ (ty : term). λ (body : term). (R15 (R2) (R1) (R0) ((R4 (R1))) ((R4 (R0))))
 | λ (na : name). λ (ty : term). λ (body : term). (R14 (R2) (R1) (R0) ((R4 (R1))) ((R4 (R0))))
 | λ (na : name). λ (def : term). λ (def_ty : term). λ (body : term). (R14 (R3) (R2) (R1) (R0) ((R5 (R2))) ((R5 (R1))) ((R5 (R0))))
 | λ (f : term). λ (args : (list (term))). (R11 (R1) (R0) ((R3 (R1))) ((R3 (R21) (R0))))
 | λ (c : MetaCoq.Template.BasicAst.kername). λ (u : MetaCoq.Template.Universes.universe_instance). (R10 (R1) (R0))
 | λ (ind : inductive). λ (u : MetaCoq.Template.Universes.universe_instance). (R9 (R1) (R0))
 | λ (ind : inductive). λ (idx : nat). λ (u : MetaCoq.Template.Universes.universe_instance). (R9 (R2) (R1) (R0))
 | λ (ind_and_nbparams : (prod (inductive) (nat))). λ (type_info : term). λ (discr : term). λ (branches : (list ((prod (nat) (term))))). (R9 (R3) (R2) (R1) (R0) ((R5 (R2))) ((R5 (R1))) ((R5 ((prod (nat) (R23))) (R0))))
 | λ (proj : MetaCoq.Template.BasicAst.projection). λ (t : term). (R6 (R1) (R0) ((R3 (R0))))
 | λ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))). λ (idx : nat). (R5 (R1) (R0) ((R3 (R21) (R1))))
 | λ (mfix : (MetaCoq.Template.BasicAst.mfixpoint (term))). λ (idx : nat). (R4 (R1) (R0) ((R3 (R21) (R1))))
end) 
 *)

(* MetaCoq Run (create term true true). *)
(* Print term_ind_MC. *)




(* Inductive rtree A : Type := *)
(* | Leaf (a:A) *)
(* | Node (l:list (rtree A)). *)

(* MetaCoq Run (create rtree false true). *)
(* Print rtree_case_MC. *)
(* MetaCoq Run (create rtree true true). *)
(* Print rtree_ind_MC. *)
(* Print rtree_ind. *)



(* Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type := *)
(*     nilᵗ : listᵗ A Aᵗ [] | consᵗ : forall H : A, Aᵗ H -> forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0). *)

(* Inductive rtreeᵗ (A : Type) (Aᵗ : A -> Type) : rtree A -> Type := *)
(*     Leafᵗ : forall a : A, Aᵗ a -> rtreeᵗ A Aᵗ (Leaf A a) *)
(*   | Nodeᵗ : forall l : list (rtree A), listᵗ (rtree A) (rtreeᵗ A Aᵗ) l -> rtreeᵗ A Aᵗ (Node A l). *)

(* MetaCoq Run (create rtreeᵗ true true). *)
(* Print rtreeᵗ_ind_MC. *)


(* here are nested *)




(** dependent indices **)

Lemma eqIsEq X (a:X) : a=a.
Proof.
  exact(Logic.eq_refl).
Qed.

Inductive dep (X:Type) : nat -> forall (x:X), x=x -> Prop :=
| dep0 y : dep X 0 y (@Coq.Init.Logic.eq_refl _ y).

MetaCoq Quote Definition Edep :=
  (
    fun (X:Type) (p:forall n x h, dep X n x h -> Prop) =>
      fun Hdep0 =>
        fix f m x h (i:dep X m x h) :=
      match i in dep _ m' x' h' return p m' x' h' i with
        dep0 y => Hdep0 y
      end
  ).
(* MetaCoq Run (bruijn_print Edep). *)
(*
λ (X : LTop.658).
λ (p : ∀ (n : nat), ∀ (x : R1), ∀ (h : (eq (R2) (R0) (R0))), ((dep (R3) (R2) (R1) (R0))) -> Prop).
  λ (Hdep0 : ∀ (x : R1), (R1 (O) (R0) ((eq_refl (R2) (R0))) ((dep0 (R2) (R0))))).
  (fix f : ∀ (m : nat), ∀ (x : R3), ∀ (h : (eq (R4) (R0) (R0))), ∀ (i : (dep (R5) (R2) (R1) (R0))), (R5 (R3) (R2) (R1) (R0)) :=
       λ (m : nat). λ (x : R4). λ (h : (eq (R5) (R0) (R0))). λ (i : (dep (R6) (R2) (R1) (R0))).
       match R0 return λ (m' : nat). λ (x' : R8). λ (h' : (eq (R9) (R0) (R0))). λ (i : (dep (R01) (R2) (R1) (R0))). (R01 (R3) (R2) (R1) (R0)) with
       | λ (y : R7). (R6 (R0))
       end
  )
 *)
MetaCoq Run (create dep false false).
MetaCoq Run (create dep false true).
Print dep_case_MC.
MetaCoq Run (create dep true true).
Print dep_ind_MC.

(** indices **)

Inductive indTest (X:Type) : nat -> Prop :=
  | indC0 : indTest X 0.

Print indTest.
MetaCoq Run (create indTest false false).
MetaCoq Run (create indTest false true).
Print indTest_case_MC.
MetaCoq Run (create indTest true true).
Print indTest_ind_MC.

Print le_n.
Check le_n.
Check le_S.
MetaCoq Run (create Peano.le false true).
MetaCoq Quote Definition leElimType := (
forall (n : nat) (p : forall H : nat, n <= H -> Prop),
             p n (le_n n) ->
             (forall (m : nat) (H : n <= m), p (S m) (le_S n m H)) -> forall (H : nat) (inst : n <= H), p H inst
                                      ).
Print leElimType.

Print le_case_MC.
MetaCoq Run (create Peano.le true true).
Print le_ind_MC.

Inductive eqT (X:Type) (x:X) : X -> Prop := Qcon : eqT X x x.

MetaCoq Run (create eqT false false).
MetaCoq Run (create eqT false true).
Print eqT_case_MC.
MetaCoq Run (create eqT true true).
Print eqT_ind_MC.

Inductive double : nat -> nat -> Prop :=
| d0 : double 0 0
| dS x y : double x y -> double (S x) (S(S y)).

MetaCoq Run (create double false true).
Print double_case_MC.
MetaCoq Run (create double true true).
Print double_ind_MC.

Inductive addition : nat -> nat -> nat -> Prop :=
| add0 x : addition 0 x x
| addS x y z : addition x y z -> addition (S x) y (S z).

MetaCoq Run (create addition false true).
Print addition_case_MC.
MetaCoq Run (create addition true true).
Print addition_ind_MC.


Print Peano.le.
Print Peano.le_ind.
MetaCoq Quote Definition Ele :=
  (fun n (p:forall m, n<=m -> Prop) Hn Hs =>
    fix f m (x:n<=m) :=
    match x in (_ <= m2) return p m2 x with
    | le_n => Hn
    | le_S k H => Hs k H
    end).
Print Ele.
(* MetaCoq Run (bruijn_print Ele). *)
(*
λ (n : nat). λ (p : ∀ (m : nat), ((le (R1) (R0))) -> Prop).
   λ (Hn : (R0 (R1) ((le_n (R1))))).
   λ (Hs : ∀ (x : nat), ∀ (x0 : (le (R3) (R0))), (R3 ((S (R1))) ((le_S (R4) (R1) (R0))))).
   (fix f : ∀ (m : nat), ∀ (x : (le (R4) (R0))), (R4 (R1) (R0)) :=
        λ (m : nat). λ (x : (le (R5) (R0))).
        match R0 return λ (m2 : nat). λ (x : (le (R7) (R0))). (R7 (R1) (R0)) with
        | R4
        | λ (k : nat). λ (H : (le (R7) (R0))). (R5 (R1) (R0))
        end
   )
 *)




(** Parameter **)

MetaCoq Quote Definition qElist := (fun X (p:list X -> Prop) Hnil Hcons =>
              fix f xs :=
              match xs return p xs with
                | nil => Hnil
                | y::ys => Hcons y ys
              end
                           ).
Print qElist.
(* MetaCoq Run (bruijn_print qElist). *)
(*
λ (X : LTop.793). λ (p : ((list (R0))) -> Prop).
  λ (Hnil : (R0 ((nil (R1))))).
  λ (Hcons : ∀ (x : R2), ∀ (x0 : (list (R3))), (R3 ((cons (R4) (R1) (R0))))).
  (fix f : ∀ (xs : (list (R3))), (R3 (R0)) := λ (xs : (list (R4))).
       match R0 return λ (xs : (list (R5))). (R5 (R0)) with
             | R3
             | λ (y : R5). λ (ys : (list (R6))). (R4 (R1) (R0))
       end
  )
 *)

MetaCoq Run (create list false false).
MetaCoq Run (create list false true).
Print list_case_MC.
Print list_ind.
MetaCoq Quote Definition E_list :=
(fun (A : Type) (P : list A -> Prop) (f : P []) (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l := match l as l0 return (P l0) with
                            | [] => f
                            | y :: l0 => f0 y l0 (F l0)
                            end
).
(* MetaCoq Run (bruijn_print E_list). *)
(*
λ (A : LTop.1687).
λ (P : ((list (R0))) -> Prop).
λ (f : (R0 ((nil (R1))))).
λ (f0 : ∀ (a : R2), ∀ (l : (list (R3))), ((R3 (R0))) -> (R4 ((cons (R5) (R2) (R1))))).
(fix F : ∀ (l : (list (R3))), (R3 (R0)) :=
λ (l : (list (R4))).
match R0 return λ (l0 : (list (R5))). (R5 (R0)) with
 | R3
 | λ (y : R5). λ (l0 : (list (R6))). (R4 (R1) (R0) ((R3 (R0))))
end)
 *)
MetaCoq Run (create list true false).
(*
λ (A : LCoq.Init.Datatypes.44).
λ (p : ∀ (inst : (list (R0))), LTop.1260).
λ (H_nil : (R0 ((nil (R1))))).
λ (H_cons : (R2) -> ((list (R3))) -> (R3 ((cons (R4) (R1) (R0))))).
(fix f : ∀ (inst : (list (R3))), (R3 (R0)) :=
λ (inst : (list (R4))).
match R0 return λ (inst : (list (R5))). (R5 (R0)) with
 | R3
 | λ (_ : R5). λ (_ : (list (R6))). (R4 (R1) (R0) ((R3 (R0))))
end)
*)
MetaCoq Run (create list true true).
Print list_ind_MC.

Inductive mutParam (X:Type) (f:X->bool) : Type :=
  | mP : mutParam X f.

MetaCoq Run (create mutParam false true).
Print mutParam.
Print mutParam_case_MC.
MetaCoq Run (create mutParam true true).
Print mutParam_ind_MC.

MetaCoq Run (create and false true).
Print and_case_MC.
MetaCoq Run (create and true true).
Print and_ind_MC.
MetaCoq Run (create or false false).
MetaCoq Run (create or false true).
Print or_case_MC.
MetaCoq Run (create or true true).
Print or_ind_MC.
MetaCoq Run (create ex false true).
Print ex_case_MC.
Print ex.
Scheme Induction for ex Sort Prop.
Print ex_ind_dep.
Print ex_case_MC.
MetaCoq Run (create ex false false).
(*
λ (A : LCoq.Init.Logic.4).
λ (P : (R0) -> Prop).
λ (p : ∀ (inst : (ex (R1) (R0))), Prop).
λ (H_ex_intro : ∀ (x : R2), ((R2 (R0))) -> (R2 ((ex_intro (R4) (R3) (R1) (R0))))).
(fix f : ∀ (inst : (ex (R3) (R2))), (R2 (R0)) :=
λ (inst : (ex (R4) (R3))).
match R0 return λ (inst : (ex (R5) (R4))). (R4 (R0)) with
 | λ (x : R5). λ (_ : (R5 (R0))). (R4 (R1) (R0))
end)
*)
MetaCoq Run (create ex true false).
MetaCoq Run (create ex true true).
Print ex_ind_MC.



Inductive G (f:nat->bool) : nat -> Prop :=
  GI : forall n, (f n = false -> G f (S n)) -> G f n.


Print G_ind.
MetaCoq Quote Definition E_G := (fun (f : nat -> bool) (P : forall n, G f n -> Prop)
  (f0 : forall (n : nat) (h:f n = false -> G f (S n)), (forall (h2:f n = false), P (S n) (h h2)) -> P n (GI f n h)) =>
fix F (n : nat) (g : G f n) {struct g} : P n g :=
  match g in (G _ n0) return (P n0 g) with
  | @GI _ n0 g0 => f0 n0 g0 (fun e : f n0 = false => F (S n0) (g0 e))
  end).
(* MetaCoq Run(bruijn_print E_G). *)
(*
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ((G (R1) (R0))) -> Prop).
λ (f0 : ∀ (n : nat), ∀ (h : ((eq (bool) ((R2 (R0))) (false))) -> (G (R3) ((S (R1))))), (∀ (h2 : (eq (bool) ((R3 (R1))) (false))), (R3 ((S (R2))) ((R1 (R0))))) -> (R3 (R2) ((GI (R4) (R2) (R1))))).
(fix F : ∀ (n : nat), ∀ (g : (G (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (g : (G (R4) (R0))).
match R0 return λ (n0 : nat). λ (g : (G (R6) (R0))). (R6 (R1) (R0)) with
 | λ (n0 : nat). λ (g0 : ((eq (bool) ((R6 (R0))) (false))) -> (G (R7) ((S (R1))))). (R5 (R1) (R0) (λ (e : (eq (bool) ((R7 (R1))) (false))). (R5 ((S (R2))) ((R1 (R0))))))
end) *)
MetaCoq Run (create G false false).
MetaCoq Run (create G false true).
Print G_case_MC.
(*
λ (f : (nat) -> bool).
λ (p : (nat) -> ∀ (inst : (G (R1) (R0))), Prop).
λ (H_GI : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G (R3) ((S (R1))))) -> (R2 (R1) ((GI (R3) (R1) (R0))))).
(fix f : (nat) -> ∀ (inst : (G (R3) (R0))), (R3 (R1) (R0)) := 
λ (_ : nat). λ (inst : (G (R4) (R0))). 
match R0 return λ (_ : nat). λ (inst : (G (R6) (R0))). (R6 (R1) (R0)) with
 | λ (n : nat). λ (_ : ((eq (bool) ((R6 (R0))) (false))) -> (G (R7) ((S (R1))))). (R5 (R1) (R0))
end)
 *)

Print G.
MetaCoq Run (create G true false).
(*
λ (f : (nat) -> bool).
λ (p : (nat) -> ∀ (inst : (G (R1) (R0))), Prop).
λ (H_GI : ∀ (n : nat), (((eq (bool) ((R2 (R0))) (false))) -> (G (R3) ((S (R1))))) -> ∀ (IH : ((eq (bool) ((R3 (R1))) (false))) -> (R3 ((S (R2))) ((R1 (R0))))), (R3 (R2) ((GI (R4) (R2) (R1))))).
(fix f : (nat) -> ∀ (inst : (G (R3) (R0))), (R3 (R1) (R0)) :=
λ (_ : nat). λ (inst : (G (R4) (R0))).
match (P:1) R0 return λ (_ : nat). λ (inst : (G (R6) (R0))). (R6 (R1) (R0)) with
 | (2) λ (n : nat). λ (_ : ((eq (bool) ((R6 (R0))) (false))) -> (G (R7) ((S (R1))))). (R5 (R1) (R0) (λ (_ : (eq (bool) ((R6 (R1))) (false))). (R5 ((S (R2))) ((R1 (R0))))))
end)
*)

Print G.
MetaCoq Run (create G true true).
Print G_ind_MC.
Print G.
Print Acc.
MetaCoq Run (create Acc true false).
(* Print Acc_ind_MC. *) (* after move to test *)

(* Inductive G3 (f:nat->bool) (n:nat) : Prop := *)
(*   G3I : (f n = false -> G3 f (S n)) -> G3 f n. *)

(* Scheme Induction for G3 Sort Type. *)
(* Print G3_rect_dep. *)

(* Quote Definition E_G3 := (fun (f : nat -> bool) (p : forall n : nat, G3 f n -> Type) *)
(*   (HG3I : forall (n : nat) (h : f n = false -> G3 f (S n)), *)
(*         p n (G3I f n h)) => *)
(* fix F (n : nat) (g : G3 f n) {struct g} : p n g := *)
(*   match g as g0 return (p n g0) with *)
(*   | @G3I _ _ h => HG3I n h *)
(*   end). *)

(* MetaCoq Run (bruijn_print E_G3). *)


(*
λ (f : (nat) -> bool).
λ (p : ∀ (n : nat), ((G3 (R1) (R0))) -> LTop.654).
λ (HG3I : ∀ (n : nat), ∀ (h : ((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))), (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix F : ∀ (n : nat), ∀ (g : (G3 (R3) (R0))), (R3 (R1) (R0)) :=
λ (n : nat). λ (g : (G3 (R4) (R0))).
match R0 return λ (g0 : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | λ (h : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0))
end)
 *)


(*
λ (f : (nat) -> bool).
λ (P : ∀ (n : nat), ((G3 (R1) (R0))) -> LTop.2540).
λ (f0 : ∀ (n : nat), ∀ (g : ((eq (bool) ((R2 (R0))) (false))) -> (G3 (R3) ((S (R1))))), (R2 (R1) ((G3I (R3) (R1) (R0))))).
(fix F : ∀ (n : nat), ∀ (g : (G3 (R3) (R0))), (R3 (R1) (R0)) := 
λ (n : nat). λ (g : (G3 (R4) (R0))). 
match R0 return λ (g0 : (G3 (R5) (R1))). (R5 (R2) (R0)) with
 | λ (g0 : ((eq (bool) ((R5 (R1))) (false))) -> (G3 (R6) ((S (R2))))). (R4 (R2) (R0))
end)
 *)

MetaCoq Run (create G3 false false).
(*

 *)
(* MetaCoq Run (create G3 false true). *)
(* Print G3_case_MC. *)
(* MetaCoq Run (create G3 true true). *)
(* Print G3_ind_MC. *)

Print Acc.
MetaCoq Run (create Acc false true).
Print Acc_case_MC.
(* Print Acc_ind_MC. *) (* after move to test *)

(* Quote Definition E_Acc := *)
(*   fun (A:Type) (R:A->A->Prop) (p:forall (x:A), ) *)

(* MetaCoq Run (create Acc true true). *)
(* Print Acc_ind_MC. *)


Inductive G2 (f:nat->bool) : nat -> Prop :=
  G2I1 : forall n, (f n = false -> G2 f (S n)) -> (f n = true -> G2 f (S (S n))) -> G2 f n
| G2I2 : forall n, (f n = false -> G2 f (S n)) -> G2 f n.

MetaCoq Run (create G2 false true).
Print G2_case_MC.
MetaCoq Run (create G2 true true).
Print G2_ind_MC.

(** without params, indices **)

Inductive pfree : Type :=
  | p0 : pfree
  | p1 : pfree
  | p2 (n:nat) : pfree
  | p3 : pfree -> pfree
  | p4 (b:bool) (p:pfree) (n:nat) : pfree.

MetaCoq Run (create pfree false true).
Print pfree_case_MC.
MetaCoq Run (create pfree true true).
Print pfree_ind_MC.

MetaCoq Run (create bool false true).
Print bool_case_MC.
MetaCoq Run (create bool true true).
Print bool_ind_MC.

MetaCoq Run (create True false true).
Print True_case_MC.
MetaCoq Run (create True true true).
Print True_ind_MC.

MetaCoq Run (create False false true).
Print False_case_MC.
MetaCoq Run (create False true true).
Print False_ind_MC.

MetaCoq Run (create nat false false).
(* MetaCoq Run (create nat false true). *)
(* Print nat_case_MC. *) (* after move to test *)
Definition Enat :=
fun (p : nat -> Type) (H_O : p 0) (H_S : forall H : nat, p (S H)) =>
fix f (inst : nat) : p inst := match inst as inst0 return (p inst0) with
                               | 0 => H_O
                               | S x => H_S x
                               end.


(* MetaCoq Run (create nat true true). *)
(* Print nat_ind_MC. *) (* after move to test *)




