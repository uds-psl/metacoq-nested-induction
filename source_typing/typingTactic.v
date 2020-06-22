Require Import Recdef.
Require Import Coq.omega.Omega.
Require Import Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.

Unset Template Cast Propositions.

MetaCoq Quote Recursively Definition idq := @Coq.Classes.Morphisms.Proper.

Existing Instance config.default_checker_flags.
Existing Instance Checker.default_fuel.


Definition timpl x y := tProd nAnon x (LiftSubst.lift0 1 y).

Unset Printing Matching.

Ltac typecheck := try red; cbn; intros;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [reflexivity|constructor|vm_compute; reflexivity]
  end.
Ltac infer := try red;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [reflexivity|constructor|
      let t' := eval vm_compute in (infer' Σ Γ t) in
          change (t' = Checked T); reflexivity]
  end.

Definition type_program (p : program) (ty : term) :=
  let Σ := empty_ext (fst p) in
  Σ ;;; [] |- snd p : ty.

Definition test_reduction (p : program) :=
    let Σ := empty_ext (fst p) in
    reduce (fst Σ) [] (snd p).

Definition string_of_env_error e :=
  match e with
  | IllFormedDecl s e => ("IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error e)%string
  | AlreadyDeclared s => ("Alreadydeclared " ++ s)%string
  end.

Definition out_typing c :=
  match c with
  | Checked t => t
  | TypeError e => tVar ("Typing error")%string
  end.

Definition out_check c :=
  match c with
  | CorrectDecl t => t
  | EnvError e => tVar ("Check error: " ++ string_of_env_error e)%string
  end.

Ltac interp_red c :=
  let t:= eval vm_compute in (out_typing (test_reduction c)) in exact t.

Ltac interp_infer c :=
  let t:= eval vm_compute in (out_check (typecheck_program c)) in exact t.

Ltac term_type c :=
  let X := type of c in exact X.

Ltac quote_type c :=
  let X := type of c in
  quote_term X ltac:(fun Xast => exact Xast).

Notation convertible x y := (@eq_refl _ x : x = y).


