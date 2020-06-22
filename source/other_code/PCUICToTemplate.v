(* Distributed under the terms of the MIT license.   *)

Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
About term.
From MetaCoq.Template Require Import config utils AstUtils BasicAst Ast.

Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

About term.
About Ast.term.
About PCUICAst.term.

Print tInd.
About inductive.
About tInd.

Fixpoint trans (t : PCUICAst.term) : Ast.term :=
  match t with
  | PCUICAst.tRel n => tRel n
  | PCUICAst.tVar n => tVar n
  | PCUICAst.tEvar ev args => tEvar ev (List.map trans args)
  | PCUICAst.tSort u => tSort u
  | PCUICAst.tConst c u => tConst c u
  | PCUICAst.tInd c u => tInd c u
  | PCUICAst.tConstruct c k u => tConstruct c k u
  | PCUICAst.tLambda na T M => tLambda na (trans T) (trans M)
  | PCUICAst.tApp u v => mkApp (trans u) (trans v)
  | PCUICAst.tProd na A B => tProd na (trans A) (trans B)
  (* | PCUICAst.tCast c kind t => tApp (tLambda nAnon (trans t) (tRel 0)) (trans c) *)
  | PCUICAst.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | PCUICAst.tCase ind p c brs =>
    let brs' := List.map (on_snd trans) brs in
    tCase ind (trans p) (trans c) brs'
  | PCUICAst.tProj p c => tProj p (trans c)
  | PCUICAst.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | PCUICAst.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  end.

Definition trans_decl (d : PCUICAst.context_decl) :=
  let 'PCUICAst.mkdecl na b t := d in
  {| decl_name := na;
     decl_body := option_map trans b;
     decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_ctor : (ident × PCUICAst.term) × nat -> (ident × term) × nat 
  := fun '(x, y, z) => (x, trans y, z).

Definition trans_one_ind_body (d : PCUICAst.one_inductive_body) :=
  {| ind_name := d.(PCUICAst.ind_name);
     ind_type := trans d.(PCUICAst.ind_type);
     ind_kelim := d.(PCUICAst.ind_kelim);
     ind_ctors := List.map trans_ctor d.(PCUICAst.ind_ctors);
     ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(PCUICAst.ind_projs) |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(PCUICAst.cst_type); cst_body := option_map trans bd.(PCUICAst.cst_body);
     cst_universes := bd.(PCUICAst.cst_universes) |}.

Print mutual_inductive_body.
Print Variance.t.

Definition trans_minductive_body md :=
  {| ind_finite := md.(PCUICAst.ind_finite);
     ind_npars := md.(PCUICAst.ind_npars);
     ind_params := trans_local md.(PCUICAst.ind_params);
     ind_bodies := map trans_one_ind_body md.(PCUICAst.ind_bodies);
     ind_universes := md.(PCUICAst.ind_universes);
     ind_variance := md.(PCUICAst.ind_variance)
  |}.

Definition trans_global_decl (d : PCUICAst.global_decl) :=
  match d with
  | PCUICAst.ConstantDecl bd => ConstantDecl (trans_constant_body bd)
  | PCUICAst.InductiveDecl bd => InductiveDecl (trans_minductive_body bd)
  end.

Definition trans_global_decls (d : PCUICAst.global_env) : global_env :=
  List.map (on_snd trans_global_decl) d.

Definition trans_global (Σ : PCUICAst.global_env_ext) : global_env_ext :=
  (trans_global_decls (fst Σ), snd Σ).
