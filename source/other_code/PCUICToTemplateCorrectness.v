(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec ZArith.


From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.

Load PCUICToTemplate.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.




Module P := PCUICAst.
Module PT := PCUICTyping.
Module T := Template.Ast.
Module TT := Template.Typing.

Local Existing Instance default_checker_flags.

Module PL := PCUICLiftSubst.
Module TL := Template.LiftSubst.

About term.
About tApp.

Ltac solve_list :=
  rewrite !map_map_compose, ?compose_on_snd, ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mkAppMkApps s t:
  mkApp s t = mkApps s [t].
Proof.
  cbn. unfold mkApp.
  reflexivity.
Qed.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.




Lemma trans_lift (t:P.term) n k:
  trans(PL.lift n k t) = TL.lift n k (trans t).
Proof.
  revert k. induction t using PCUICInduction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite IHt1, IHt2.
    rewrite mkAppMkApps.
    rewrite <- mapOne.
    rewrite <- TL.lift_mkApps.
    f_equal.
  - f_equal; auto. red in X. solve_list.
  - f_equal; auto; red in X; solve_list.
  - f_equal; auto; red in X; solve_list.
Qed.





Definition on_fst {A B C} (f:A->C) (p:A×B) := (f p.1, p.2).

Definition trans_def (decl:def PCUICAst.term) : def term.
Proof.
  destruct decl.
  constructor.
  - exact dname.
  - exact (trans dtype).
  - exact (trans dbody).
  - exact rarg.
Defined.

Require Import FunInd.
Functional Scheme mem_ind := Induction for LevelSet.Raw.mem Sort Prop.

Lemma trans_global_ext_levels Σ:
PT.global_ext_levels Σ = global_ext_levels (trans_global Σ).
Proof.
  unfold global_ext_levels, PT.global_ext_levels.
  destruct Σ.
  cbn [trans_global fst snd].
  f_equal.
  induction g.
  - reflexivity.
  - Print global_levels.
    unfold PT.global_levels in IHg.
    cbn.
    rewrite IHg.
    f_equal.
    destruct a.
    cbn.
    unfold monomorphic_levels_decl, monomorphic_udecl_decl, on_udecl_decl.
    unfold PT.monomorphic_levels_decl, PT.monomorphic_udecl_decl, PT.on_udecl_decl.
    destruct g0.
    + cbn.
      destruct c.
      reflexivity.
    + cbn.
      destruct m.
      reflexivity.
Qed.

Lemma trans_mem_level_set l Σ:
LevelSet.mem l (PT.global_ext_levels Σ) ->
LevelSet.mem l (global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_in_level_set l Σ:
LevelSet.In l (PT.global_ext_levels Σ) ->
LevelSet.In l (global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.


Lemma trans_lookup Σ cst decl:
PT.lookup_env Σ.1 cst = Some decl ->
Typing.lookup_env (trans_global Σ).1 cst =
Some (trans_global_decl decl).
Proof.
  intros H.
  destruct Σ.
  cbn in *.
  induction g;cbn in H.
  - discriminate H.
  - cbn.
    destruct ident_eq.
    + destruct a.
      cbn in *.
      injection H as ->.
      reflexivity.
    + apply IHg, H.
Qed.

Lemma trans_declared_constant Σ cst decl:
PT.declared_constant Σ.1 cst decl ->
declared_constant (trans_global Σ).1 cst (trans_constant_body decl).
Proof.
  intros H.
  unfold declared_constant.
  unfold PT.declared_constant in H.
  apply trans_lookup in H as ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
ConstraintSet.In x (PT.global_ext_constraints Σ) ->
ConstraintSet.In x (trans_global Σ).
Proof.
  enough (PT.global_ext_constraints Σ = trans_global Σ) as ->.
  trivial.
  destruct Σ.
  unfold PT.global_ext_constraints, trans_global.
  cbn [fst snd].
Admitted.


Lemma trans_consistent_instance_ext Σ decl u:
PT.consistent_instance_ext Σ decl u ->
consistent_instance_ext (trans_global Σ) decl u.
Proof.
  intros H.
  unfold consistent_instance_ext, PT.consistent_instance_ext in *.
  unfold consistent_instance, PT.consistent_instance in *.
  destruct decl;trivial.
  destruct H as (?&?&?&?).
  repeat split;trivial.
  - eapply forallb_impl.
    2: apply H0.
    cbv beta.
    intros.
    now apply trans_mem_level_set.
  - unfold valid_constraints in *.
    destruct check_univs;trivial.
    unfold valid_constraints0 in *.
    intros.
    apply H2.
    unfold satisfies in *.
    unfold ConstraintSet.For_all in *.
    intros.
    apply H3.
    now apply trans_constraintSet_in.
Qed.

Lemma trans_declared_inductive Σ mdecl ind idecl:
PT.declared_inductive Σ.1 mdecl ind idecl ->
declared_inductive (trans_global Σ).1 (trans_minductive_body mdecl) ind (trans_one_ind_body idecl).
Proof.
  intros [].
  split.
  - unfold declared_minductive, PT.declared_minductive in *.
    apply trans_lookup in H as ->.
    reflexivity.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
trans (PCUICAst.mkApps t args) =
mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity. 
  - cbn [map].
  rewrite <- mkApps_mkApp.
  cbn.
  rewrite IHargs.
  reflexivity.
Qed.


Lemma trans_decl_type decl:
trans (PCUICAst.decl_type decl) =
decl_type (trans_decl decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma All_forall {X Y} (f:X->Y->Prop) xs: 
  All (fun a => forall b, f a b) xs ->
  (forall b, All (fun a => f a b) xs).
Proof.
  intros.
  induction X0.
  - constructor.
  - constructor.
    + apply p.
    + apply IHX0.
Qed.


Lemma trans_subst xs k t:
  trans (PL.subst xs k t) =
  subst (map trans xs) k (trans t).
Proof.
  induction t in k |- * using PCUICInduction.term_forall_list_ind.
  all: cbn;try congruence.
  - destruct leb;trivial.
    rewrite nth_error_map.
    destruct nth_error;cbn.
    2: now rewrite map_length.
    rewrite trans_lift.
    reflexivity.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    eapply All_forall in X.
    apply X.
  - rewrite IHt1, IHt2.
    destruct (trans t1);cbn;trivial.
    rewrite mkApp_mkApps.
    do 2 f_equal.
    rewrite map_app.
    cbn.
    reflexivity.
  - f_equal;trivial.
    do 2 rewrite map_map.
    apply All_map_eq.
    induction X;trivial.
    constructor.
    + destruct x.
      unfold on_snd;cbn.
      rewrite p0.
      reflexivity.
    + apply IHX.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e, e0.  
    + apply IHX.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e, e0.  
    + apply IHX.
Qed.


Lemma trans_subst10 u B:
trans (PL.subst1 u 0 B)=
subst10 (trans u) (trans B).
Proof.
  unfold PL.subst1.
  rewrite trans_subst.
  reflexivity.
Qed.

Lemma trans_subst_instance_constr u t:
trans (PCUICUnivSubst.subst_instance_constr u t) =
Template.UnivSubst.subst_instance_constr u (trans t).
Proof.
  induction t using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map. 
    f_equal.
    apply All_map_eq.
    apply X.
  - rewrite IHt1, IHt2.
    do 2 rewrite mkAppMkApps.
    rewrite subst_instance_constr_mkApps.
    cbn.
    reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2. 
    + do 2 rewrite map_map.
      unfold tCaseBrsProp in X.
      apply All_map_eq.
      induction X.
      * constructor.
      * constructor;trivial.
        destruct x.
        cbn.
        unfold on_snd.
        cbn. cbn in p0.
        rewrite p0.
        reflexivity.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e, e0.
    + apply IHX.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e, e0.
    + apply IHX.
Qed.

Lemma trans_cst_type decl:
trans (PCUICAst.cst_type decl) =
cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type idecl:
trans (PCUICAst.ind_type idecl) =
ind_type (trans_one_ind_body idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_type_of_constructor mdecl cdecl ind i u:
trans (PT.type_of_constructor mdecl cdecl (ind, i) u) =
type_of_constructor 
  (trans_minductive_body mdecl) 
  (trans_ctor cdecl)
  (ind,i)
  u.
Proof.
  unfold PT.type_of_constructor.
  rewrite trans_subst.
  unfold type_of_constructor.
  f_equal.
  - cbn [fst].
    rewrite PT.inds_spec.
    rewrite inds_spec.
    rewrite map_rev.
    rewrite map_mapi.
    destruct mdecl.
    cbn.
    f_equal.
    remember 0 as k.
    induction ind_bodies in k |- *.
    + reflexivity.
    + cbn.
      f_equal.
      apply IHind_bodies.
  - rewrite trans_subst_instance_constr.
    f_equal.
    destruct cdecl as [[? ?] ?].
    reflexivity.
Qed.

Lemma trans_dtype decl:
trans (dtype decl) =
dtype (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_dbody decl:
trans (dbody decl) =
dbody (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_declared_projection Σ mdecl idecl p pdecl :
PT.declared_projection Σ.1 mdecl idecl p pdecl ->
declared_projection (trans_global Σ).1 (trans_minductive_body mdecl) (trans_one_ind_body idecl) p (on_snd trans pdecl).
Proof.
  intros (?&?&?).
  split;[|split].
  - now apply trans_declared_inductive.
  - unfold on_snd.
    destruct pdecl, p.
    cbn in *.
    change (Some (i, trans t)) with
      (Some((fun '(x, y) => (x, trans y)) (i,t))).
    now apply map_nth_error.
  - now destruct mdecl;cbn in *.
Qed.


Import MonadNotation.

Lemma inv_opt_monad {X Y Z} (f:option X) (g:X->option Y) (h:X->Y->option Z) c:
  (x <- f;;
  y <- g x;;
  h x y) = Some c ->
  exists a b, f = Some a /\
  g a = Some b /\ h a b = Some c.
Proof.
  intros H.
  destruct f eqn: ?;cbn in *;try congruence.
  destruct (g x) eqn: ?;cbn in *;try congruence.
  do 2 eexists.
  repeat split;eassumption.
Qed.


Lemma trans_instantiate_params params pars ty:
  option_map trans 
  (PT.instantiate_params 
    params pars ty) = 
    instantiate_params (trans_local params) (map trans pars) (trans ty).
Proof.
  rewrite instantiate_params_, PT.instantiate_params_.
  rewrite option_map_two.
  Print instantiate_params_subst.
  match goal with
  |- option_map _ (_ _ _ ?A _) = option_map _ (_ _ _ ?B _) => change B with (map trans A)
  end.
  remember nil as xs.
  clear Heqxs.
  revert pars xs ty.
  induction params using rev_ind;intros pars xs ty.
  - cbn. destruct pars;trivial.
    cbn. now rewrite trans_subst.
  - unfold trans_local. 
    rewrite map_app. cbn.
    do 2 rewrite rev_unit. cbn.
    destruct x as [? [] ?];cbn.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. rewrite IHparams.
      cbn. now rewrite trans_subst.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. destruct pars;trivial.
      cbn. now rewrite IHparams.
Qed.


Lemma trans_instantiate_params' u mdecl idecl args npar x:
PT.instantiate_params
      (PCUICUnivSubst.subst_instance_context u (PCUICAst.ind_params mdecl))
      (firstn npar args)
      (PCUICUnivSubst.subst_instance_constr u (PCUICAst.ind_type idecl)) =
    Some x ->
 instantiate_params
   (subst_instance_context u
      (trans_local (PCUICAst.ind_params mdecl)))
   (firstn npar (map trans args))
   (subst_instance_constr u (trans (PCUICAst.ind_type idecl))) =
   Some (trans x).
Proof.
  intros H.
  rewrite <- trans_subst_instance_constr.
  rewrite firstn_map.
  match goal with
  |- instantiate_params ?A _ _ = _ =>
      replace A with (trans_local (PCUICUnivSubst.subst_instance_context u (PCUICAst.ind_params mdecl)))
  end.
  2: {
    unfold PCUICUnivSubst.subst_instance_context, trans_local.
    unfold PCUICAst.map_context.
    rewrite map_map.
    destruct mdecl.
    cbn. 
    clear H.
    induction ind_params;cbn in *;trivial.
    f_equal.
    - destruct a;cbn.
      unfold map_decl;cbn.
      do 2 rewrite option_map_two.
      f_equal.
      + destruct decl_body;cbn;trivial.
        now rewrite trans_subst_instance_constr.
      + now rewrite trans_subst_instance_constr.
    - apply IHind_params.
  }
  rewrite <- trans_instantiate_params.
  rewrite H.
  reflexivity.
Qed.

Lemma trans_destr_arity x:
destArity [] (trans x) 
= option_map (fun '(xs,u) => (map trans_decl xs,u)) (PT.destArity [] x).
Proof.
  remember (@nil PCUICAst.context_decl) as xs.
  replace (@nil context_decl) with (map trans_decl xs) by (now subst).
  clear Heqxs.
  induction x in xs |- *;cbn;trivial;unfold snoc, PCUICAst.snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
  - destruct (trans x1);cbn;trivial.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (PCUICAst.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (PCUICAst.it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map trans_decl xs) (trans t).
Proof.
  induction xs in t |- *;simpl;trivial.
  rewrite IHxs.
  f_equal.
  apply trans_mkProd_or_LetIn.
Qed.


Lemma trans_build_case_predicate_type ind mdecl idecl npar args u ps pty:
PT.build_case_predicate_type ind mdecl idecl (firstn npar args) u ps = Some pty ->
build_case_predicate_type ind (trans_minductive_body mdecl)
  (trans_one_ind_body idecl) (firstn npar (map trans args)) 
  u ps = Some (trans pty).
Proof.
  intros H.
  apply inv_opt_monad in H as (?&?&?&?&[=]).
  unfold build_case_predicate_type.
  simpl in *.
  apply trans_instantiate_params' in H as ->.
  simpl.
  rewrite trans_destr_arity, H0. 
  simpl. f_equal.
  rewrite <- H2.
  rewrite trans_it_mkProd_or_LetIn,
  trans_mkProd_or_LetIn.
  f_equal.
  - now destruct x0.
  - f_equal. cbn.
    f_equal.
    rewrite trans_mkApps. cbn.
    f_equal.
    destruct x0;cbn.
    rewrite map_app.
    rewrite map_map.
    clear H2.
    f_equal.
    + rewrite firstn_map.
      induction (firstn npar args);cbn;trivial.
      now rewrite IHl0, map_length, trans_lift.
    + remember 0 as n;clear Heqn.
      remember (@nil PCUICAst.term) as xs.
      replace (@nil term) with (map trans xs) by (now subst).
      clear Heqxs.
      induction l in n, xs |- *;cbn;trivial.
      now destruct a as [? [] ?];rewrite <- IHl;cbn.
Qed.


Lemma trans_fix_context mfix:
map trans_decl (PCUICLiftSubst.fix_context mfix) =
fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  destruct mfix;trivial.
  unfold fix_context, PCUICLiftSubst.fix_context.
  rewrite map_rev, map_mapi.
  cbn. f_equal.
  2: {
    destruct d. cbn.
    rewrite lift0_p.
    rewrite PCUICLiftSubst.lift0_p.
    unfold vass.
    reflexivity.
  }
  f_equal.
  unfold vass.
  remember 1 as k.
  induction mfix in k |- *;trivial.
  cbn;f_equal.
  - now rewrite trans_lift.
  - apply IHmfix.
Qed.



Lemma trans_wf_local':
  forall (Σ : PCUICAst.global_env_ext) Γ (wfΓ : PT.wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : PCUICAst.term) _ =>
           trans_global Σ0;;; trans_local Γ0 |- trans t : trans T)
    in
    PT.All_local_env_over PT.typing P Σ Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct tu. exists x. eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x. auto.
Qed.

Lemma trans_wf_local_env Σ Γ :
  PT.All_local_env
        (PT.lift_typing
           (fun (Σ : PCUICAst.global_env_ext) Γ b ty =>
              PT.typing Σ Γ b ty × trans_global Σ;;; trans_local Γ |- trans b : trans ty) Σ)
        Γ ->
  wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red. red in t1. destruct t1. eapply t2.
Qed.

Lemma trans_branches Σ Γ brs btys ps:
All2
   (fun br bty : nat × PCUICAst.term =>
    (((br.1 = bty.1 × PT.typing Σ Γ br.2 bty.2)
      × trans_global Σ;;; trans_local Γ |- trans br.2 : trans bty.2)
     × PT.typing Σ Γ bty.2 (PCUICAst.tSort ps))
    × trans_global Σ;;; trans_local Γ |- trans bty.2
      : trans (PCUICAst.tSort ps)) brs btys ->
All2
  (fun br bty : nat × term =>
   (br.1 = bty.1 × trans_global Σ;;; trans_local Γ |- br.2 : bty.2)
   × trans_global Σ;;; trans_local Γ |- bty.2 : tSort ps)
  (map (on_snd trans) brs) (map (fun '(x, y) => (x, trans y)) btys).
Proof.
  induction 1;cbn.
  - constructor.
  - constructor.
    + destruct r as [[[[] ] ] ].
      destruct x,y.
      cbn in *.
      repeat split;trivial.
    + apply IHX.
Qed.



Lemma trans_mfix_All Σ Γ mfix:
PT.All_local_env
  (PT.lift_typing
     (fun (Σ : PCUICEnvironment.global_env_ext)
        (Γ : PCUICEnvironment.context) (b ty : PCUICAst.term) =>
      PT.typing Σ Γ b ty
      × trans_global Σ;;; trans_local Γ |- trans b : trans ty) Σ)
  (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context mfix)) ->
wf_local (trans_global Σ)
  (trans_local Γ ,,, fix_context (map (map_def trans trans) mfix)).
Proof.
  intros.
  Print All_local_env.
  rewrite <- trans_fix_context.
  match goal with
  |- wf_local _ ?A =>
      replace A with (trans_local (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context mfix)))
  end.
  2: {
    unfold trans_local, PCUICAst.app_context.
    now rewrite map_app.
  }

  induction X;cbn;constructor;auto;cbn in *.
  - destruct t0 as (?&?&?).
    exists x.
    apply t1.
  - destruct t0 as (?&?&?).
    eexists;eassumption.
  - destruct t1.
    assumption.
Qed.


Lemma trans_mfix_All2 Σ Γ mfix xfix:
All
 (fun d : def PCUICAst.term =>
  (PT.typing Σ (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix))
   (dbody d)
   (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix| (dtype d))
   × PCUICAst.isLambda (dbody d) = true)
  × trans_global Σ;;;
    trans_local (PCUICAst.app_context Γ (PCUICLiftSubst.fix_context xfix))
    |- trans (dbody d)
    : trans
        (PCUICLiftSubst.lift0 #|PCUICLiftSubst.fix_context xfix|
           (dtype d))) mfix ->
All
  (fun d : def term =>
   trans_global Σ;;;
   trans_local Γ ,,, fix_context (map (map_def trans trans) xfix) |- 
   dbody d : lift0 #|fix_context (map (map_def trans trans) xfix)| (dtype d)
   × isLambda (dbody d) = true) (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - constructor.
    + destruct p as [[]].
      unfold app_context, PCUICAst.app_context in *.
      split.
      * unfold trans_local in t0.
        rewrite map_app, trans_fix_context in t0.
        rewrite trans_dbody, trans_lift, trans_dtype in t0.
        replace(#|PCUICLiftSubst.fix_context xfix|) with
            (#|fix_context (map(map_def trans trans) xfix)|) in t0.
        2: admit.
Admitted.


Lemma All_over_All Σ Γ wfΓ :
PT.All_local_env_over PT.typing
  (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
     (_ : PCUICTyping.wf_local Σ Γ) (t T : PCUICAst.term)
     (_ : PT.typing Σ Γ t T) =>
   trans_global Σ;;; trans_local Γ |- trans t : trans T) Σ Γ wfΓ ->
PT.All_local_env
  (PT.lift_typing
     (fun (Σ0 : PCUICAst.global_env_ext) (Γ0 : PCUICEnvironment.context)
        (b ty : PCUICAst.term) =>
      PT.typing Σ0 Γ0 b ty
      × trans_global Σ0;;; trans_local Γ0 |- trans b : trans ty) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  - constructor.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
    + cbn in *.
      split;eassumption.
Qed.



Theorem template_to_pcuic (Σ : P.global_env_ext) Γ t T :
  PT.wf Σ ->
  PT.typing Σ Γ t T ->
  typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.

  intros X X0.
  pose proof (PT.typing_wf_local X0).
  revert Σ X Γ X1 t T X0.
  apply (PT.typing_ind_env (fun Σ Γ t T =>
    typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type);intros.
(*
like induction but with
additional assumptions for the nested typing in All (in wf_local assumptions)
*)
  - rewrite trans_lift.
    rewrite trans_decl_type.
    eapply type_Rel.
    + now eapply trans_wf_local_env, All_over_All.
    + now apply map_nth_error.
  - eapply type_Sort.
    + now eapply trans_wf_local_env, All_over_All.
    + now apply trans_in_level_set.
  - eapply type_Prod;assumption.
  - eapply type_Lambda;eassumption.
  - eapply type_LetIn;eassumption.
  - eapply Generation.type_mkApp.
    + eassumption.
    + econstructor.
      3: eassumption.
      3: {
        rewrite trans_subst10.
        constructor.
      }
      2: {
        cbn. constructor.
        apply leq_term_refl.
      }
      admit. 
      (* 
      tProd na (trans A) (trans B) has a type
      obtain with inversion from IHX0_1
      *)
  - rewrite trans_subst_instance_constr.
    rewrite trans_cst_type.
    eapply type_Const.
    + now eapply trans_wf_local_env, All_over_All.
    + now apply trans_declared_constant.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_subst_instance_constr.
    rewrite trans_ind_type.
    eapply type_Ind.
    + now eapply trans_wf_local_env, All_over_All.
    + now apply trans_declared_inductive.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_type_of_constructor.
    eapply type_Construct.
    + now eapply trans_wf_local_env, All_over_All.
    + destruct isdecl. 
      constructor.
      * now apply trans_declared_inductive. 
      * now apply map_nth_error. 
    + now apply trans_consistent_instance_ext.
  - replace (trans (PCUICAst.mkApps p (skipn npar args ++ [c])))
    with (mkApps (trans p) (skipn npar (map trans args) ++ [trans c])).
    2: {
      rewrite trans_mkApps.
      rewrite map_app.
      cbn.
      repeat f_equal.
      now rewrite map_skipn.
    }
    eapply type_Case.
    + now apply trans_declared_inductive.
    + cbn. assumption.
    + apply trans_build_case_predicate_type.
      eassumption.
    + eassumption.
    + eassumption.
    + rewrite trans_mkApps in X4.
      cbn in X4.
      apply X4.
    + admit. (* map_option_out build branche type *)
    + now apply trans_branches.
  - rewrite trans_subst.
    rewrite trans_subst_instance_constr.
    cbn.
    rewrite map_rev.
    change (trans ty) with ((on_snd trans pdecl).2).
    eapply type_Proj.
    + now apply trans_declared_projection.
    + rewrite trans_mkApps in X2.
      assumption.
    + rewrite map_length.
      rewrite H.
      destruct mdecl.
      reflexivity.
  - rewrite trans_dtype.
    eapply type_Fix.
    + admit. (* fix guard *)
    + erewrite map_nth_error. 
      2: apply H.
      destruct decl.
      unfold map_def.
      reflexivity.
    + fold trans.
      eapply trans_mfix_All;eassumption.
    + fold trans.
      subst types.
      eapply trans_mfix_All2;eassumption.
  - rewrite trans_dtype.
    eapply type_CoFix.
    + trivial.
    + erewrite map_nth_error. 
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + fold trans.
      eapply trans_mfix_All;eassumption.
    + fold trans;subst types.
      (* like trans_mfix_All2 without isLambda *)
      admit.
  - eapply type_Conv.
    + eassumption.
    + admit. (* trans isWfArity *)
    + admit. (* trans_cumul *)
Admitted.
