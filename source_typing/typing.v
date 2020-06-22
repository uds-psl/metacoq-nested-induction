Require Import List.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

(*
Notation for Admitted:
admit              not possible
Universe           lemmas with universes
Basic              basic lemmas of MetaCoq and functions
TODO               lemmas directly in this plugin
 *)

Load destruct_lemma.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.

(* didn't helped *)
(* From Hammer Require Import Hammer. *)



Print trans.

Check Build_on_ind_body.
Print on_ind_body.
Check ind_arity_eq.
Print lift_typing.

Check (forall Σ mind mdecl idecl i, on_ind_body (lift_typing typing) Σ mind mdecl i idecl).

Print getPCount.
Print getParamCount.
Print countOfCtor.

Print typing_spine.
Check Generation.type_mkApp.


(* Section Tactics. *)

Ltac typecheck2 := try red; cbn; intros;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [reflexivity|constructor|vm_compute; reflexivity]
  end.
Ltac infer2 := try red;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [|constructor|
      let t' := eval vm_compute in (infer' Σ Γ t) in
          change (t' = Checked T); reflexivity]
  end.
Ltac infer2Try := try red;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [|try constructor|
      try (let t' := eval vm_compute in (infer' Σ Γ t) in
          change (t' = Checked T); reflexivity)]
  end.

Ltac rewrite_it_mk H :=
  let tH := fresh in
  pose proof H as tH;
  unfold vass in tH;
  unfold it_mkLambda_or_LetIn in tH;
  unfold it_mkProd_or_LetIn in tH;
  rewrite tH;clear tH.

Ltac maxElimProof:= (unfold getMaxElim;do 2 (destruct canElim;cbn;trivial)).

Ltac uniapply H := revert H;
                   match goal with
                     |- ?A -> ?B => replace A with B
                   end;[trivial | ].

Ltac f_equal_typing := match goal with
              |- ?S1;;;?G1|- ?a1 : ?b1 = ?S2;;;?G2|- ?a2 : ?b2 =>
              replace b1 with b2;
                [replace a1 with a2;
                  [replace G1 with G2;
                  [replace S1 with S2
                  |]
                |]
              |]
                       end;trivial.

Ltac f_equal_wf_local := match goal with
              |- wf_local ?a1 ?b1 = wf_local ?a2 ?b2 =>
              replace b1 with b2;
                [replace a1 with a2
              |]
            end;trivial.


(* End Tactics. *)

Section Basic.

Lemma rev_elim A:
      forall P:list A -> Type,
        P [] ->
        (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
Proof.
  intros P H0 Hs l.
  replace l with (rev(rev l)).
  remember (rev l) as l'.
  clear Heql' l.
  induction l'.
  - apply H0.
  - cbn. apply Hs. eapply IHl'.
  - induction l;cbn.
    + reflexivity.
    + now rewrite rev_unit, IHl.
Qed.

Lemma fold_right_min m xs: fold_right min m xs <= m.
Proof.
  induction xs;cbn.
  - constructor.
  - etransitivity.
    + apply Min.le_min_r.
    + apply IHxs.
Qed.

Lemma lengthAppend {X} (xs ys:list X): #|xs++ys| = #|xs| + #|ys|.
Proof.
  induction xs in ys |- *;cbn.
  - reflexivity.
  - now rewrite IHxs.
Qed.

Lemma revLen {X} (xs:list X): #|rev xs| = #|xs|.
Proof.
  induction xs.
  - reflexivity.
  - cbn. now rewrite lengthAppend, add_comm.
Qed.

Lemma revInj {X} (xs ys:list X): rev xs = rev ys -> xs = ys.
Proof.
  induction xs using rev_ind in ys |- *.
  - destruct ys using rev_ind;cbn.
    + trivial.
    + rewrite rev_unit. congruence.
  - destruct ys using rev_ind;cbn.
    + rewrite rev_unit. congruence.
    + do 2 rewrite rev_unit.
      now intros [=-> ->%IHxs].
Qed.

Lemma revRev {X} (xs:list X): rev(rev xs) = xs.
Proof.
  induction xs;trivial;cbn.
  now rewrite rev_unit, IHxs.
Qed.

Lemma le_elim (A:nat->Type):
  forall n : nat, A n -> (forall m : nat, n <= m -> A m -> A (S m)) -> forall m : nat, n <= m -> A m.
Proof.
Admitted. (* Basic *)

Lemma mapiSub {X Y} (f:nat -> X -> Y) (xs:list X) m:
  m >= #|xs| ->
  mapi (fun i a => f (m - i) a) xs = mapi (fun i a => f (S(m - i - 1)) a) xs.
Proof.
  unfold mapi.
  remember 0 as n.
  replace (S n) with 1 by now subst n.
  assert(n < m) by admit.
  intros F.
  induction xs in f, n, m, H, F |- *.
  - reflexivity.
  - cbn [mapi_rec].
    f_equal.
    + f_equal. lia.
    + rewrite IHxs.
      * reflexivity.
      * admit.
      * cbn in F.
        admit.
Admitted. (* Basic *)

Lemma in_app_or {X} (x:X) xs ys: In x (xs++ys) -> In x xs \/ In x ys.
Proof.
  intros H.
  induction xs in ys, H |- *.
  - now right.
  - destruct H as [-> | H].
    + left. now left.
    + apply IHxs in H as [].
      * left. now right.
      * now right.
Qed.

Lemma pointLessIf {Y} (x:bool) (a:Y): (if x then a else a) = a.
Proof.
  now destruct x.
Qed.

End Basic.



Section PICUICTheory.

  Check type_it_mkLambda_or_LetIn.
Print Assumptions type_it_mkLambda_or_LetIn.

Lemma type_it_mkLambda_or_LetIn: forall (Σ : global_env_ext) (Γ Δ : context) (t A : term),
       typing Σ (app_context Γ Δ) t A ->
       typing Σ Γ (it_mkLambda_or_LetIn Δ t) (it_mkProd_or_LetIn Δ A).
Proof.
Admitted. (* Done *)

Print type_Lambda.
(*
  | type_Lambda : forall (n : name) (t b : term) (s1 : universe) (bty : term),
                  Σ;;; Γ |- t : tSort s1 -> Σ;;; Γ,, vass n t |- b : bty -> Σ;;; Γ |- tLambda n t b : tProd n t bty
 *)

Lemma type_Lambda2: forall (Σ : global_env_ext) (Γ : context) n t (b bty : term),
Σ;;; Γ,, vass n t |- b : bty -> Σ;;; Γ |- tLambda n t b : tProd n t bty.
Proof.
  intros.
  change (tProd n t0 bty) with
      (it_mkProd_or_LetIn [vass n t0] bty).
  change (tLambda n t0 b) with
      (it_mkLambda_or_LetIn [vass n t0] b).
  apply type_it_mkLambda_or_LetIn, X.
Qed.




(* Print wf_local_app_inv. *)
Lemma wf_local_app_inv Σ Γ1 Γ2:
  All_local_env (lift_typing typing Σ) Γ1 ->
  wf_local_rel Σ Γ1 Γ2 ->
  All_local_env (lift_typing typing Σ)
  (app_context Γ1 Γ2).
Proof.
Admitted. (* Done *)

Check wf_local_rel_app_inv.
Lemma wf_local_rel_app_inv Σ Γ1 Γ2 Γ3:
     wf_local_rel Σ Γ1 Γ2 ->
     wf_local_rel Σ (Γ1 ,,, Γ2) Γ3 -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3).
Proof.
Admitted. (* Done *)

End PICUICTheory.



Section MetaCoqTheorem.

Lemma foldMkLambda xs name type x:
  it_mkLambda_or_LetIn (xs++[vass name type]) x =
  tLambda name type (it_mkLambda_or_LetIn xs x).
Proof.
  induction xs in x |- *.
  - reflexivity.
  - cbn. apply IHxs.
Qed.

Lemma foldMkProdLetIn xs name body type x:
  it_mkProd_or_LetIn (xs++[vdef name body type]) x =
  tLetIn name body type (it_mkProd_or_LetIn xs x).
Proof.
  induction xs in x |- *.
  - reflexivity.
  - cbn. apply IHxs.
Qed.

Lemma foldMkProd xs name type x:
  it_mkProd_or_LetIn (xs++[vass name type]) x =
  tProd name type (it_mkProd_or_LetIn xs x).
Proof.
  induction xs in x |- *.
  - reflexivity.
  - cbn. apply IHxs.
Qed.

Lemma foldMkLambdaUnfold xs name type x:
  fold_left (fun (acc : term) (d : context_decl) => mkLambda_or_LetIn d acc) (xs++[vass name type]) x =
  tLambda name type (it_mkLambda_or_LetIn xs x).
Proof.
  induction xs in x |- *.
  - reflexivity.
  - cbn. apply IHxs.
Qed.

(* fold doesn't work *)
Lemma foldMkProdUnfold xs name type x:
  fold_left (fun (acc : term) (d : context_decl) => mkProd_or_LetIn d acc) (xs++[vass name type]) x =
  tProd name type (it_mkProd_or_LetIn xs x).
Proof.
  induction xs in x |- *;cbn.
  - reflexivity.
  - cbn. apply IHxs.
Qed.

Lemma lifttInd ind u n k: lift n k (tInd ind u) = tInd ind u.
Proof.
  reflexivity.
Qed.

(*  *)
(* done by weakening *)
(* cyclic dependency with wfLocalToRel *)
Lemma typingApp Σ Γ Γ0 t T: Σ;;; Γ0 |- t : T -> Σ;;; (Γ0 ++ Γ) |- t : T.
Proof.
  intros.
  (* intros H. *)
  (* induction H. *)
  (* - constructor. *)
  (*   + apply wf_local_app_inv. *)
  (*     * admit. *)
  (*     * admit. (* cyclic dependency with wfLocalToRel *) *)
  (*   + admit. *)
  (* - constructor. *)
Admitted. (* Done *)

Lemma wfLocalToRel Σ Γ Γ0: wf_local Σ Γ -> wf_local Σ Γ0 -> wf_local_rel Σ Γ Γ0.
Proof.
  intros.
  induction Γ0 in Γ, X, X0 |- *.
  - constructor.
  -
    (* assert(forall n k, lift_context n k (a::Γ0) = a::Γ0). *)
    (* { *)
    (*   intros. *)
    (*   eapply lift_wf_local. *)
    (*   2: apply X0. *)
    (*   admit. *)
    (* } *)
    inversion X0;subst.
    + destruct X2.
      apply wf_local_rel_abs.
      * now apply IHΓ0.
      *
        (* assert(t0 = lift0 #|Γ0| t0). *)
        (* { *)
        (*   admit. *)
        (* } *)
        eexists.
        (* apply weakening. *)
        now apply typingApp. (* use weakening *)
    + cbn in X2, X3. destruct X2.
      apply wf_local_rel_def.
      * now apply IHΓ0.
      * eexists.
        apply typingApp, t1. (* use weakening *)
      * apply typingApp, X3. (* use weakening *)
Qed. (* TODO *)

Lemma indParamVass mind_body ind Σ:
  on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body ->
  forall x : context_decl, In x (ind_params mind_body) -> decl_body x = None.
Proof.
  destruct mind_body.
  intros [].
  cbn in *.
  clear onGuard onInductives.
  (* inv onParams. *)
  (* - intros x []. *)
  (* - intros  *)
  (* 1-2: admit. *)
  (* cbn in X0, X1. *)
  (* inv onNpars. *)
Admitted. (* Basic *)

Lemma liftAdd n m s: lift0 n (lift0 m s) = lift0 (n+m) s.
Proof.
  rewrite simpl_lift;trivial.
  lia.
Qed.

End MetaCoqTheorem.




Section Functions.

Definition isProd := fun t : term => match t with
                           | tProd _ _ _ => true
                           | _ => false
                                  end.

Definition isLetIn := fun t : term => match t with
                           | tLetIn _ _ _ _ => true
                           | _ => false
                                   end.


Fixpoint mapProdToLambda2 (u:term) : term :=
  match u with
    tProd na t1 t2 => tLambda na t1 (mapProdToLambda2 t2)
  | _ => u
  end.

Definition createElimType (isInductive:bool) (ind:inductive) (univ:universe_instance) (ind_body:mutual_inductive_body) (returnType:option term) (nameFun:name->term->name) :=
  (* take params *)
    (* p *)
  (* var for cases *)
  (* f *)
  (* indices *)
  (* instance *)
  match nth_error ind_body.(ind_bodies) ind.(inductive_ind) with
  | None => None
  | Some one_body => Some(
  (* let paramCount := ind_body.(ind_npars) in *)
  let trueParamCount := getParamCount one_body ind_body.(ind_npars) in
  let nonUniformArgCount := ind_body.(ind_npars) - trueParamCount in

  let allParams := ind_body.(ind_params) in
  let trueParams := skipn nonUniformArgCount allParams in

  let trueParamCtors := one_body.(ind_ctors) in
  let allParamCtors := map (on_snd (plus nonUniformArgCount)) one_body.(ind_ctors) in

  let type := tInd ind univ in
  let ind_applied := (* typ applied with params *)
      mkApps type (mapi (fun i _ => tRel (trueParamCount-i-1)) trueParams)
  in
  let nuIndex_type := remove_arity trueParamCount one_body.(ind_type) in
  let allIndCount := (* count of indices and non Uniform *)
      count_prods nuIndex_type
  in
  let ctorCount := #|trueParamCtors| in
  let predType :=
      replaceLastProd
        (
            (* add ∀ for instance *)
            (tProd (nNamed "inst"%string)
                  (createAppChain (lift0 allIndCount ind_applied) allIndCount)
                (* if prop => elim over prop *)
                (* if type => elim over type *)
              (match returnType with None => getMaxElim one_body.(ind_kelim) | Some t => t end)
          )
        )
        (* quantify over indices but not over params *)
        nuIndex_type in
  (* quantify over all params *)
  it_mkProd_or_LetIn trueParams
  (tProd
     (* predicate *)
     (nNamed "p"%string)
     (* the type of p is a transformation of the type
      todo: fold indices for type of p or use the type in index construction below
      for consistency*)
     predType
     (
       it_mkProd_or_LetIn (rev (quantifyCases isInductive allParamCtors trueParamCount ind univ))
        (*
          theoretically recursive fix after cases
         *)
         (
               replaceLastProd'
               (lift0 (S ctorCount) predType)
               (createAppChain (tRel (allIndCount + S ctorCount)) (S allIndCount))
  )))
  )
  end.

End Functions.




Section CustomFunction.

Lemma removeArityProds2 t: remove_arity (count_prods t) t = remove_prods t.
Proof.
  induction t;cbn;try congruence.
  now rewrite IHt2.
Qed.

Lemma removeArityProds t: exists n, remove_arity n t = remove_prods t.
Proof.
  induction t.
  6: {
    destruct IHt2.
    now exists (S x).
  }
  all: try (exists 0;cbn;congruence).
Qed.

Lemma removeArityProdCount t: remove_arity (count_prods t) t = remove_prods t.
Proof.
  induction t;cbn;try congruence.
  apply IHt2.
Qed.

Lemma replaceLastLambdaSelf t: replaceLastLambda (remove_lambdas t) t = t.
Proof.
  induction t;cbn;try congruence.
  pose proof foldMkLambda.
  unfold replaceLastLambda in *.
  unfold it_mkLambda_or_LetIn in *.
  now rewrite H, IHt2.
Qed.

Lemma replaceLastProdSelf t: replaceLastProd (remove_prods t) t = t.
Proof.
  induction t;cbn;try congruence.
  pose proof foldMkProd.
  unfold replaceLastProd in *.
  unfold it_mkProd_or_LetIn in *.
  now rewrite H, IHt2.
Qed.

Lemma quantifyCasesType Σ Γ ctors pC univ ind T r:
Σ ;;; rev (quantifyCases false ctors pC ind univ) ++ Γ |- r : T ->
Σ ;;; Γ |- it_mkLambda_or_LetIn (rev (quantifyCases false ctors pC ind univ)) r :
  it_mkProd_or_LetIn (rev (quantifyCases false ctors pC ind univ)) T.
Proof.
  apply type_it_mkLambda_or_LetIn.
Qed.

Lemma replaceUnderOneLambda n lt s t:
  replaceLastLambda t (tLambda n lt s) =
  tLambda n lt (replaceLastLambda t s).
Proof.
  cbn. pose proof foldMkLambda.
  unfold it_mkLambda_or_LetIn in H.
  now rewrite H.
Qed.

Lemma replaceUnderLambda s xs t:
  (forall x, In x xs -> decl_body x = None) ->
  replaceLastLambda t (it_mkLambda_or_LetIn xs s) =
  it_mkLambda_or_LetIn xs (replaceLastLambda t s).
Proof.
  induction xs in s |- *;cbn;intros H.
  - reflexivity.
  - unfold replaceLastLambda, it_mkLambda_or_LetIn in *.
    rewrite IHxs.
    + f_equal.
      pose proof (replaceUnderOneLambda).
      unfold replaceLastLambda, it_mkLambda_or_LetIn in H0.
      unfold mkLambda_or_LetIn at 2 3.
      now rewrite H.
    + intros x F. apply H. now right.
Qed.

Lemma replaceLastTypeLambdaItLam Σ Γ t s T2 xs:
  (forall x, In x xs -> decl_body x = None) ->
  Σ;;;Γ,,,xs |- replaceLastLambda (s) t : T2 ->
  forall T3, T3 = it_mkProd_or_LetIn xs T2 ->
  Σ;;;Γ |- replaceLastLambda (s) (it_mkLambda_or_LetIn xs t) : T3.
Proof.
  intros H0 H T3 ->.
  rewrite replaceUnderLambda.
  now apply type_it_mkLambda_or_LetIn.
  intros x H1. now apply H0.
Qed.

Lemma replaceLastTypeLambda Σ Γ t s T2:
  Σ;;;(rev (collect_lambdas t)++Γ) |- s : T2 ->
  forall T3, T3 = it_mkProd_or_LetIn (rev (collect_lambdas t)) T2 ->
  Σ;;;Γ |- replaceLastLambda s t : T3.
Proof.
  intros H T3 ->.
  induction t in Γ, H, T2 |- *;cbn;trivial.
  rewrite_it_mk foldMkLambda.
  rewrite_it_mk foldMkProd.
  apply typing_wf_local in H as H2.
  cbn in H2.
  rewrite <- app_assoc in H2.
  apply wf_local_app in H2.
  cbn in H2.
  pose proof (wf_local_inv H2).
  specialize (X (vass na t1) Γ).
  destruct X;trivial.
  destruct y as (u&ty&H1&H3).
  cbn in ty.
  eapply type_Lambda.
  - apply ty.
  - apply IHt2.
    cbn in H.
    rewrite <- app_assoc in H.
    apply H.
Qed.

Lemma replaceLastTypeProd Σ Γ t s T2:
  (forall x xs1 xs2 T, xs1++x::xs2=collect_prods t -> Σ;;;(rev xs1++Γ)|-decl_type x:tSort T -> Universe.sort_of_product T T2=T2) ->
  Σ;;;(rev (collect_prods t)++Γ) |- s : tSort T2 ->
  forall T3, T3 = T2 ->
  Σ;;;Γ |- replaceLastProd s t : tSort T3.
Proof.
  intros H0 H T3 ->.
  induction t in Γ, H0, H, T2 |- *;cbn;trivial.
  rewrite_it_mk foldMkProd.
  apply typing_wf_local in H as H2.
  cbn in H2.
  rewrite <- app_assoc in H2.
  apply wf_local_app in H2.
  cbn in H2.
  edestruct (wf_local_inv H2);trivial.
  destruct y as (u&ty&_&_).
  cbn in ty.
  cbn in H0.
  pose proof H0 as H0'.
  specialize (H0 (vass na t1) [] (collect_prods t2)).
  erewrite <- H0.
  2: reflexivity.
  2: {
    cbn.
    apply ty.
  }
  - apply type_Prod.
    + apply ty.
    + apply IHt2.
      * intros.
        unfold snoc in X.
        eapply H0' with (xs1 := vass na t1::xs1).
        -- cbn. f_equal. rewrite <- H1.
           reflexivity.
        -- cbn. rewrite <- app_assoc. cbn.
           apply X.
      * unfold snoc.
        cbn in H. rewrite <- app_assoc in H. apply H.
Qed.

Lemma collectProdVass t x: In x (collect_prods t) -> decl_body x = None.
Proof.
  induction t;cbn;try tauto.
  intros [<- | H];cbn;trivial.
  now apply IHt2.
Qed.

Lemma isProdInv s: isProd s = true -> {n&{t1&{t2&s = tProd n t1 t2}}}.
Proof.
  intros H.
  destruct s;cbn in H;try congruence.
  repeat eexists;reflexivity.
Qed.

Lemma isLambdaInv s: isLambda s = true -> {n&{t1&{t2&s = tLambda n t1 t2}}}.
Proof.
  intros H.
  destruct s;cbn in H;try congruence.
  repeat eexists;reflexivity.
Qed.

Lemma RLProdIsProd s t: isProd s=true -> isProd (replaceLastProd s t) = true.
Proof.
  intros (n&s1&s2&->)%isProdInv.
  destruct t;cbn;try reflexivity.
  pose proof (foldMkProd).
  unfold it_mkProd_or_LetIn in H.
  rewrite H. reflexivity.
Qed.

Lemma RLLambdaIsLambdaInner s t: isLambda s=true -> isLambda (replaceLastLambda s t) = true.
Proof.
  intros (n&s1&s2&->)%isLambdaInv.
  destruct t;cbn;try reflexivity.
  pose proof (foldMkLambda).
  unfold it_mkLambda_or_LetIn in H.
  rewrite H. reflexivity.
Qed.

Lemma RLLambdaIsLambdaOuter s t: isLambda t=true -> isLambda (replaceLastLambda s t) = true.
Proof.
  intros (n&s1&s2&->)%isLambdaInv.
  cbn.
  pose proof (foldMkLambda).
  unfold it_mkLambda_or_LetIn in H.
  rewrite H. reflexivity.
Qed.

Lemma LiftIsProd s n m: isProd s -> isProd (lift n m s).
Proof.
  intros (na&s1&s2&->)%isProdInv.
  reflexivity.
Qed.

Lemma mapIsProdLam s: isProd s -> isLambda (mapProdToLambda s).
Proof.
  intros (na&s1&s2&->)%isProdInv.
  cbn.
  pose proof (foldMkLambda).
  unfold it_mkLambda_or_LetIn in H.
  rewrite H. reflexivity.
Qed.

Lemma mapAgreement s: mapProdToLambda2 s = mapProdToLambda s.
Proof.
  induction s;cbn;try congruence.
  rewrite IHs2.
  pose proof (foldMkLambda).
  unfold it_mkLambda_or_LetIn in H.
  rewrite H. reflexivity.
Qed.

Lemma collectLambdaProdDisjoint t:
  collect_lambdas t <> [] -> collect_prods t = [].
Proof.
  induction t;cbn;trivial.
  congruence.
Qed.

Lemma collectProdLambdaDisjoint t:
  collect_prods t <> [] -> collect_lambdas t = [].
Proof.
  induction t;cbn;trivial.
  congruence.
Qed.

Lemma collectLambdaMapIsNotLambda t: ~isLambda (remove_prods t) ->
  collect_lambdas (mapProdToLambda t) = collect_prods t.
Proof.
  induction t;cbn;trivial.
  - rewrite_it_mk foldMkLambda;cbn.
    now intros ->%IHt2.
  - congruence.
Qed.

Lemma removeReplaceProd s t: remove_prods (replaceLastProd s t) = remove_prods s.
Proof.
  induction t;cbn;trivial.
  now rewrite_it_mk foldMkProd.
Qed.

Lemma minChainMin n m xs: getMinChain n m xs >= m.
Proof.
  induction xs in n, m |- *.
  - constructor.
  - cbn. destruct a;cbn;try constructor.
    destruct n;try constructor.
    destruct Nat.eqb eqn:H;try constructor.
    unfold ge.
    etransitivity.
    2: apply IHxs.
    do 2 constructor.
Qed.

Lemma minChainMax n m xs: getMinChain n m xs <= m+#|xs|.
Proof.
  induction xs in n, m |- *;cbn.
  - lia.
  - destruct a;cbn;try lia.
    destruct n;try lia.
    destruct Nat.eqb;try lia.
    etransitivity.
    + apply IHxs.
    + lia.
Qed.


Lemma countMax n m c : countOfCtor n m c <= m.
Proof.
  induction c in n |- *;cbn;try constructor.
  - etransitivity.
    apply Min.le_min_l.
    apply IHc1.
  - pose proof (fold_right_min (countOfCtor n m c) (map (countOfCtor n m) args)).
    pose proof (fold_right_min m (map (countOfCtor n m) args)).
    pose proof (Nat.le_trans _ _ _ H (IHc _));clear H.
    revert H0;destruct c;try trivial;intros H0.
    destruct Nat.eqb;trivial.
Abort.

Lemma getParamCountBound indb mind: getParamCount indb (ind_npars mind) <= ind_npars mind.
Proof.
  destruct indb.
  induction ind_ctors.
  - constructor.
  - cbn.
    etransitivity.
    + apply Min.le_min_l.
    + apply IHind_ctors.
Qed.

Lemma nonUniCount n mind: forall k, getPCount mind n = Some k -> k <= ind_npars mind.
Proof.
  unfold getPCount.
  intros.
  destruct nth_error;cbn in H;try congruence.
  injection H as H.
  subst k.
  apply getParamCountBound.
Qed.

Lemma getKelim Σ Γ mind_body ind ind_body:
  on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body ->
  wf_local Σ Γ ->
  {T & Σ;;;Γ |- getMaxElim (Ast.ind_kelim ind_body) : tSort T}.
Proof.
  intros [] H.
  eexists.
  induction ind_kelim.
  - cbn. apply type_Sort.
    + exact H.
    + admit.
  - cbn in *.
    unfold getMaxElim.
    destruct canElim;cbn.
    + admit.
    + admit.
Admitted. (* Universe *)

Lemma removeArityCount n xs t: (forall x, In x xs -> decl_body x = None) -> n=#|xs| -> remove_arity n (it_mkProd_or_LetIn xs t) = t.
Proof.
  intros F.
  induction xs using rev_ind in n, t, F |- *;cbn;intros H.
  - now rewrite H.
  - pose proof (F x).
    remember x.
    rewrite Heqc.
    rewrite Heqc in H0 at 3.
    destruct x;cbn in H0.
    rewrite H0.
    + unfold it_mkProd_or_LetIn. rewrite_it_mk foldMkProd.
      rewrite H, lengthAppend, add_comm. cbn.
      apply IHxs;trivial.
      intros;apply F,in_or_app. now left.
    + apply in_or_app. right. now left.
Qed.

Lemma replaceUnderItMkProd s t xs: (forall x, In x xs -> decl_body x = None) -> replaceLastProd t (it_mkProd_or_LetIn xs s) = it_mkProd_or_LetIn xs (replaceLastProd t s).
Proof.
  intros H.
  induction xs using rev_ind in H |- *.
  - reflexivity.
  - specialize (H x) as ?.
    destruct x. cbn in H0. rewrite H0.
    + rewrite foldMkProd.
      cbn.
      rewrite foldMkProd.
      rewrite_it_mk foldMkProd.
      f_equal.
      rewrite <- IHxs.
      * cbn. reflexivity.
      * intros. apply H, in_or_app. now left.
    + apply in_or_app. right. now left.
Qed.

Lemma replaceUnderItMkLambda s t xs: (forall x, In x xs -> decl_body x = None) -> replaceLastLambda t (it_mkLambda_or_LetIn xs s) = it_mkLambda_or_LetIn xs (replaceLastLambda t s).
Proof.
  intros H.
  induction xs using rev_ind in H |- *.
  - reflexivity.
  - specialize (H x) as ?.
    destruct x. cbn in H0. rewrite H0.
    + rewrite foldMkLambda.
      cbn.
      rewrite foldMkLambda.
      rewrite_it_mk foldMkLambda.
      f_equal.
      rewrite <- IHxs.
      * cbn. reflexivity.
      * intros. apply H, in_or_app. now left.
    + apply in_or_app. right. now left.
Qed.

Lemma collectProdMkProdGen xs s: (forall x, In x xs -> decl_body x = None) -> collect_prods(it_mkProd_or_LetIn xs s) = rev xs ++ collect_prods s.
Proof.
  intros H.
  induction xs using rev_ind in H |- *;cbn.
  - reflexivity.
  - specialize (H x) as ?.
    destruct x;cbn in *.
    rewrite H0.
    + rewrite foldMkProd, rev_unit.
      cbn. f_equal.
      rewrite IHxs.
      * reflexivity.
      * intros. apply H.
        now apply in_or_app.
    + apply in_or_app;right;now left.
Qed.

Lemma collectProdMkProd xs s: (forall x, In x xs -> decl_body x = None) -> ~isProd s -> collect_prods(it_mkProd_or_LetIn xs s) = rev xs.
Proof.
  intros H F.
  induction xs using rev_ind in H |- *.
  - cbn. destruct s;cbn in *;congruence.
  - specialize (H x) as ?.
    destruct x;cbn in *.
    rewrite H0.
    + rewrite foldMkProd.
      unfold it_mkProd_or_LetIn in IHxs.
      cbn.
      rewrite IHxs.
      * now rewrite rev_unit.
      * intros;apply H,in_or_app;now left.
    + apply in_or_app;right;now left.
Qed.

Lemma replaceLastProdReplaceLastProd s t u: replaceLastProd s (replaceLastProd t u) = replaceLastProd (replaceLastProd s t) u.
Proof.
  induction u;cbn;try reflexivity.
  rewrite_it_mk foldMkProd.
  cbn.
  rewrite_it_mk foldMkProd.
  rewrite_it_mk foldMkProd.
  f_equal.
  unfold replaceLastProd, it_mkProd_or_LetIn in IHu2.
  apply IHu2.
Qed.

Lemma liftCollectProd t n k: rev (lift_context n k (rev (collect_prods t))) = collect_prods (lift n k t).
Proof.
  unfold lift_context, fold_context,mapi.
  do 2 rewrite revRev.
  change (lift n k t) with (lift n (0+k) t).
  remember 0 as a.
  induction t in a, n, k |- *;cbn;trivial.
  - destruct Nat.leb;reflexivity.
  - f_equal.
    apply IHt2.
Qed.

Lemma liftReplaceLastProd s t n k: lift n k (replaceLastProd s t) = replaceLastProd (lift n (count_prods t + k) s) (lift n k t).
Proof.
  unfold replaceLastProd.
  rewrite lift_it_mkProd_or_LetIn.
  unfold count_prods.
  rewrite revLen.
  f_equal.
  now rewrite <- liftCollectProd, revRev.
Qed.

Lemma liftUnderReplaceLambda n k s:
  isLambda(remove_prods (lift n k s))=isLambda(remove_prods s).
Proof.
  intros.
  induction s in n,k |- *;cbn;trivial.
  now destruct Nat.leb.
Qed.

Lemma collectReplace s t: collect_prods(replaceLastProd s t) = collect_prods t ++ collect_prods s.
Proof.
  unfold replaceLastProd.
  rewrite collectProdMkProdGen.
  - now rewrite revRev.
  - intros x H.
    rewrite <- in_rev in H.
    now eapply collectProdVass.
Qed.

Lemma collectNoProd s: ~isProd s -> collect_prods s = [].
Proof.
  destruct s;cbn;congruence.
Qed.

Lemma revCollect s t u na: ~isProd t -> rev(collect_prods(replaceLastProd (tProd na s t) u))=(vass na s)::rev(collect_prods u).
Proof.
  intros H.
  rewrite collectReplace,rev_app_distr. cbn.
  rewrite collectNoProd;trivial.
Qed.

Lemma removeMkProd xs t: (forall x, In x xs -> decl_body x = None) -> remove_prods (it_mkProd_or_LetIn xs t) = remove_prods t.
Proof.
  intros H.
  induction xs in t, H |- *;cbn.
  - reflexivity.
  - rewrite IHxs.
    + specialize (H a). destruct a.
      cbn in *.
      rewrite H.
      * reflexivity.
      * now left.
    + intros. apply H. now right.
Qed.

Lemma mkLambdaCollect s t: it_mkLambda_or_LetIn (rev(collect_lambdas s)) t = replaceLastLambda t s.
Proof.
  induction s in t |- *;cbn;try congruence.
Qed.

Lemma liftMaxElim n k xs: lift n k (getMaxElim xs) = getMaxElim xs.
Proof.
  maxElimProof.
Qed.

Lemma collectLambdaMaxElim xs: collect_lambdas (getMaxElim xs) = [].
Proof.
  maxElimProof.
Qed.

Lemma collectProdMaxElim xs: collect_prods (getMaxElim xs) = [].
Proof.
  maxElimProof.
Qed.

Lemma removeProdMaxElim xs: remove_prods (getMaxElim xs) = getMaxElim xs.
Proof.
  maxElimProof.
Qed.

Lemma replaceLambdaMaxElim s xs: replaceLastLambda s (getMaxElim xs) = s.
Proof.
  maxElimProof.
Qed.

Lemma replaceProdMaxElim s xs: replaceLastProd s (getMaxElim xs) = s.
Proof.
  maxElimProof.
Qed.

Lemma noProdMaxElim xs: ~ isProd (getMaxElim xs).
Proof.
  maxElimProof.
Qed.

Lemma noLambdaMaxElim xs: ~ isLambda (getMaxElim xs).
Proof.
  maxElimProof.
Qed.

Lemma collectNoLambda t: ~isLambda t -> collect_lambdas t = [].
Proof.
  destruct t;cbn;congruence.
Qed.

Lemma collectLambdaMkLambda xs t: (forall x, In x xs -> decl_body x = None) -> collect_lambdas (it_mkLambda_or_LetIn (rev xs) t) = xs++collect_lambdas t.
Proof.
  intros.
  induction xs using rev_ind in t, H |- *;cbn.
  - destruct t;cbn in *;congruence.
  - rewrite rev_unit.
    rewrite IHxs.
    + specialize (H x).
      destruct x;cbn in *.
      rewrite H.
      * cbn. now rewrite <- app_assoc.
      * apply in_or_app. right. now left.
    + intros. apply H, in_or_app. now left.
Qed.

Lemma collectLift n k s: collect_prods (lift n k s) = rev(lift_context n k (rev(collect_prods s))).
Proof.
  induction s in k |- *;cbn;try congruence.
  - destruct Nat.leb;reflexivity.
  - rewrite revRev.
    rewrite rev_unit.
    cbn.
    unfold map_decl,vass.
    f_equal.
    rewrite IHs2.
    unfold lift_context, fold_context, mapi.
    do 2 rewrite revRev.
    rewrite mapi_rec_Sk.
    unfold map_decl.
    clear.
    remember 0 as a.
    clear Heqa.
    induction (collect_prods s2) in a |- *.
    + reflexivity.
    + cbn. f_equal.
      * f_equal.
        -- f_equal. f_equal. now rewrite <- plus_n_Sm.
        -- f_equal. now rewrite <- plus_n_Sm.
      * apply IHl.
Qed.

End CustomFunction.




Section AuxLemma.

Lemma createReturnNone b ind univ mind n nf: createElim b ind univ mind n nf = None <-> nth_error (ind_bodies mind) (inductive_ind ind) = None.
Proof.
  unfold createElim;destruct nth_error;split;congruence.
Qed.

Corollary createSome b ind univ mind n nf t na: createElim b ind univ mind n nf = Some (t,na) -> { indB & nth_error (ind_bodies mind) (inductive_ind ind) = Some indB}.
Proof.
  unfold createElim;destruct nth_error eqn: F.
  - now exists o.
  - congruence.
Qed.

Lemma onIndDeclInd Σ mind_body ind ind_body:
  on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body ->
  declared_inductive Σ mind_body ind ind_body.
Proof.
  intros [].
  unfold declared_inductive.
  cbn in *. destruct onArity.
Admitted. (* Basic *)

Lemma onIndMutInd Σ mind_body ind ind_body:
  on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body ->
  declared_minductive Σ (inductive_mind ind) mind_body.
Proof.
  now intros []%onIndDeclInd.
Qed.

Lemma onIndNth Σ mind_body ind ind_body:
  on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body ->
  nth_error (ind_bodies mind_body) (inductive_ind ind) = Some ind_body.
Proof.
  now intros []%onIndDeclInd.
Qed.

Lemma getOndIndBody (Σ:global_env_ext) mind_body ind ind_body:
     declared_inductive Σ mind_body ind ind_body ->
     on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body (* obtain from on_inductive *)
.
Proof.
  intros H.
  inv H.
  eapply Build_on_ind_body.
  - admit.
  - cbn.
    unfold declared_minductive in H0.
    destruct Σ.
    cbn in H0.
    induction g;cbn in H0.
    + discriminate.
    + destruct ident_eq eqn: H2.
      * injection H0 as H3.
        destruct a. cbn in *.
        subst g0. admit.
      * apply IHg in H0 as [].
        exists x.
    (* apply weakening_typing. *)
        admit.
  - unfold on_constructors.
    (* instantiate by hand *)
    induction ind_ctors.
    2: {
      constructor.
      - unfold on_constructor.
        split.
        + cbn. admit.
        + admit.
      - admit.
    }
    + admit.
Admitted. (* Basic *)

End AuxLemma.

Section Tmp.

Lemma replaceMap s t: ~isProd s -> ~isLambda (remove_prods t) -> replaceLastLambda s (mapProdToLambda t) = mapProdToLambda (replaceLastProd s t).
Proof.
  intros.
  unfold mapProdToLambda.
  rewrite collectReplace,collectNoProd with (s:=s),app_nil_r;trivial.
  rewrite replaceUnderItMkLambda.
  2: intros x F;apply in_rev in F; now eapply collectProdVass.
  f_equal.
  rewrite removeArityProdCount.
  assert(#|collect_prods t| = count_prods (replaceLastProd s t)) as ->.
  {
    unfold replaceLastProd,count_prods.
    rewrite collectProdMkProd;trivial.
    2: intros x F;apply in_rev in F; now eapply collectProdVass.
    now do 2 rewrite revLen.
  }
  assert(replaceLastLambda s (remove_prods t) = s) as ->.
  {
    destruct (remove_prods t);cbn in *;congruence.
  }
  rewrite removeArityProdCount.
  rewrite removeReplaceProd.
  destruct s;cbn in *;congruence.
Qed.

Lemma replaceOneProd s n t1 t2: replaceLastProd s (tProd n t1 t2) = tProd n t1 (replaceLastProd s t2).
Proof.
  cbn.
  rewrite fold_left_app;cbn.
  reflexivity.
Qed.

Lemma mapMk xs t: (forall x, In x xs -> decl_body x = None) -> mapProdToLambda (it_mkProd_or_LetIn xs t) = it_mkLambda_or_LetIn xs (mapProdToLambda t).
Proof.
  induction xs using rev_elim.
  - reflexivity.
  - rewrite <- mapAgreement in *.
    intros H.
    specialize (H x) as H2.
    destruct x.
    cbn in H2.
    rewrite H2.
    2: {
      apply in_or_app.
      right.
      now left.
    }
    rewrite foldMkProd.
    rewrite foldMkLambda.
    cbn.
    f_equal.
    apply IHxs.
    intros. apply H, in_or_app.
    now left.
Qed.

Lemma liftingInVass xs:
(forall x : Ast.context_decl,
In x xs -> Ast.decl_body x = None) ->
  forall n m,
forall x : Ast.context_decl,
  In x (lift_context n m xs) -> Ast.decl_body x = None.
Proof.
  induction xs;intros.
  - cbn in H0. contradict H0.
  - cbn in H0.
    rewrite mapi_rec_app in H0.
    cbn in H0.
    rewrite rev_unit in H0.
    destruct H0.
    + specialize (H a).
      subst x.
      destruct a.
      cbn in H.
      rewrite H.
      2: now left.
      reflexivity.
    + revert H0.
      apply IHxs.
      intros.
      apply H.
      now right.
Qed.

Inductive typingList Σ Γ : list context_decl -> list universe -> Type :=
| typeNil : typingList Σ Γ [] []
| typeCons x t xs ts: Σ;;;Γ |- decl_type x : tSort t -> typingList Σ (x::Γ) xs ts -> typingList Σ Γ (x::xs) (t::ts).

Lemma typeSnoc Σ Γ x t xs ts: Σ;;;Γ,,,(rev xs) |- decl_type x : tSort t -> typingList Σ Γ xs ts -> typingList Σ Γ (xs++[x]) (ts++[t]).
Proof.
  induction xs in Γ, ts |- *;intros.
  - cbn in *.
    inv X0.
    constructor.
    + apply X.
    + constructor.
  - inv X0.
    cbn.
    constructor.
    + apply X1.
    + apply IHxs.
      * unfold app_context in *.
        cbn in X.
        rewrite <- app_assoc in X.
        apply X.
      * apply X2.
Qed.

Lemma typeSnocInv Σ Γ x xs ts:
  typingList Σ Γ (xs ++ [x]) ts ->
  { ts' & {t &
           ts=ts'++[t] × typingList Σ Γ xs ts' × Σ;;;Γ,,,(rev xs) |- decl_type x : tSort t
  }}.
Proof.
  intros.
Admitted. (* Basic *)

Lemma typingListOffset Σ Γ Γ0 xs t n:
  typingList Σ Γ xs t -> n=#|Γ0| ->
  typingList Σ (Γ,,,Γ0) (lift_context n 0 xs) t.
Proof.
  intros.
Admitted. (* Basic *)


(* maybe typingList -> type_local_ctx *)
(* type_local_ctx
   all vass in Delta
   under Rest Delta0
   is t typed with tSort u
 *)
Lemma type_it_mkProd_or_LetIn Σ Γ xs t ts s2:
  (forall x, In x xs -> decl_body x = None) ->
  typingList Σ Γ xs ts ->
  Σ;;;Γ,,,xs |- t : tSort s2 ->
  Σ;;;Γ |- it_mkProd_or_LetIn xs t : tSort (fold_left Universe.sort_of_product ts s2).
Proof.
  induction xs using rev_elim;intros EmptyBody Typing InnerType.
  - cbn in *. inv Typing.
    cbn. apply InnerType.
  - specialize (EmptyBody x) as H.
    destruct x;cbn in H.
    rewrite H in *.
    2-5: apply in_or_app; right; now left.
    clear H.
    rewrite foldMkProd.
    apply typeSnocInv in Typing.
    destruct Typing as (ts'&t0&->&?&?).
    rewrite fold_left_app.
    cbn.
    apply type_Prod.
    + cbn in t2. admit.
    + admit.
Admitted. (* Basic *)

Lemma fixGuardAxiom m: fix_guard m.
Proof.
Admitted. (* admit *)

Lemma wfParamsAux:
forall
(Σ : TemplateEnvironment.global_env_ext)
(Γ : TemplateEnvironment.context)
(Hwf : wf_local Σ Γ)
(ind : inductive)
(mind_body : TemplateEnvironment.mutual_inductive_body)
(onInd : on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body)
(onParams : on_context (lift_typing typing) Σ (TemplateEnvironment.ind_params mind_body)),
  wf_local_rel Σ Γ (ind_params mind_body).
Proof.
  intros.
  pose proof(indParamVass _ _ _ onInd).
  remember (ind_params mind_body) as params.
  clear ind Heqparams onInd.
  destruct params as [|a params].
  - constructor.
  - specialize (H a) as G.
    inversion onParams;subst;clear onParams;cbn in *.
    + apply wf_local_rel_abs.
      * apply wfLocalToRel.
        -- apply Hwf.
        -- apply X.
      * destruct X0.
        eexists.
        apply typingApp. (* use weakening *)
        apply t1.
    + discriminate G. now left.
Qed.

Lemma onSndId {X Y} (a:X×Y): on_snd (fun x => x) a = a.
Proof.
  destruct a.
  reflexivity.
Qed.

Lemma mapId {X} (xs:list X): map (fun x => x) xs = xs.
Proof.
  induction xs;cbn;trivial.
  now f_equal.
Qed.

Lemma mapSndAdd0 {X} (xs:list (X×nat)):
  map (on_snd (Init.Nat.add 0)) xs = xs.
Proof.
  induction xs;cbn.
  - reflexivity.
  - f_equal.
    + now destruct a.
    + apply IHxs.
Qed.

Lemma mapi_rec_len {X Y} (f:nat->X->Y) xs n: #|mapi_rec f xs n| = #|xs|.
Proof.
  induction xs in n |- *;cbn.
  - reflexivity.
  - f_equal. apply IHxs.
Qed.

Lemma liftContextSucc n k xs: lift_context 1 k (lift_context n k xs) = lift_context (S n) k xs.
Proof.
  induction xs in k |- *.
  - reflexivity.
  - repeat (cbn; rewrite mapi_rec_app, rev_unit).
    f_equal.
    + destruct a;cbn.
      destruct decl_body;cbn.
      * unfold map_decl;cbn.
        f_equal.
        -- f_equal.
           rewrite simpl_lift.
           ++ reflexivity.
           ++ rewrite revRev,mapi_rec_len. lia.
           ++ rewrite revRev,mapi_rec_len. lia.
        -- rewrite simpl_lift.
           ++ reflexivity.
           ++ rewrite revRev,mapi_rec_len. lia.
           ++ rewrite revRev,mapi_rec_len. lia.
      * unfold map_decl;cbn.
        f_equal.
        rewrite simpl_lift.
        -- reflexivity.
        -- rewrite revRev.
           rewrite mapi_rec_len, revLen. lia.
        -- rewrite revRev, mapi_rec_len. lia.
    + unfold lift_context, fold_context in IHxs.
      apply IHxs.
Qed.

Lemma liftContextSum n m k xs: lift_context n k (lift_context m k xs) = lift_context (n+m) k xs.
Proof.
  induction n.
  - now rewrite lift0_context.
  - cbn. rewrite <- liftContextSucc.
    rewrite IHn, liftContextSucc.
    reflexivity.
Qed.

Lemma lift_context_len n k xs: #| lift_context n k xs | = #| xs |.
Proof.
  unfold lift_context,fold_context, mapi;
    rewrite revLen, mapi_rec_len, revLen; lia.
Qed.

Lemma subst_context_len n k xs: #| subst_context n k xs | = #| xs |.
Proof.
  unfold subst_context,fold_context, mapi;
    rewrite revLen, mapi_rec_len, revLen; lia.
Qed.

(* useful to avoid collect_prods condition *)
(* maybe strenghen ~isProd to remove_prods s = t *)
Lemma collect_prods2 s: {xs & { t & it_mkProd_or_LetIn xs t = s /\ ~isProd t}}.
Proof.
  induction s eqn:H in s |- *.
  all: try (exists []; exists s; split; [apply H | subst;cbn;congruence]).
  specialize (IHt0_2 t0_2).
  destruct IHt0_2 as (xs&t&H1&H2);trivial.
  exists (xs ++ [vass na  t0_1]). exists t. split.
  - cbn.
    rewrite foldMkProd.
    f_equal.
    apply H1.
  - apply H2.
Qed.

Lemma mapTypeEraseAux n m:
  n<m ->
 map (lift 1 m)
    (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) n) =
 nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) n.
Proof.
  induction n in m |- *.
  - reflexivity.
  - cbn. intros.
    assert ( m <=? n = false) as ->.
    {
      apply leb_correct_conv.
      lia.
    }
    f_equal.
    apply IHn.
    lia.
Qed.

Lemma lift_it_mkLambda_or_LetIn n k ctx t :
  lift n k (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (lift_context n k ctx) (lift n (#|ctx| + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (#|ctx| + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma subst_it_mkProd_or_LetIn xs k ctx t :
  subst xs k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_context xs k ctx) (subst xs (#|ctx| + k) t).
Proof.
  induction ctx in xs, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc xs k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (subst_context_snoc xs k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma replaceLastProdNotProd s t:
  ~ isProd t -> replaceLastProd s t = s.
Proof.
  intros.
  destruct t;cbn in *;congruence.
Qed.

Lemma replaceLastLambdaNoLambda s t:
  ~ isLambda t -> replaceLastLambda s t = s.
Proof.
  intros.
  destruct t;cbn in *;congruence.
Qed.

Lemma quantifyCasesLen b ctors paramCount ind univ:
  #|quantifyCases b ctors paramCount ind univ| = #|ctors|.
Proof.
  unfold quantifyCases,mapi.
  now rewrite mapi_rec_len.
Qed.


Lemma mapLen {X Y} (f:X->Y) xs: #|map f xs| = #|xs|.
Proof.
  induction xs.
  - reflexivity.
  - cbn. now rewrite IHxs.
Qed.

Lemma typingSpineLifting Σ Γ xs ys x a t:
  (* wf_local Σ (Γ ,,, ys ,,, lift_context #|ys| 0 xs) -> *)
  typing_spine Σ (Γ ,,, xs) a x t -> forall n, #|ys| = n ->
  typing_spine Σ (Γ ,,, ys ,,, (lift_context n 0 xs)) (lift n #|xs| a) (map (lift n #|xs|) x) (lift n #|xs| t).
Proof.
  intros.
  subst n.

  assert(wf Σ.1).
  admit.
 assert(wf_local Σ (Γ ,,, xs)).
  admit.
 assert(wf_local Σ (Γ ,,, ys ,,, lift_context #|ys| 0 xs)).
  admit.

  remember (Γ,,,xs) as Γ'.
  induction X.
  - constructor.
  - subst Γ0.
    Print typing_spine.
    eapply type_spine_cons with (na0:=na)
                                (A0:=lift #|ys| #|xs| A)
                                (B0:=lift #|ys| (S #|xs|) B)
                                (s0:=s).
    Check weakening.
    Check weakening_typing.
    3: {
      apply weakening_typing.
      1-3: assumption.
      apply t1.
    }
    3: {
      rewrite distr_lift_subst in IHX.
      cbn in IHX.
      now apply IHX.
    }
    1: {
      match goal with
        |- _ ;;; _ |- ?Body : ?Typ =>
        change Body with (lift #|ys| #|xs| (tProd na A B));
        change Typ with (lift #|ys| #|xs| (tSort s))
      end.
      apply weakening_typing.
      1-3: assumption.
      apply t0.
    }
    1: {
      Locate "_ ;;; _ |- _ : _".
      Locate "_ ;;; _ |- _ <= _".
      Search cumul.
      Print cumul.
      match goal with
        |- _ ;;; _ |- ?Body <= ?Typ =>
        change Typ with (lift #|ys| #|xs| (tProd na A B))
      end.
      clear IHX X t1 t0.
      remember (tProd na A B) as prod.
      clear Heqprod.
      induction c.
      - constructor.
        now apply lift_leq_term.
      - econstructor 2.
        2: now apply IHc.
        apply weakening_red1.
        2: apply r.
        1: assumption.
      - econstructor 3.
        1: apply IHc.
        apply weakening_red1.
        2: apply r.
        1: assumption.
    }
Admitted. (* Basic *)

Lemma appLen {X} (xs ys:list X): #|xs ++ ys| = #|xs| + #|ys|.
Proof.
  induction xs in ys |- *.
  - reflexivity.
  - cbn. now rewrite IHxs.
Qed.


Lemma lift_wf_local_rel Σ Γ Γ' n k : wf Σ.1 -> wf_local_rel Σ Γ Γ' -> lift_context n k Γ' = Γ'.
Proof.
  intros wfΣ.
  induction 1; auto; unfold lift_context, snoc;
  rewrite fold_context_snoc0; auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl. unfold vass. simpl. f_equal.
  destruct t0.
  eapply typed_liftn; eauto. cbn. lia. unfold vdef.
  (* f_equal. f_equal. eapply typed_liftn; eauto. lia. *)
  (* destruct t0. *)
  (* eapply typed_liftn in t0 as [Ht HT]; eauto. lia. *)
Admitted. (* Basic *)

Lemma weakeningWfLocalRel Σ Γ xs t n:
  wf_local Σ Γ ->
  wf_local_rel Σ Γ xs ->
  wf_local_rel Σ Γ t ->
  n = #|xs| -> wf_local_rel Σ (Γ,,, xs) (lift_context n 0 t).
Proof.
  intros.
  subst n.
  apply wfLocalToRel.
  - apply wf_local_app_inv;assumption.
  - admit.
Admitted. (* Basic *)

Lemma appCons {X} xs (y:X) ys: xs ++ [y] ++ ys = xs ++ y::ys.
Proof.
  reflexivity.
Qed.

Lemma appConsNilFront {X} (y:X) ys: y::ys = [y] ++ ys.
Proof.
  reflexivity.
Qed.

Lemma consMin {X} (x:X) xs ys: x::(xs++ys) = (x::xs)++ys.
Proof.
  reflexivity.
Qed.

Lemma substInstanceConstrMkProd univ xs t:
  (forall x, In x xs -> decl_body x = None) ->
  subst_instance_constr univ (it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map (fun x => {| decl_body := decl_body x; decl_type := subst_instance_constr univ (decl_type x); decl_name := decl_name x |}) xs) (subst_instance_constr univ t).
Proof.
  intros.
  induction xs using rev_elim.
  - reflexivity.
  - specialize (H x) as H2.
    destruct x.
    rewrite map_app.
    cbn [map].
    cbn in H2.
    rewrite H2.
    2: {
      apply in_or_app.
      right. now left.
    }
    do 2 rewrite foldMkProd.
    rewrite <- IHxs.
    2: {
      intros.
      apply H, in_or_app.
      now left.
    }
    reflexivity.
Qed.


    Print red.
    Print red1.
    Search "eta".
    Print cumul_eta_l.
    Print cumul_eta_r.
    Print eta_expands.
    Print stack.

(* Variable eta_expands. *)

Lemma cumul_eta_r Σ Γ : forall t u v : term, Σ;;; Γ |- t <= v ->
                                              (* eta_expands u v -> *)
                                              Σ;;; Γ |- t <= u.
Proof.
Admitted. (* Done *)

Lemma leq_term_refl:
  forall (H : config.checker_flags) (φ : constraints), CRelationClasses.Reflexive (PCUICEquality.leq_term φ).
Proof.
Admitted. (* Done *)

Print type_Case.

Lemma etaConvType Σ Γ t T na to ty:
  Σ;;;Γ |- t : T ->
  Σ;;;Γ |- to : ty ->
  Σ;;;Γ |- t : tApp (tLambda na ty T) [to].
Proof.
  intros.
  apply type_Conv with (A:=T).
  - apply X.
  - right. admit.
  - Locate "<=".
    Print cumul.
    Print cumul_eta_r.
    apply cumul_eta_r with (v:=T).
    constructor.
    Print leq_term.
    admit.
Admitted. (* Basic *)

Lemma etaConvTypeInv Σ Γ t T na to ty:
  Σ;;;Γ |- to : ty ->
  Σ;;;Γ |- t : tApp (tLambda na ty T) [to] ->
  Σ;;;Γ |- t : T.
Proof.
Admitted. (* Basic *)

Lemma etaConvTypeGen Σ Γ t T xs ys:
  (forall x, In x xs -> decl_body x = None) ->
  All2 (fun x y => Σ;;;Γ |- y : (decl_type x)) xs ys ->
  Σ;;;Γ |- t : mkApps (it_mkLambda_or_LetIn xs T) (rev ys) ->
  Σ;;;Γ |- t : T.
  (* Σ;;;Γ |- to : ty -> *)
Proof.
  intros.
  induction X in t, T, X0, H |- *.
  - cbn in X0. apply X0.
  - specialize (H x) as H2.
    destruct x.
    cbn in H2.
    rewrite H2 in X0.
    2: {
      now left.
    }
    cbn in X0.
Admitted. (* Basic *)

Lemma mapExt {X Y:Type} (f g:X->Y) xs: (forall x, f x = g x) -> map f xs = map g xs.
Proof.
  intros.
  induction xs.
  - reflexivity.
  - cbn. now rewrite IHxs, H.
Qed.

Lemma mapiExt {X Y:Type} (f g:nat->X->Y) xs: (forall i x, f i x = g i x) -> mapi f xs = mapi g xs.
Proof.
  intros.
  unfold mapi.
  remember 0.
  clear Heqn.
  induction xs in n |- *.
  - reflexivity.
  - cbn. now rewrite IHxs, H.
Qed.

Lemma natRecExt {Y:Set} f g (a:Y) m:
  (forall n a, f n a = g n a) ->
  nat_rec (fun _ => Y) a f m = nat_rec (fun _ => Y) a g m.
Proof.
  intros.
  induction m.
  - reflexivity.
  - cbn.
    now rewrite IHm, H.
Qed.

Lemma AllSpecial {X:Type} (P Q:X->Type) xs:
  (forall x, P x -> Q x) -> All (fun x => P x -> Q x) xs.
Proof.
Admitted. (* Basic *)

Lemma wfLocalRelTypingList Σ Γ xs:
  wf_local_rel Σ Γ xs -> { ts & typingList Σ Γ xs ts}.
Proof.
  intros H.
  induction xs as [|[? [] ?] ?] in Γ, H |- *.
  - eexists. constructor.
  - inv H.
    cbn in *.
    destruct X0.
    eexists.
    constructor.
    + cbn.
      (* need reversion somewhere *)
      (* apply t1. *)
Admitted. (* Basic *)


Definition allVass xs := forall x, In x xs -> decl_body x = None.

Definition mkRel {X} (xs:list X) :=
  nat_rec (fun _ => list term) [] (fun n a => tRel n :: a) #|xs|.


Lemma natRecAppGen {X} (xs ys:list X) l:
  nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (l+n) :: a) (#|xs++ys|) =
  nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (l+n + #|ys|) :: a) #|xs| ++
  nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (l+n) :: a) #|ys|.
Proof.
  induction xs.
  - reflexivity.
  - cbn. rewrite appLen at 1.
    f_equal.
    1: f_equal;lia.
    apply IHxs.
Qed.

(* Lemma natRecApp: *)
(*   nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (n + l) :: a) (#|xs| + 1) = *)
(*   nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (n + S l) :: a) #|xs| ++ *)
(*   [tRel (#|xs| + S l - (#|xs| + 0) - 1)] *)

Lemma mapiNatRecGen {X} (xs:list X) l:
  nat_rec (fun _ => list term) [] (fun n a => tRel (l+n) :: a) #|xs| =
  mapi (fun i _ => tRel (l+#|xs| -i-1)) xs.
Proof.
  induction xs in l |- * using rev_ind.
  - reflexivity.
  - rewrite mapi_app.
    cbn.
    rewrite natRecAppGen.
    rewrite appLen.
    replace (l + (#|xs| + #|[x]|)) with ((l+#|[x]|) + #|xs|) by lia.
    rewrite <- IHxs.
    cbn.
    f_equal.
    + apply natRecExt.
      intros.
      do 2 f_equal.
      lia.
    + do 2 f_equal.
      lia.
Qed.


Lemma mapiNatRec {X} (xs:list X):
  mkRel xs =
  mapi (fun i _ => tRel (#|xs| -i-1)) xs.
Proof.
  unfold mkRel.
  change (#|xs|) with (0+#|xs|).
  rewrite <- mapiNatRecGen.
  cbn.
  apply natRecExt.
  reflexivity.
Qed.

(* Compute (mkRel [1;2;3]). *)

Lemma liftMkRel {X} (xs:list X) n k:
  k >= #|xs| ->
  map (lift n k) (mkRel xs) = mkRel xs.
Proof.
  intros H.
  induction xs in k, H |- *.
  - reflexivity.
  - cbn.
    assert(k <=? #|xs| = false) as ->.
    {
      apply leb_correct_conv.
      cbn in H.
      lia.
    }
    f_equal.
    rewrite IHxs.
    + reflexivity.
    + cbn in H.
      lia.
Qed.

Instance typingSpineReflexive:
   forall Re Rle : Relation_Definitions.relation universe,
   RelationClasses.Reflexive Re ->
   RelationClasses.Reflexive Rle -> CRelationClasses.Reflexive (eq_term_upto_univ Re Rle).
Proof.
Admitted. (* done *)

(* Lemma typingSpineProdApp Σ Γ xs t: *)
(*       typing_spine Σ (Γ,,,xs) *)
(*       (it_mkProd_or_LetIn (rev xs) t) *)
(*       (mkRel xs) *)
(*       t. *)
(* Proof. *)
(*   cbn. *)
(*   induction xs. *)
(*   - constructor. *)
(*   - destruct a as [? [] ?]. *)
(*     + admit. *)
(*     + rewrite foldMkProd. *)
(*       cbn. *)
(*       econstructor. *)
(*       2: { *)
(*         constructor. *)
(*         constructor. *)
(*         Search "eq_term_upto_univ". *)
(*         - reflexivity. *)
(*         - reflexivity. *)
(*       } *)
(*       2: { *)
(*         cbn. *)
(*         admit. *)
(*       } *)
(*       2: { *)
(*         admit. *)
(*       } *)
(*       admit. *)
(* Admitted. (* Basic *) *)


Lemma typingSpineProdApp Σ Γ xs a t:
      typing_spine Σ (Γ,,,xs)
      t
      []
      (tSort a) ->
      typing_spine Σ (Γ,,,xs)
      (it_mkProd_or_LetIn xs t)
      (mkRel xs)
      (tSort a).
Proof.
  cbn.
  intros H.
  (* inversion H. *)
  (* inv H. *)
Admitted. (* Basic *)

    (* mkRel with numbers and output number list *)
Lemma mkRelApp {X} (xs ys:list X):
  mkRel (xs++ys) =
  mapi (fun (i : nat) _ => tRel (#|xs| + (#|ys| - i - 1)))
       ys ++
       mkRel xs.
Proof.
  rewrite mapiNatRec.
  rewrite mapiNatRec.
  rewrite mapi_app.
  rewrite appLen.
  replace (fun n (_:X) => tRel (#|xs| + #|ys| - (#|xs| + n) - 1)) with
      (fun n (_:X) => tRel (#|ys| - n - 1)).
  2: admit.
  (* wrong order? *)

  (* induction ys. *)
  (* - cbn. admit. *)
  (* - rewrite mapiNatRec. *)
  (*   rewrite mapi_app. *)
  (*   cbn. *)
Admitted. (* Basic *)

Lemma onContextInv typing Σ x xs:
  on_context typing Σ (x::xs) ->
  on_context typing Σ xs.
Proof.
  unfold on_context.
  intros H.
  inv H;assumption.
Qed.

Lemma replaceOffsetUnderItProd f n xs t:
  replaceLastOffset f n (it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn xs (replaceLastOffset f (n+#|xs|) t).
Proof.
  induction xs in t,n |- *.
  - cbn. rewrite add_0_r. reflexivity.
  - cbn.
    unfold it_mkProd_or_LetIn in IHxs.
    rewrite IHxs.
    f_equal.
    destruct a as [? [] ?];cbn;now rewrite plus_n_Sm.
Qed.

Lemma succLen {X} (x:X) xs:
  #|x::xs| = S #|xs|.
Proof.
  reflexivity.
Qed.

Lemma optionMapNested {X Y Z} (f:Y->Z) (g:X->Y) x:
  option_map f (option_map g x) =
  option_map (fun a => f(g a)) x.
Proof.
  now destruct x.
Qed.


Lemma mapDeclNested f g a:
  map_decl f (map_decl g a) =
  map_decl (fun x => f(g x)) a.
Proof.
  destruct a.
  unfold map_decl.
  cbn.
  f_equal.
  apply optionMapNested.
Qed.

Lemma mapiNested {X Y Z} (f :nat->Y->Z) (g:nat->X->Y) xs:
  mapi f (mapi g xs) =
  mapi (fun n a => f n (g n a)) xs.
Proof.
  induction xs using rev_ind.
  - reflexivity.
  - do 3 rewrite mapi_app.
    rewrite IHxs.
    f_equal.
    unfold mapi.
    now rewrite mapi_rec_len.
Qed.

Lemma mapiRecNested {X Y Z} (f :nat->Y->Z) (g:nat->X->Y) xs m:
  mapi_rec f (mapi_rec g xs m) m =
  mapi_rec (fun n a => f n (g n a)) xs m.
Proof.
  induction xs using rev_ind.
  - reflexivity.
  - do 3 rewrite mapi_rec_app.
    rewrite IHxs.
    f_equal.
    now rewrite mapi_rec_len.
Qed.

Lemma mapiLiftContext n m xs:
  rev
    (mapi (fun k decl => map_decl (lift n k) decl)
          (rev (lift_context m 0 xs))) =
     lift_context (n+m) 0 xs.
Proof.
  induction xs.
  - reflexivity.
  - cbn. rewrite revRev.
    f_equal.
    do 3 rewrite mapi_rec_app.
    cbn.
    rewrite mapi_rec_len, revLen.
    f_equal.
    + rewrite mapiRecNested.
      clear IHxs.
      induction (rev xs) using rev_ind;trivial.
      do 2 rewrite mapi_rec_app.
      cbn.
      rewrite IHl.
      do 2 f_equal.
      rewrite mapDeclNested.
      destruct x as [? [] ?];
      unfold map_decl;cbn;f_equal;now rewrite simpl_lift.
    + rewrite mapDeclNested.
      f_equal.
      do 2 rewrite add_0_r.
      destruct a as [? [] ?];
      unfold map_decl;
      cbn;
      f_equal;now rewrite simpl_lift.
Qed.



Lemma skipnApp {X} (xs:list X) ys:
  skipn #|xs| (xs++ys) = ys.
Proof.
  induction xs.
  - reflexivity.
  - cbn.
    unfold skipn in *.
    apply IHxs.
Qed.

Lemma it_mkProd_inv Σ Γ xs t u:
  (forall x, In x xs -> decl_body x = None) ->
  Σ;;;Γ |- it_mkProd_or_LetIn xs t : tSort u ->
  Σ;;;Γ,,,xs |- t : tSort u.
Proof.
  intros H.
  induction xs using rev_elim.
  - trivial.
  - specialize (H x) as H2.
    destruct x.
    cbn in H2.
    rewrite H2.
    2: {
      apply in_or_app.
      right. now left.
    }
    rewrite foldMkProd.
    intros.
    (* apply IHxs in X. *)
Admitted. (* Basic *)

Lemma optMonadEq {X Y} e1 (f:X->Y) a y:
  e1 = Some y -> f y = a ->
  (x <- e1;;Some (f x)) = Some a.
Proof.
  intros.
  rewrite H.
  cbn.
  now rewrite H0.
Qed.

Lemma optMonadEq2 {X Y Z} (e1:option X) (f:X->option Y) (g:Y->Z) a b c:
  e1 = Some a ->
  f a = Some b ->
  g b = c ->
  (x <- e1;;y <- f x;;Some (g y)) = Some c.
Proof.
  intros.
  rewrite H;cbn.
  rewrite H0;cbn.
  now rewrite H1.
Qed.

Lemma instParamsSubstSimpl params pars s xs ty:
  (forall x, In x params -> decl_body x = None) ->
  (forall x, In x xs -> decl_body x = None) ->
  #|params| = #|pars| ->
  #|params| = #|xs| ->
  instantiate_params_subst params pars s (it_mkProd_or_LetIn xs ty) = Some (rev pars ++ s, ty).
Proof.
  intros.
  induction params in H, H0, H1, H2, xs, pars, s, ty |- *.
  - cbn.
    destruct pars, xs;try inv H1;try inv H2.
    reflexivity.
  - cbn.
    specialize (H a) as H3.
    rewrite H3.
    2: {
      now left.
    }
    destruct pars;try inversion H1.
    destruct xs using rev_ind;try inversion H2.
    specialize (H0 x) as H4.
    destruct x.
    cbn in H4.
    rewrite H4.
    2: {
      apply in_or_app.
      right.
      now left.
    }
    rewrite foldMkProd.
    rewrite IHparams.
    + cbn.
      rewrite <- appCons.
      now rewrite app_assoc.
    + intros.
      apply H.
      now right.
    + intros.
      apply H0.
      apply in_or_app.
      now left.
    + apply H5.
    + rewrite appLen, plus_comm in H2.
      now inversion H2.
Qed.

Lemma substInstParamVass mind_body ind Σ univ:
  on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body ->
  forall x : context_decl, In x (subst_instance_context univ (ind_params mind_body)) -> decl_body x = None.
Proof.
  intros.
  unfold subst_instance_context, map_context in H.
  apply in_map_iff in H as [? []].
  subst x.
  eapply indParamVass in H0;try eassumption.
  destruct x0.
  cbn in *.
  now rewrite H0.
Qed.

Check in_map_iff.

Lemma in_mapi:
  forall (A B : Type) (f : nat -> A -> B) (l : list A) (y : B), In y (mapi f l) -> (exists (i:nat) (x:A), f i x = y /\ In x l).
Proof.
  intros.
  induction l using rev_ind.
  - cbn in H. contradict H.
  - rewrite mapi_app in H.
    apply in_app_or in H as [].
    + apply IHl in H as (i&z&H1&H2).
      do 2 eexists. split.
      * apply H1.
      * apply in_or_app. now left.
    + destruct H.
      * do 2 eexists. split.
        -- apply H.
        -- apply in_or_app. right.
           now left.
      * cbn in H.
        contradict H.
Qed.

Lemma substContextSubstInstParamVass mind_body ind Σ univ:
  on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body ->
  forall x : context_decl,
  In x
    (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body)) 0
       (subst_instance_context univ (TemplateEnvironment.ind_params mind_body))) -> decl_body x = None.
Proof.
  intros.
  unfold subst_context, fold_context in H.
  rewrite <- in_rev in H.
  unfold subst_instance_context, map_context in H.
  apply in_mapi in H as (i&y&H1&H).
  subst x.
  rewrite <- in_rev in H.
  apply in_map_iff in H as [? []].
  subst y.
  eapply indParamVass in H0;try eassumption.
  destruct x.
  cbn in *.
  now rewrite H0.
Qed.


Lemma destAritySimpl Γ xs t:
  destArity Γ (it_mkProd_or_LetIn xs t) = destArity (Γ,,,xs) t.
Proof.
  unfold app_context.
  induction xs in Γ, t |- *.
  - reflexivity.
  - cbn.
    rewrite IHxs.
    destruct a as [? [] ?];cbn;
      unfold snoc;reflexivity.
Qed.

Lemma extractOption {X} (o:option X):
  {a & o = Some a} -> X.
Proof.
  intros H.
  now destruct H.
Defined.

Print map_option_out.
Lemma mapOptionOutApp {X} (xs ys:list X) ox oy:
  map_option_out ox = Some xs ->
  map_option_out oy = Some ys ->
  map_option_out (ox++oy) = Some (xs++ys).
Proof.
  intros.
  induction ox in xs, ys, H, H0 |- *.
  - inv H. cbn. apply H0.
  - cbn in *.
    destruct a;try congruence.
    destruct xs.
    1: {
      destruct map_option_out;congruence.
    }
    cbn in *.
    destruct map_option_out.
    2: congruence.
    injection H as -> ->.
    rewrite IHox with (xs0:=xs) (ys:=ys);trivial.
Qed.

Lemma itMkProdNeq t xs:
  xs <> [] ->
  t <> it_mkProd_or_LetIn xs t.
Proof.
  (* induction xs in t |- *. *)
  (* - intros []. reflexivity. *)
  (* - intros _ H. *)
  (*   destruct a as [? [] ?];cbn in H. *)
  (*   + apply IHxs. *)
  (*   cbn. *)

  (* induction xs using rev_ind. *)
  (* - intros []. reflexivity. *)
  (* - intros. *)
  (*   destruct x as [? [] ?]. *)
  (*   +  *)

  (* intros H H1. *)
  (* induction xs using rev_ind. *)
  (* - now contradict H. *)
  (* - destruct x as [? [] ?]. *)
  (*   + rewrite foldMkProdLetIn. *)
Admitted. (* Basic *)

Lemma appOneNeqNil {X} xs (x:X):
  xs ++ [x] <> [].
Proof.
  induction xs;cbn;congruence.
Qed.

Lemma itMkProdInj xs ys t:
  it_mkProd_or_LetIn xs t = it_mkProd_or_LetIn ys t ->
  xs=ys.
Proof.
  intros H.
  induction xs as [|[? [] ?]] using rev_ind in ys, H |- *;
    destruct ys as [|[? [] ?]] using rev_ind.
  6, 8:
    try rewrite foldMkProd in H;
    try rewrite foldMkProdLetIn in H;
    try congruence.
  2,3,4,6:
    cbn in H;
    [apply itMkProdNeq in H as [] +
    (symmetry in H;apply itMkProdNeq in H as [])];
    apply appOneNeqNil.
  - reflexivity.
  - do 2 rewrite foldMkProdLetIn in H.
    injection H as -> -> ->.
    erewrite IHxs.
    + reflexivity.
    + apply H.
  - do 2 rewrite foldMkProd in H.
    injection H as -> ->.
    erewrite IHxs.
    + reflexivity.
    + apply H.
Qed.



Lemma appInjLen {X} (xs ys xs2 ys2:list X):
  #|xs| = #|xs2| ->
  xs ++ ys = xs2 ++ ys2 ->
  xs=xs2 /\ ys=ys2.
Proof.
  intros.
  induction xs in xs2, H, H0 |- *.
  - cbn in H.
    destruct xs2;cbn in H;try congruence.
    cbn in H0.
    now split.
  - destruct xs2;cbn in H;try congruence.
    injection H as H.
    cbn in H0.
    injection H0 as -> H0.
    apply IHxs in H as [-> ->];trivial.
    now split.
Qed.

Print to_extended_list_k.
Lemma toExtendedListLen Γ k:
  #|to_extended_list_k Γ k| = #|filter (fun a => match decl_body a with None => true | _ => false end) Γ |.
Proof.
  unfold to_extended_list_k.
  enough (forall Γ2 Γ1 k, #|reln Γ1 k Γ2| = #|Γ1| + #|filter (fun a => match decl_body a with None => true | _ => false end) Γ2|).
  1: {
    rewrite H.
    cbn.
    reflexivity.
  }
  clear Γ k.
  intros Γ.
  induction Γ;intros;cbn.
  - lia.
  - destruct a, decl_body.
    + rewrite IHΓ.
      cbn.
      reflexivity.
    + rewrite IHΓ.
      cbn.
      lia.
Qed.

Lemma toExtendedListLenNoBody Γ k:
  (forall a, In a Γ -> decl_body a = None) ->
  #|to_extended_list_k Γ k| = #|Γ|.
Proof.
  intros.
  rewrite toExtendedListLen.
  induction Γ.
  - reflexivity.
  - cbn.
    specialize (H a) as H2.
    rewrite H2.
    + cbn.
      rewrite IHΓ;trivial.
      intros.
      apply H. now right.
    + now left.
Qed.

Lemma substInstanceContextLen a xs:
  #|subst_instance_context a xs| = #|xs|.
Proof.
  unfold subst_instance_context, map_context.
  now rewrite mapLen.
Qed.

Lemma mapProdToLambdaItMkProd xs t:
  (forall x, In x xs -> decl_body x = None) ->
  mapProdToLambda (it_mkProd_or_LetIn xs t) =
  it_mkLambda_or_LetIn xs (mapProdToLambda t).
Proof.
  intros H.
  do 2 rewrite <- mapAgreement.
  induction xs using rev_ind.
  - reflexivity.
  - specialize (H x) as H2.
    destruct x.
    cbn in H2.
    rewrite H2.
    2: {
      apply in_or_app.
      right. now left.
    }
    rewrite foldMkProd, foldMkLambda.
    cbn. f_equal.
    apply IHxs.
    intros;apply H.
    apply in_or_app.
    now left.
Qed.

Lemma mapProdNoProd t:
  ~isProd t ->
  mapProdToLambda t = t.
Proof.
  rewrite <- mapAgreement.
  intros H.
  destruct t;cbn in *;try congruence.
Qed.

Lemma subst_it_mkLambda_or_LetIn xs k ctx t :
  subst xs k (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (subst_context xs k ctx) (subst xs (#|ctx| + k) t).
Proof.
  induction ctx in xs, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc xs k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (subst_context_snoc xs k ctx a).
  now destruct a as [na [b|] ty].
Qed.

Lemma mkAppsTApp xs t:
  xs <> [] -> exists s ys, mkApps t xs = tApp s ys.
Proof.
  intros.
  induction xs.
  - congruence.
  - destruct xs.
    + destruct t;eexists;eexists;reflexivity.
    + destruct t;eexists;eexists;reflexivity.
Qed.

Lemma mkAppNoLambda t xs:
  ~isLambda t ->
  ~ isLambda(mkApps t xs).
Proof.
  destruct xs.
  - trivial.
  - intros.
    pose proof (mkAppsTApp (t0::xs) t).
    destruct H0 as (?&?&?).
    1: congruence.
    rewrite H0.
    trivial.
Qed.

Lemma replaceLastOffsetAll f off s:
  ~isLambda s -> ~isProd s -> ~isLetIn s ->
  replaceLastOffset f off s = f off s.
Proof.
  destruct s;cbn;congruence.
Qed.

Lemma matchOnMkApps {X} t ys f (g:X):
  ~isApp t ->
  match mkApps t ys with
  | tApp _ xs => f xs
  | _ => g
  end
  =
  match ys with
  | [] => g
  | _ => f ys
  end.
Proof.
  intros.
  destruct ys.
  - cbn.
    destruct t;cbn;cbn in H;congruence.
  - cbn.
    assert(match t with
        | tApp f0 args => tApp f0 (args ++ t0 :: ys)
        | _ => tApp t (t0 :: ys)
           end = tApp t (t0::ys)) as ->.
    {
      destruct t;cbn;cbn in H;congruence.
    }
    reflexivity.
Qed.

Check simpl_lift.

Lemma simplLiftContext M n k p i:
  i <= k + n -> k <= i ->
  lift_context p i (lift_context n k M) =
  lift_context (p+n) k M.
Proof.
  intros.
  unfold lift_context, fold_context.
  rewrite revRev.
  rewrite mapi_mapi.
  unfold map_decl.
  cbn.
  (* rewrite simpl_lift. *)
  f_equal.
  apply mapiExt.
  intros.
  rewrite simpl_lift.
  2-3: lia.
  f_equal.
  destruct decl_body.
  2: reflexivity.
  cbn.
  f_equal.
  rewrite simpl_lift.
  2-3: lia.
  reflexivity.
Qed.


Lemma mapDeclVass x n: map decl_type (map (vass n) x)=x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - cbn.
    now rewrite IHx.
Qed.


Compute (reln_alt 0 [vass nAnon (tRel 42);vass nAnon (tRel 43)]).
Compute (mkRel [vass nAnon (tRel 42);vass nAnon (tRel 43)]).

Lemma vassCons x xs: allVass (x::xs) -> allVass xs.
Proof.
  intros H y H1.
  apply H.
  now right.
Qed.

Lemma vassSubstContext Γ xs k:
  allVass Γ ->
  allVass (subst_context xs k Γ).
Proof.
  intros.
  induction Γ.
  - cbn. apply H.
  - cbn.
    rewrite mapi_rec_app.
    intros x H1.
    apply in_rev in H1.
    apply in_app_or in H1 as [].
    + apply in_mapi in H0.
      destruct H0 as (?&?&?&?%in_rev).
      subst x.
      specialize (H x1).
      destruct x1.
      cbn in *.
      rewrite H.
      2: {
        right.
        apply H2.
      }
      reflexivity.
    + cbn in H0.
      destruct H0 as [<- | []].
      specialize (H a).
      destruct a;cbn in H;rewrite H.
      2: now left.
      reflexivity.
Qed.

(* maybe replace mkRel with reln *)
Lemma relnMkRel xs:
  allVass xs ->
  reln_alt 0 xs = rev(mkRel xs).
Proof.
Admitted. (* basic *)

Print inds.
Lemma nthInds n ind univ mutbodies:
  n < #|mutbodies| ->
  nth_error (inds ind univ mutbodies) n =
  Some (tInd {| inductive_mind := ind; inductive_ind := n |} univ).
Proof.
  intros H.
  unfold inds.
  remember (#|mutbodies|).
  clear Heqn0.
  induction H;admit.
Admitted. (* Basic *)


End Tmp.

Variable (maxElimSort: universe).

Section MainSec.

Variable
  (Σ : global_env_ext)
  (Γ : context)
  (mind_body : mutual_inductive_body)
  (ind : inductive)
  (univ : universe_instance)
  (ind_body : one_inductive_body)
  (Hwf : wf_local Σ Γ)
  (onInd : on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body)
  (onIndB : on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body)
  (declM : declared_minductive Σ (inductive_mind ind) mind_body)
  (declI : declared_inductive Σ mind_body ind ind_body)
  (uniP : getParamCount ind_body (ind_npars mind_body) = ind_npars mind_body)
  (nparCount : ind_npars mind_body = #|ind_params mind_body|)
  (nameF : name -> term -> name)
  (findBody : nth_error (Ast.ind_bodies mind_body) (inductive_ind ind) = Some ind_body)
  (onInductives : Alli (on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body) 0 (ind_bodies mind_body))
  (onParams : on_context (lift_typing typing) Σ (ind_params mind_body))
  (onNpars : context_assumptions (ind_params mind_body) = ind_npars mind_body)
  (onGuard : TemplateTyping.ind_guard mind_body)
  (ind_indices : context)
  (ind_sort : universe)
  (ind_arity_eq : ind_type ind_body =
  it_mkProd_or_LetIn (ind_params mind_body)
  (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
  (onArity : on_type (lift_typing typing) Σ [] (ind_type ind_body))
  (ind_ctors_sort : list universe)
  (onConstructors : on_constructors (lift_typing typing) Σ mind_body (inductive_ind ind) ind_body
  (ind_ctors ind_body) ind_ctors_sort)
  (onProjections : ind_projs ind_body <> [] ->
  on_projections (lift_typing typing) Σ (inductive_mind ind) mind_body
  (inductive_ind ind) ind_body ind_indices)
  (ind_sorts : check_ind_sorts (lift_typing typing) Σ (ind_params mind_body) (ind_kelim ind_body) ind_indices
  ind_ctors_sort ind_sort).

Print wf_local.
Print wf.


Lemma getMaxElimSort: (* ind_body: *)
   getMaxElim (ind_kelim ind_body) = tSort maxElimSort.
Proof.
Admitted. (* Universe *)

Lemma wfSigma:
  wf Σ.1.
Proof.
Admitted. (* Universe *)

Lemma indicesVass :
forall x : Ast.context_decl, In x ind_indices -> Ast.decl_body x = None.
Proof.
  intros.
  Print check_ind_sorts.
  Print type_local_ctx. (* maybe here *)
  unfold check_ind_sorts in ind_sorts.
  destruct universe_family eqn: UnivFamEq.
  - admit.
  - destruct ind_sorts.
    cbn in y.
    admit.
  - cbn in ind_sorts. admit.
Admitted. (* Basic *)


Lemma liftIndicesVass :
  forall n,
forall x : Ast.context_decl,
In x (lift_context n 0 ind_indices) -> Ast.decl_body x = None.
Proof.
  intros.
  eapply liftingInVass.
  2: apply H.
  eapply indicesVass;eassumption.
Qed.

Lemma typingParamInd:
  { x &
    Σ;;; [] |- it_mkProd_or_LetIn (ind_params mind_body) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) : TemplateTerm.tSort x}.
Proof.
  rewrite ind_arity_eq in onArity.
  cbn in onArity.
  apply onArity.
Qed.

Lemma wfLocalIndicesMin:
  wf_local Σ
           (ind_params mind_body,,,ind_indices).
Proof.
  pose proof typingParamInd.
  destruct X.
  apply it_mkProd_inv in t0.
  2: {
    eapply indParamVass.
    apply onInd.
  }
  apply it_mkProd_inv in t0.
  2: {
    apply indicesVass.
  }
  apply typing_wf_local in t0.
  unfold app_context in *.
  rewrite app_nil_r in t0.
  apply t0.
Qed.

Lemma wfLocalRelIndicesMin:
  wf_local_rel Σ
    (Γ ,,, (ind_params mind_body))
    ind_indices.
Proof.
  pose proof wfLocalIndicesMin.
Admitted. (* Basic *)

Lemma wfParams :
wf_local_rel Σ Γ (ind_params mind_body).
Proof.
  intros.
  eapply wfParamsAux;eassumption.
Qed.

Lemma wfLocalParamsMinMin:
  wf_local Σ
           (ind_params mind_body).
Proof.
  inv onParams;now constructor.
Qed.

Lemma wfLocalParamsMin:
  wf_local Σ
           (Γ ,,, (ind_params mind_body)).
Proof.
  apply wf_local_app_inv.
  - apply Hwf.
  - apply wfParams.
Qed.

Lemma wfLocalParams:
  wf_local Σ
           (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)).
Proof.
  rewrite uniP, sub_diag.
  unfold skipn.
  apply wfLocalParamsMin.
Qed.

Lemma consistentInstanceExt:
  consistent_instance_ext Σ (ind_universes mind_body) univ.
Proof.
Admitted. (* Universe *)


Lemma substInstanceConstrParam:
map (fun x : context_decl =>
           {|
           decl_name := decl_name x;
           decl_body := decl_body x;
           decl_type := subst_instance_constr univ (decl_type x) |}) (ind_params mind_body)
= ind_params mind_body.
Proof.
Admitted. (* universe *)

Lemma substInstanceConstrIndices:
map (fun x : context_decl =>
           {|
           decl_name := decl_name x;
           decl_body := decl_body x;
           decl_type := subst_instance_constr univ (decl_type x) |}) ind_indices
= ind_indices.
Proof.
Admitted. (* universe *)


Lemma typingSpineIndices2:
  typing_spine Σ (Γ ,,, ind_params mind_body ,,, ind_indices) (subst_instance_constr univ (ind_type ind_body))
    (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
          (ind_params mind_body) ++
     mkRel ind_indices)
    (* nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|) *)
    (tSort (subst_instance_univ univ ind_sort)).
Proof.
  rewrite ind_arity_eq.

  unfold app_context.
  rewrite app_assoc.
  rewrite <- it_mkProd_or_LetIn_app.
  rewrite mapiNatRec.
  replace (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
       (ind_params mind_body) ++
       mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| - i - 1)) ind_indices) with
      (mkRel (ind_indices++ind_params mind_body)).
  2: {
    rewrite nparCount.
    now rewrite mkRelApp, <- mapiNatRec.
  }
  pose proof typingSpineProdApp.
  unfold app_context in X.
  rewrite substInstanceConstrMkProd.
  2: {
    intros.
    apply in_app_or in H as [].
    + now apply indicesVass.
    + eapply indParamVass;try eassumption.
  }
  replace (map
          (fun x : context_decl =>
           {|
           decl_name := decl_name x;
           decl_body := decl_body x;
           decl_type := subst_instance_constr univ (decl_type x) |}) (ind_indices ++ ind_params mind_body))
    with (ind_indices ++ ind_params mind_body).
  2: now rewrite map_app, substInstanceConstrParam, substInstanceConstrIndices.
  apply X.
  cbn.
  constructor.
Qed.

Lemma indAppType :
  { s1 &
  Σ;;;
  Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body) ,,,
  ind_indices
  |- createAppChain
       ((lift0 #|ind_indices|)
          (mkApps (tInd ind univ)
             (mapi
                (fun (i : nat) (_ : context_decl) => tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)))))
       #|ind_indices| : tSort s1}.
Proof.
  (* destruct typingSpineIndices2. *)
  eexists.
  rewrite lift_mkApps.
  rewrite map_mapi.
  rewrite uniP, sub_diag.
  unfold skipn.
  unfold createAppChain, createAppChainOff.
  rewrite mkApps_nested.
  cbn.
  eapply Generation.type_mkApps.
  - eapply type_Ind;try eassumption.
    + apply wf_local_app_inv.
      * apply wfLocalParamsMin.
      * apply wfLocalRelIndicesMin.
    + apply consistentInstanceExt.
  - apply typingSpineIndices2.
Qed.


Lemma indicesType:
  {ts &
 typingList Σ
    (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body))
    ind_indices ts}.
Proof.
  rewrite uniP, sub_diag. unfold skipn.
  apply wfLocalRelTypingList.
  apply wfLocalRelIndicesMin.
Qed.


Lemma maxElimType:
  {s2 &
 Σ;;;
  (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body) ,,,
   ind_indices),,
  vass (nNamed (ind_name ind_body))
    (createAppChain
       ((lift0 #|ind_indices|)
          (mkApps (tInd ind univ)
             (mapi
                (fun (i : nat) (_ : context_decl) => tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)))))
       #|ind_indices|) |- getMaxElim (ind_kelim ind_body) : tSort s2
  }.
Proof.
Admitted. (* Universe *)

Lemma pType :
  ∑ s1 : universe,
    Σ;;;
    Γ ,,,
    skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)
    |- replaceLastProd
         (tProd (nNamed (ind_name ind_body))
            (createAppChain
               ((lift0
                   (count_prods
                      (remove_arity (getParamCount ind_body (ind_npars mind_body))
                         (ind_type ind_body))))
                  (mkApps (tInd ind univ)
                     (mapi
                        (fun (i : nat) (_ : context_decl) =>
                         tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                        (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                           (ind_params mind_body)))))
               (count_prods
                  (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
            (getMaxElim (ind_kelim ind_body)))
         (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)) :
    tSort s1.
Proof.
  destruct indicesType as [ts tsH].
  destruct indAppType as [s1 s1H].
  destruct maxElimType as [s2 s2H].
  evar (s3:universe).
  exists s3.

  rewrite ind_arity_eq.
  rewrite removeArityCount.
  2: eapply indParamVass;eassumption.
  2: now rewrite nparCount.
  rewrite replaceUnderItMkProd.
  cbn.
  2: eapply indicesVass;eassumption.
  unfold count_prods.
  rewrite collectProdMkProd.
  2: eapply indicesVass;eassumption.
  2: cbn;congruence.
  rewrite revLen.

  eapply type_it_mkProd_or_LetIn.
  - eapply indicesVass;eassumption.
  - apply tsH.
  - apply type_Prod.
    + apply s1H.
    + apply s2H.
Qed.

Print onConstructors.
Print on_constructors.
Print on_constructor.

About typing.

Print typing.
Print cumul.

Lemma onConstructorIndBodyNotMatter A B ctor sort:
  on_constructor (lift_typing typing) Σ mind_body (inductive_ind ind) A ctor sort ->
  on_constructor (lift_typing typing) Σ mind_body (inductive_ind ind) B ctor sort.
Proof.
  intros.
  destruct X as [H [s H1]].
  split.
  - apply H.
  - Print constructor_shape.
    destruct s.
Admitted. (* Basic *)

(* Lemma typeCtorCase: *)
(*   Σ;;; *)
(*   (Γ ,,, skipn 0 (ind_params mind_body)),, *)
(*   vass (nNamed "p"%string) *)
(*     (it_mkProd_or_LetIn ind_indices *)
(*        (tProd (nNamed "inst"%string) *)
(*           (createAppChain *)
(*              ((lift0 #|ind_indices|) *)
(*                 (mkApps (tInd ind univ) (mapi (fun (i0 : nat) (_ : context_decl) => tRel (ind_npars mind_body - i0 - 1)) (ind_params mind_body)))) *)
(*              #|ind_indices|) (getMaxElim ind_kelim))) ,,, *)
(*   rev *)
(*     (mapi_rec *)
(*        (fun (n0 : nat) (x : (ident × term) × nat) => *)
(*         let (y0, count) := x in *)
(*         let (name, _) := y0 in *)
(*         vass (nNamed ("H" :s ("_" :s name))) *)
(*           (constrMapping (tInd ind univ) (ind_npars mind_body) x (S n0) *)
(*              (fun type_app : term => *)
(*               tApp (tRel (count + n0)) *)
(*                 (match type_app with *)
(*                  | tApp _ xs => skipn (ind_npars mind_body) xs *)
(*                  | _ => [] *)
(*                  end ++ [createAppChain ((lift0 (S (count + n0))) (createAppChain (tConstruct ind n0 univ) (ind_npars mind_body))) count])))) ind_ctors 0) *)
(*   |- replaceLastOffset *)
(*        (fun (_ : nat) (type_app : term) => *)
(*         tApp (tRel (n + (#|ind_ctors| + 0))) *)
(*           (match type_app with *)
(*            | tApp _ xs => skipn (ind_npars mind_body) xs *)
(*            | _ => [] *)
(*            end ++ *)
(*            [createAppChain ((lift0 (S (n + (#|ind_ctors| + 0)))) (createAppChain (tConstruct ind (#|ind_ctors| + 0) univ) (ind_npars mind_body))) n])) 0 *)
(*        ((lift0 (S (#|ind_ctors| + 0))) *)
(*           ((TemplateEnvironment.it_mkProd_or_LetIn cshape_args *)
(*               (TemplateTerm.mkApps cshape_concl_head *)
(*                  (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args| ++ cshape_indices))) *)
(*            {ind_npars mind_body := tInd ind univ})) : TemplateTerm.tSort ?u *)

Lemma diffIndBody:
  0 = #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind).
Proof.
Admitted. (* Universe *)

(* Lemma typeCtorCase: *)
(*   forall (ind_name : ident) (ind_type : TemplateTerm.term) (ind_kelim : list sort_family) *)
(*     (ind_ctors : list ((ident × TemplateTerm.term) × nat)) (ind_projs : list (ident × TemplateTerm.term)) *)
(*     (i : ident) (t0 : TemplateTerm.term) (n : nat) (sorts1 sorts2 : list universe) *)
(*     (onConstructors : ∑ '(l1', l2'), *)
(*                         (sorts1 ++ sorts2 = l1' ++ l2' *)
(*                          × All2 *)
(*                              (on_constructor (lift_typing typing) Σ mind_body (inductive_ind ind) *)
(*                                 {| *)
(*                                 ind_name := ind_name; *)
(*                                 ind_type := ind_type; *)
(*                                 ind_kelim := ind_kelim; *)
(*                                 ind_ctors := ind_ctors ++ [(i, t0, n)]; *)
(*                                 ind_projs := ind_projs |}) ind_ctors l1') *)
(*                         × All2 *)
(*                             (on_constructor (lift_typing typing) Σ mind_body (inductive_ind ind) *)
(*                                {| *)
(*                                ind_name := ind_name; *)
(*                                ind_type := ind_type; *)
(*                                ind_kelim := ind_kelim; *)
(*                                ind_ctors := ind_ctors ++ [(i, t0, n)]; *)
(*                                ind_projs := ind_projs |}) [(i, t0, n)] l2') *)
(*     (onCtors1 : All2 *)
(*                   (on_constructor (lift_typing typing) Σ mind_body (inductive_ind ind) *)
(*                      {| *)
(*                      ind_name := ind_name; *)
(*                      ind_type := ind_type; *)
(*                      ind_kelim := ind_kelim; *)
(*                      ind_ctors := ind_ctors ++ [(i, t0, n)]; *)
(*                      ind_projs := ind_projs |}) ind_ctors sorts1) (y : universe) (l' : list universe) *)
(*     (X0 : on_type (lift_typing typing) Σ *)
(*             (TemplateEnvironment.arities_context (TemplateEnvironment.ind_bodies mind_body)) *)
(*             (i, t0, n).1.2) (cshape_args : TemplateEnvironment.context), *)
(*   let cshape_concl_head := *)
(*     TemplateTerm.tRel *)
(*       (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) + *)
(*        #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|) in *)
(*   forall (cshape_indices : list TemplateTerm.term) *)
(*     (cshape_eq : t0 = *)
(*                  TemplateEnvironment.it_mkProd_or_LetIn (TemplateEnvironment.ind_params mind_body) *)
(*                    (TemplateEnvironment.it_mkProd_or_LetIn cshape_args *)
(*                       (TemplateTerm.mkApps cshape_concl_head *)
(*                          (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) *)
(*                             #|cshape_args| ++ cshape_indices)))) *)
(*     (t1 : type_local_ctx (lift_typing typing) Σ *)
(*             (TemplateEnvironment.arities_context (TemplateEnvironment.ind_bodies mind_body) ,,, *)
(*              TemplateEnvironment.ind_params mind_body) cshape_args y), *)
(*     { u & *)
(*   Σ;;; *)
(*   (Γ ,,, skipn 0 (ind_params mind_body)),, *)
(*   vass (nNamed "p"%string) *)
(*     (it_mkProd_or_LetIn ind_indices *)
(*        (tProd (nNamed "inst"%string) *)
(*           (createAppChain *)
(*              (mkApps (tInd ind univ) *)
(*                 (mapi *)
(*                    (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i0 - 1))) *)
(*                    (ind_params mind_body))) #|ind_indices|) (getMaxElim ind_kelim))) ,,, *)
(*   rev *)
(*     (mapi_rec *)
(*        (fun (n0 : nat) (x : (ident × term) × nat) => *)
(*         let (y0, count) := x in *)
(*         let (name, _) := y0 in *)
(*         vass (nNamed ("H" :s ("_" :s name))) *)
(*           (constrMapping (tInd ind univ) (ind_npars mind_body) x (S n0) *)
(*              (fun type_app : term => *)
(*               tApp (tRel (count + n0)) *)
(*                 (match type_app with *)
(*                  | tApp _ xs => skipn (ind_npars mind_body) xs *)
(*                  | _ => [] *)
(*                  end ++ *)
(*                  [createAppChain *)
(*                     ((lift0 (S (count + n0))) (createAppChain (tConstruct ind n0 univ) (ind_npars mind_body))) *)
(*                     count])))) ind_ctors 0) *)
(*   |- it_mkProd_or_LetIn *)
(*        (lift_context (S #|ind_ctors|) 0 (subst_context [tInd ind univ] (ind_npars mind_body) cshape_args)) *)
(*        (replaceLastOffset *)
(*           (fun (_ : nat) (type_app : term) => *)
(*            tApp (tRel (n + #|ind_ctors|)) *)
(*              (match type_app with *)
(*               | tApp _ xs => skipn (ind_npars mind_body) xs *)
(*               | _ => [] *)
(*               end ++ *)
(*               [createAppChain *)
(*                  ((lift0 (S (n + #|ind_ctors|))) *)
(*                     (createAppChain (tConstruct ind #|ind_ctors| univ) (ind_npars mind_body))) n])) #|cshape_args| *)
(*           (mkApps (tInd ind univ) *)
(*              (map *)
(*                 (fun x : term => *)
(*                  lift (S #|ind_ctors|) #|cshape_args| *)
(*                    (subst [tInd ind univ] (#|cshape_args| + ind_npars mind_body) x)) *)
(*                 (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args| ++ *)
(*                  cshape_indices)))) : TemplateTerm.tSort u}. *)
(* Proof. *)
(*   intros. *)
(*   eexists. *)

(*   rewrite map_app. *)
(*   cbn. *)
(*   Print type_local_ctx. (* t1 *) *)
(*   cbn in X0. *)
(*   cbn in *. *)
(*   (* subst t0. *) *)
(* Admitted. (* TODO *) *)


Lemma typingListIndices:
  {ts & typingList Σ
    (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body))
    ind_indices ts}.
Proof.
  apply indicesType.
Qed.

Lemma typingListIndices2:
  { ts &
  typingList Σ
    ((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                ((lift0 #|ind_indices|)
                   (mkApps (tInd ind univ)
                      (mapi
                         (fun (i : nat) (_ : context_decl) =>
                          tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                         (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                            (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
     rev
       (quantifyCases false
          (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
             (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ))
    (lift_context (S #|ind_ctors ind_body|) 0 ind_indices) ts}.
Proof.
  destruct typingListIndices.
  unfold app_context in t0.
  eexists.
  unfold snoc, app_context.
  rewrite <- appCons.
  rewrite app_assoc.
  apply typingListOffset.
  2: {
    rewrite appLen, revLen, quantifyCasesLen.
    rewrite mapLen. cbn. lia.
  }
  apply t0.
Qed.

Lemma extendOnConstructors ind_name ind_type ind_kelim ind_ctors ind_projs xs zs:
on_constructors (lift_typing typing) Σ mind_body (inductive_ind ind)
                     {|
                     ind_name := ind_name;
                     ind_type := ind_type;
                     ind_kelim := ind_kelim;
                     ind_ctors := ind_ctors ++ xs;
                     ind_projs := ind_projs |} ind_ctors zs ->
on_constructors (lift_typing typing) Σ mind_body (inductive_ind ind)
                     {|
                     ind_name := ind_name;
                     ind_type := ind_type;
                     ind_kelim := ind_kelim;
                     ind_ctors := ind_ctors;
                     ind_projs := ind_projs |} ind_ctors zs.
Proof.
  pose proof onConstructorIndBodyNotMatter as IndBodyNotMatter.
  Print on_constructors.
  unfold on_constructors.
  intros onCtors1.
  eapply All2_impl'.
  apply onCtors1.
  clear ind_sorts onProjections onArity ind_sort onGuard onNpars onParams onInductives findBody nameF uniP declI declM onIndB ind_arity_eq.
  clear Hwf onInd onConstructors.
  clear onCtors1.
  match goal with
    |- All ?f ?xs =>
    enough(forall xs, All f xs)
  end.
  * apply X.
  * intros ys.
    induction ys.
    -- constructor.
    -- constructor.
        ++ apply IndBodyNotMatter.
        ++ apply IHys.
Qed.


Lemma typingSpineParamIndexRel:
  typing_spine Σ (Γ ,,, ind_params mind_body ,,, ind_indices) (subst_instance_constr univ (ind_type ind_body))
    (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
       (ind_params mind_body) ++
     nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)
    (tSort (subst_instance_univ univ ind_sort)).
Proof.
  apply typingSpineIndices2.
Qed.


Lemma wfLocalRelIndices2:
  wf_local_rel Σ
    (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body))
    ind_indices.
Proof.
  rewrite uniP, sub_diag.
  unfold skipn.
  apply wfLocalRelIndicesMin.
Qed.

Lemma typeIndAppIndices:
  ∑ s : universe,
    Σ;;; Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)
    |- it_mkProd_or_LetIn ind_indices
         (tProd (nNamed (ind_name ind_body))
            (mkApps (tInd ind univ)
               (mapi
                  (fun (i : nat) (_ : context_decl) =>
                   tRel (#|ind_indices| + (getParamCount ind_body (ind_npars mind_body) - i - 1)))
                  (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)) ++
                nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
            (getMaxElim (ind_kelim ind_body))) : TemplateTerm.tSort s.
Proof.
      destruct maxElimType.
      destruct typingListIndices.
      eexists.
      apply type_it_mkProd_or_LetIn.
      * apply indicesVass.
      * apply t1.
      * apply type_Prod.
        -- eapply Generation.type_mkApps.
           ++ eapply type_Ind;try eassumption.
              ** apply wf_local_app_inv.
                 --- apply wfLocalParams.
                 --- apply wfLocalRelIndices2.
              ** apply consistentInstanceExt.
           ++ rewrite uniP, sub_diag.
              unfold skipn.
              apply typingSpineParamIndexRel.
        -- unfold createAppChain, createAppChainOff in t0.
          rewrite lift_mkApps in t0.
          rewrite mkApps_nested in t0.
          rewrite map_mapi in t0.
          cbn in t0.
          apply t0.
Qed.





(* needs some additional assumptions *)
Lemma cshapeArgsVass cshape_args:
  forall x : context_decl, In x cshape_args -> decl_body x = None.
Proof.
Admitted. (* Basic *)

(* is given in form of type_local_ctx *)
(* need some additional assumptions *)
Lemma cshapeTypingList cshape_args:
  { ts &
    typingList Σ (ind_params mind_body ++ Γ) (subst_context [tInd ind univ] (ind_npars mind_body) cshape_args) ts}.
Proof.
Admitted. (* TODO *)


Lemma typeParamsP:
  ∑ s : universe,
    Σ;;; Γ ,,, ind_params mind_body
    |- it_mkProd_or_LetIn ind_indices
         (tProd (nNamed (ind_name ind_body))
            (createAppChain
               (mkApps (tInd ind univ)
                  (mapi
                     (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i0 - 1)))
                     (ind_params mind_body))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))
      : TemplateTerm.tSort s.
Proof.
    destruct typeIndAppIndices.
    exists x.
    rewrite uniP, nparCount, sub_diag in t0.
    unfold skipn in t0.
    unfold createAppChain, createAppChainOff.
    rewrite mkApps_nested.
    cbn. cbn in t0.
    uniapply t0.
    cbn.
    match goal with
      |- _ ;;; _ |- ?A : _ = _ ;;; _ |- ?B : _ =>
      replace A with B
    end;[trivial|].
    rewrite nparCount.
    reflexivity.
Qed.


Lemma wfLocalParamsP:
wf_local Σ
    ((Γ ,,, skipn 0 (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i0 - 1)))
                      (ind_params mind_body))) #|ind_indices|) (getMaxElim (ind_kelim ind_body))))).
Proof.
  unfold skipn.
  constructor.
  - apply wfLocalParamsMin.
  - cbn.
    apply typeParamsP.
Qed.

(* maybe inline *)
Lemma wfLocalRelCshapeArgs cshape_args:
wf_local_rel Σ
    ((Γ ,,, skipn 0 (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i0 - 1)))
                      (ind_params mind_body))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
     rev
       (mapi_rec
          (fun (n0 : nat) (x : (ident × term) × nat) =>
           let (y0, count) := x in
           let (name, _) := y0 in
           vass (nNamed ("H" :s ("_" :s name)))
             (constrMapping (tInd ind univ) (ind_npars mind_body) x (S n0)
                (fun type_app : term =>
                 tApp (tRel (count + n0))
                   (match type_app with
                    | tApp _ xs => skipn (ind_npars mind_body) xs
                    | _ => []
                    end ++
                    [createAppChain
                       ((lift0 (S (count + n0))) (createAppChain (tConstruct ind n0 univ) (ind_npars mind_body)))
                       count])))) (ind_ctors ind_body) 0))
    (lift_context (S #|(ind_ctors ind_body)|) 0 (subst_context [tInd ind univ] (ind_npars mind_body) cshape_args)).
Proof.
  match goal with
    |- wf_local_rel _ (?L1,,?l2,,,?L3) _ =>
    replace (L1,,l2,,,L3) with (L1,,,([l2],,,L3))
  end.
  2: {
    unfold snoc, app_context.
    cbn.
    repeat rewrite <- app_assoc.
    reflexivity.
  }
  apply weakeningWfLocalRel.
  - unfold skipn. apply wfLocalParamsMin.
  - apply wf_local_rel_app_inv.
    + constructor.
      * constructor.
      * cbn.
        apply typeParamsP.
    + cbn.
      admit. (* IH in wfLocalRelCases *)
  - admit. (* need ideas and knowledge for cshape_aprgs *)
  - rewrite appLen;cbn.
    rewrite revLen.
    rewrite mapi_rec_len.
    now rewrite add_comm.
Admitted. (* TODO *)


Print type_local_ctx.

Lemma wfLocalRelCases:
  wf_local_rel Σ
    ((Γ ,,, skipn 0 (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                ((lift0 #|ind_indices|)
                   (mkApps (tInd ind univ)
                      (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                         (ind_params mind_body)))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))))
    (rev (quantifyCases false (ind_ctors ind_body) (ind_npars mind_body) ind univ)).
Proof.
  pose proof cshapeArgsVass as HshapeVass.
  pose proof wfLocalParamsP as HwfParamsP.
  (* pose proof typeCtorCase as HtypeCtorCase. *)
  pose proof diffIndBody as diffEq.
  unfold quantifyCases.
  pose proof extendOnConstructors as extOnCtors.

  pose proof wfLocalParamsMin as HwfParamsMin.

  (* pose proof wfLocalRelCshapeArgs as HwfRelCshapeArgs. *)
  pose proof cshapeTypingList as HargsTypingList.
  (* [argsTy HargsTypingList]. *)
  (* pose proof typingListIndices2 as HtypeIndices. *)
  (* pose proof typingListIndices as HtypeIndices. *)
  (* rewrite uniP, sub_diag in HtypeIndices. *)

  (* pose proof onConstructorIndBodyNotMatter as IndBodyNotMatter. *)
  destruct ind_body.
  cbn in *.

  clear ind_sorts onProjections onArity ind_sort onGuard onNpars onParams onInductives findBody nameF uniP declI declM onIndB ind_arity_eq.
  induction ind_ctors using rev_elim in ind_ctors_sort, onConstructors, extOnCtors
                                        (* , HtypeIndices *)
                                        (* , HtypeIndices *)
                                        (* , HwfRelCshapeArgs *)
                                        |- *.
  - cbn. constructor.
  - rewrite mapi_rec_app.
    cbn. rewrite rev_unit.
    destruct x,p.
      unfold on_constructors in onConstructors.
      apply All2_app_inv in onConstructors.
      destruct onConstructors as [[sorts1 sorts2] [[-> onCtors1] onCtors2]].
    apply wf_local_rel_abs.
    + eapply IHind_ctors.
      2: {
        apply extOnCtors.
      }
      (* 2: { *)
      (*   apply HwfRelCshapeArgs. *)
      (* } *)
      (* 2: { *)
      (*   apply HtypeIndices. *)
      (* } *)
      eapply extOnCtors.
      eapply onCtors1.
      (* Print on_constructors. *)
      (* unfold on_constructors. *)
      (* eapply All2_impl'. *)
      (* apply onCtors1. *)
      (* clear Hwf onInd onConstructors IHind_ctors. *)
      (* clear onCtors1 onCtors2. *)
      (* match goal with *)
      (*   |- All ?f ?xs => *)
      (*   enough(forall xs, All f xs) *)
      (* end. *)
      (* * apply X. *)
      (* * intros xs. *)
      (*   induction xs. *)
      (*   -- constructor. *)
      (*   -- constructor. *)
      (*      ++ apply IndBodyNotMatter. *)
      (*      ++ apply IHxs. *)
    + cbn. (* needs information about ctors *)
      inv onCtors2.
      inv X0.
      inv X.
      cbn in X1.
      destruct X1.

      destruct x.
      rewrite cshape_eq.
      cbn in t1.

      specialize (HargsTypingList cshape_args).
      destruct HargsTypingList as [argsType HargsTypingList].

      eexists.
      match goal with
        |- TemplateTyping.typing ?T0 ?T1 ?T2 ?T3 ?T4 =>
          change (T1;;;T2 |- T3 : T4)
      end.

      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: apply nparCount.

      {
        unfold subst1.
        rewrite subst_it_mkProd_or_LetIn.
        rewrite lift_it_mkProd_or_LetIn.
        rewrite subst_mkApps.
        cbn.
        replace (#|cshape_args| + ind_npars mind_body <=?
                  #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
                  #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|) with true.
        2: {
          rewrite nparCount.
          symmetry.
          apply leb_correct.
          lia.
        }
        replace (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
                 #|TemplateEnvironment.ind_params mind_body| + #|cshape_args| -
                 (#|cshape_args| + ind_npars mind_body)) with 0.
        2: {
          rewrite nparCount.
          match goal with
            |- 0 = ?G =>
            replace G with (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind)) by lia
          end.
          apply diffEq.
        }
        cbn.
        rewrite replaceOffsetUnderItProd.
        rewrite lift_context_len.
        rewrite subst_context_len.
        cbn.
        do 2 rewrite lift_mkApps.
        rewrite map_mapi.
        cbn.
        rewrite map_map.
        repeat rewrite add_0_r.
        Print to_extended_list_k.
        Print reln.
        (* clear IHind_ctors diffEq. *)
        rewrite cshape_eq in X0.
        cbn in X0.


        rewrite map_app.
        cbn.
        Print type_local_ctx. (* t1 *)
        cbn in X0.
        cbn in *.
        Print replaceLastOffset.

        match goal with
          |- _ ;;; _ |- it_mkProd_or_LetIn _ (replaceLastOffset _ _ (mkApps _ ?L)) : _ => set L as appList
        end.
        rewrite replaceLastOffsetAll.
        2-4: destruct appList;cbn;trivial.
        subst appList.
        (* rewrite <- map_app. *)

        apply type_it_mkProd_or_LetIn.
        1: {
          intros.
          eapply liftingInVass.
          2: apply H.
          intros.
          (* eapply HshapeVass with (cshape_args := cshape_args). *)
          unfold subst_context, fold_context in H0.
          apply In_rev in H0.
          apply in_mapi in H0 as (?&?&?&?).
          subst x0.
          apply In_rev in H1.
          apply HshapeVass in H1.
          destruct x2.
          cbn in H1.
          rewrite H1.
          reflexivity.
        }
        1: {

  (* destruct HtypeIndices as [? t2]. *)
  (* unfold app_context in t2. *)
  (* eexists. *)
  unfold snoc, app_context.
  rewrite <- appCons.
  rewrite app_assoc.
  apply typingListOffset.
  2: {
    rewrite appLen, revLen, mapi_rec_len.
    cbn.
    lia.
    (* rewrite appLen, revLen, quantifyCasesLen. *)
    (* rewrite mapLen. cbn. lia. *)
  }
  unfold skipn.
  (* apply t2. *)
  (* is in t1 given with type_local_ctx *)
  apply HargsTypingList.

        }

        replace (match
          mkApps (tInd ind univ)
            (map
               (fun x : term =>
                lift (S #|ind_ctors|) #|cshape_args|
                  (subst [tInd ind univ] (#|cshape_args| + ind_npars mind_body) x))
               (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args|) ++
             map
               (fun x : term =>
                lift (S #|ind_ctors|) #|cshape_args|
                  (subst [tInd ind univ] (#|cshape_args| + ind_npars mind_body) x)) cshape_indices)
        with
        | tApp _ xs => skipn (ind_npars mind_body) xs
        | _ => []
                  end) with (
             map
               (fun x : term =>
                lift (S #|ind_ctors|) #|cshape_args|
                  (subst [tInd ind univ] (#|cshape_args| + ind_npars mind_body) x)) cshape_indices
                         ).
        2: {
          rewrite matchOnMkApps.
          2: {
            trivial.
          }
          replace (skipn (ind_npars mind_body)) with
              (@skipn term (#|map
           (fun x : term =>
            lift (S #|ind_ctors|) #|cshape_args| (subst [tInd ind univ] (#|cshape_args| + ind_npars mind_body) x))
           (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args|)  |)).
          2: {
            f_equal.
            rewrite mapLen.
            rewrite toExtendedListLenNoBody.
            2: eapply indParamVass;eassumption.
            rewrite nparCount.
            reflexivity.
          }
          rewrite skipnApp.
          destruct map.
          - destruct map;trivial.
          - destruct map;cbn;trivial.
        }
        eapply type_App.
        - apply type_Rel.
          + apply wf_local_app_inv.
            * apply wf_local_app_inv.
              -- apply HwfParamsP.
              -- rewrite lift_mkApps in IHind_ctors.
                 rewrite map_mapi in IHind_ctors.
                eapply IHind_ctors.
                2: {
                  apply extOnCtors.
                }
                eapply extOnCtors.
                eapply onCtors1.
            * match goal with
                |- wf_local_rel _
                               (?L1,,?l2,,,?L3) _ =>
                replace (L1,,l2,,,L3) with (L1,,,(L3++[l2]))
              end.
              2: {
                unfold snoc, app_context.
                cbn.
                repeat rewrite <- app_assoc.
                cbn.
                reflexivity.
              }
              unfold skipn.
              apply weakeningWfLocalRel.
              4: {
                rewrite appLen,revLen,mapi_rec_len.
                cbn.
                lia.
              }
              1: {
                apply HwfParamsMin.
              }
              1: {
                Fail apply IHind_ctors.
                admit.
              }
              (* should be derived from t1 *)
              admit. (* cshape_args wf_local *) (* wfLocalRelCshapeArgs *)
          + assert(n=#|cshape_args|) by admit. (* from paper maybe in proof somewhere *)
            rewrite H.
            rewrite nth_error_app_ge.
            2: {
              rewrite lift_context_len, subst_context_len.
              lia.
            }
            rewrite nth_error_app_ge.
            2: {
              rewrite revLen, mapi_rec_len, lift_context_len, subst_context_len.
              lia.
            }
            match goal with
              |- nth_error _ ?m = _ =>
              replace m with 0
            end.
            2: {
              rewrite lift_context_len, revLen, mapi_rec_len, subst_context_len.
              lia.
            }
            reflexivity.
        - reflexivity.
        - destruct map;cbn;congruence.
        - cbn.
          (* part 1 cshape_indices have indices as argument *)
          (* part 2 construct has ind as type *)

          (* maybe contained in X0 *)
          admit. (* above in this proof (only that lift_context is under rest typingList) *)
          (* here typing Spine *)
        (* X0 looks similiar *)


        (* revert *)
        (*   ind_name ind_type ind_kelim ind_ctors ind_projs *)
        (*   i t0 n sorts1 sorts2 onConstructors onCtors1 y l' X0 cshape_args cshape_concl_head cshape_indices cshape_eq t1. *)

        (* edestruct HtypeCtorCase;try eassumption. *)
        (* apply t2. *)
        (* destruct typeCtorCase. *)

        (* match goal with *)
        (*   |- _ ;;; _ |- it_mkProd_or_LetIn _ (replaceLastOffset) *)
        (* destruct map;cbn. *)

      }
Admitted. (* TODO *)


Lemma wfLocalQuantifyCases:
  wf_local Σ
    ((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (mkApps (tInd ind univ)
                (mapi
                   (fun (i : nat) (_ : context_decl) =>
                    tRel (#|ind_indices| + (getParamCount ind_body (ind_npars mind_body) - i - 1)))
                   (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                      (ind_params mind_body)) ++
                 nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                   #|ind_indices|)) (getMaxElim (ind_kelim ind_body)))) ,,,
     rev
       (quantifyCases false
          (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
               (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)).
Proof.
  apply wf_local_app_inv.
  - constructor.
    + apply wfLocalParams.
    + cbn.
      apply typeIndAppIndices.
  - pose proof wfLocalRelCases.
    unfold createAppChain, createAppChainOff in X.
    rewrite lift_mkApps in X.
    rewrite mkApps_nested in X.
    rewrite map_mapi in X.
    cbn in X.
    rewrite uniP.
    rewrite sub_diag.
    cbn.
    rewrite mapSndAdd0.
    apply X.
Qed.


Lemma wfLocalRelCasesAux :
  wf_local_rel Σ
    ((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (replaceLastProd
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                ((lift0
                    (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                   (mkApps (tInd ind univ)
                      (mapi
                         (fun (i : nat) (_ : context_decl) =>
                          tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                         (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                            (ind_params mind_body)))))
                (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
             (getMaxElim (ind_kelim ind_body)))
          (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
    (rev
       (quantifyCases false
          (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
             (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)).
Proof.
  intros.
  rewrite uniP.
  rewrite sub_diag.
  rewrite mapSndAdd0.
  rewrite ind_arity_eq.
  rewrite removeArityCount.
  2: eapply indParamVass;eassumption.
  2: apply nparCount.
  rewrite replaceUnderItMkProd.
  2: eapply indicesVass.
  unfold count_prods.
  rewrite collectProdMkProd.
  2: eapply indicesVass.
  2: cbn;congruence.
  cbn.
  unfold skipn.
  rewrite revLen.
  apply wfLocalRelCases.
Qed.





Lemma wfLocalRelIndices:
  wf_local_rel Σ
    ((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                ((lift0 #|ind_indices|)
                   (mkApps (tInd ind univ)
                      (mapi
                         (fun (i : nat) (_ : context_decl) =>
                          tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                         (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                            (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
     rev
       (quantifyCases false
          (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
             (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ))
    (lift_context (S #|ind_ctors ind_body|) 0 ind_indices).
Proof.
  rewrite uniP, sub_diag.
  unfold skipn.
  unfold snoc, app_context.
  rewrite <- appCons.
  rewrite app_assoc.
  apply weakeningWfLocalRel.
  - apply wf_local_app_inv.
    + apply Hwf.
    + apply wfParams.
  - apply wf_local_rel_app_inv.
    + apply wf_local_rel_abs.
      * constructor.
      * cbn.
        destruct typeIndAppIndices.
        unfold createAppChain, createAppChainOff.
        rewrite lift_mkApps.
        rewrite mkApps_nested.
        rewrite map_mapi.
        cbn.
        rewrite uniP in t0.
        rewrite sub_diag in t0.
        unfold skipn in t0.
        eexists.
        apply t0.
    + cbn. pose proof wfLocalRelCases.
      unfold skipn in X.
      unfold snoc, app_context in X.
      rewrite mapSndAdd0.
      apply X.
  - apply wfLocalRelIndicesMin.
  - rewrite appLen, revLen, quantifyCasesLen.
    cbn.
    rewrite mapLen.
    lia.
Qed.



Lemma typetInd:
  { t &
  Σ;;;
  (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
  vass (nNamed "p"%string)
    (it_mkProd_or_LetIn ind_indices
       (tProd (nNamed (ind_name ind_body))
          (mkApps (tInd ind univ)
             (mapi
                (fun (i : nat) (_ : context_decl) =>
                 tRel (#|ind_indices| + (getParamCount ind_body (ind_npars mind_body) - i - 1)))
                (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)) ++
              nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
          (getMaxElim (ind_kelim ind_body)))) ,,,
  rev
    (quantifyCases false
       (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
          (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ,,,
    lift_context (S #|ind_ctors ind_body|) 0 ind_indices |- tInd ind univ : t}.
Proof.
  eexists.
  eapply type_Ind;try eassumption.
  2: apply consistentInstanceExt.
  apply wf_local_app_inv.
  - apply wfLocalQuantifyCases.
  - pose proof wfLocalRelIndices.
    unfold createAppChain, createAppChainOff in X.
    rewrite lift_mkApps in X.
    rewrite mkApps_nested in X.
    rewrite map_mapi in X.
    apply X.
Qed.


Lemma liftIndParams n m:
  lift_context n m (ind_params mind_body) = ind_params mind_body.
Proof.
  pose proof wfSigma as wfSig.
  destruct mind_body.
  cbn.
  clear ind_sorts onProjections onConstructors onArity ind_arity_eq onGuard onNpars onInductives.
  clear findBody nparCount uniP declI.
  clear declM onIndB onInd.
  induction ind_params as [|[? [] ?] ?].
  - reflexivity.
  - pose proof onParams as onParams2.
    inv onParams.
    cbn.
    rewrite mapi_rec_app, rev_unit.
    unfold map_decl.
    f_equal.
    + cbn. f_equal.
      * cbn in X0, X1.
        eapply typed_liftn in X1 as [].
        now rewrite H0.
        -- apply wfSig.
        -- apply X.
        -- rewrite revLen. lia.
      * cbn in X0, X1.
        eapply typed_liftn in X1 as [].
        now rewrite H.
        -- apply wfSig.
        -- apply X.
        -- rewrite revLen. lia.
    + cbn in IHind_params.
      apply IHind_params.
      cbn in onParams2.
      now apply onContextInv in onParams2.
  - pose proof onParams as onParams2.
    inv onParams.
    cbn.
    rewrite mapi_rec_app, rev_unit.
    unfold map_decl.
    cbn.
    destruct X0.
    f_equal.
    + f_equal.
      eapply typed_liftn in t0 as [].
      now rewrite H0.
      * apply wfSig.
      * apply X.
      * rewrite revLen.
        lia.
    + cbn in IHind_params, onParams2.
      apply IHind_params.
      now apply onContextInv in onParams2.
Qed.


Lemma liftIndIndices n m:
  lift_context n (#|ind_params mind_body| + m) ind_indices = ind_indices.
Proof.
  pose proof typingParamInd.
  destruct X.
  eapply typed_liftn with (n0:=n) (k:=m) in t0.
  (* apply typed_liftn with (n0:=n) (k:=#|ind_params mind_body|) in t0. *)
  2: apply wfSigma.
  2: constructor.
  2: cbn;lia.
  destruct t0.
  Check it_mkProd_or_LetIn_app.
  rewrite <- it_mkProd_or_LetIn_app in H0.
  rewrite lift_it_mkProd_or_LetIn in H0.
  cbn in H0.
  apply itMkProdInj in H0.
  unfold lift_context in H0.
  unfold fold_context in H0.
  rewrite rev_app_distr in H0.
  rewrite mapi_app in H0.
  rewrite rev_app_distr in H0.
  unfold lift_context, fold_context.

  apply appInjLen in H0 as [].
  2: {
    unfold mapi.
    now rewrite revLen, mapi_rec_len, revLen.
  }
  rewrite <- H0 at 2.
  f_equal.
  apply mapiExt.
  intros.
  do 2 f_equal.
  rewrite revLen.
  lia.
Qed.

Lemma liftIndType n m: (* m needs only be larger than ind_indices in application *)
  ind_type ind_body = lift n m (ind_type ind_body).
Proof.
  rewrite ind_arity_eq.
  do 2 rewrite lift_it_mkProd_or_LetIn.
  rewrite liftIndParams, liftIndIndices.
  reflexivity.
Qed.

Lemma liftSubstInstanceConstrGen n:
  subst_instance_constr univ (ind_type ind_body) = lift n #|ind_indices| (subst_instance_constr univ (ind_type ind_body)).
Proof.
  rewrite lift_subst_instance_constr.
  f_equal.
  apply liftIndType.
Qed.


Lemma liftSubstInstanceConstr:
  subst_instance_constr univ (ind_type ind_body) = lift (S #|ind_ctors ind_body|) #|ind_indices| (subst_instance_constr univ (ind_type ind_body)).
Proof.
  rewrite lift_subst_instance_constr.
  f_equal.
  apply liftIndType.
Qed.

Lemma typingSpineParamIndexRelLiftet:
  { s &
  typing_spine Σ
    ((Γ ,,, ind_params mind_body),,
     vass (nNamed "p"%string)
       (it_mkProd_or_LetIn ind_indices
          (tProd (nNamed (ind_name ind_body))
             (mkApps ((lift0 #|ind_indices|) (tInd ind univ))
                (mapi
                   (fun (i : nat) (_ : context_decl) =>
                    (lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                 nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                   #|ind_indices|)) (getMaxElim (ind_kelim ind_body)))) ,,,
     rev (quantifyCases false (map (on_snd (Init.Nat.add 0)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ)
     ,,, lift_context (S #|ind_ctors ind_body|) 0 ind_indices) (subst_instance_constr univ (ind_type ind_body))
    (mapi
       (fun (i : nat) (_ : context_decl) =>
        lift (S #|ind_ctors ind_body|) #|ind_indices|
          ((lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1)))) (ind_params mind_body) ++
     map (lift (S #|ind_ctors ind_body|) #|ind_indices|)
       (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a) #|ind_indices|))
    (TemplateTerm.tSort s)}.
Proof.
  pose proof (typingSpineParamIndexRel).
  assert(
mapi
         (fun (i : nat) (_ : context_decl) =>
          lift (S #|ind_ctors ind_body|) #|ind_indices|
            ((lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1)))) (ind_params mind_body) ++
       map (lift (S #|ind_ctors ind_body|) #|ind_indices|)
         (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                  #|ind_indices|) =
map (lift (S #|ind_ctors ind_body|) #|ind_indices|)
(mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
             (ind_params mind_body) ++
           nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)
    ) as ->.
  {
    rewrite map_app.
    f_equal.
    now rewrite map_mapi.
  }
  assert(
(Γ ,,, ind_params mind_body),,
       vass (nNamed "p"%string)
         (it_mkProd_or_LetIn ind_indices
            (tProd (nNamed (ind_name ind_body))
               (mkApps ((lift0 #|ind_indices|) (tInd ind univ))
                  (mapi
                     (fun (i : nat) (_ : context_decl) =>
                      (lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                   nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                     #|ind_indices|)) (getMaxElim (ind_kelim ind_body)))) ,,,
       rev
         (quantifyCases false (map (on_snd (Init.Nat.add 0)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ)
         ,,, lift_context (S #|ind_ctors ind_body|) 0 ind_indices =
(Γ ,,, ind_params mind_body) ,,,
       ([vass (nNamed "p"%string)
         (it_mkProd_or_LetIn ind_indices
            (tProd (nNamed (ind_name ind_body))
               (mkApps ((lift0 #|ind_indices|) (tInd ind univ))
                  (mapi
                     (fun (i : nat) (_ : context_decl) =>
                      (lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                   nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                     #|ind_indices|)) (getMaxElim (ind_kelim ind_body))))] ,,,
       rev
         (quantifyCases false (map (on_snd (Init.Nat.add 0)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ) )
       ,,, lift_context (S #|ind_ctors ind_body|) 0 ind_indices
  ) as ->.
  {
    cbn.
    unfold snoc.
    unfold app_context at 2.
    rewrite <- appCons.
    rewrite app_assoc.
    reflexivity.
  }
  set (x:=subst_instance_univ univ ind_sort).
  exists x.
  assert(TemplateTerm.tSort x = lift (S #|ind_ctors ind_body|) #|ind_indices| (tSort x)) as -> by reflexivity.
  rewrite liftSubstInstanceConstr.
  apply typingSpineLifting.
  - apply X.
  - cbn. unfold app_context.
    rewrite appLen.
    cbn. rewrite revLen.
    rewrite quantifyCasesLen.
    rewrite mapLen.
    lia.
Qed.

Lemma typingLiftAppChain:
  ∑ s : universe,
    Σ;;;
    (Γ ,,,
     skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
       (ind_params mind_body)),,
    vass (nNamed "p"%string)
      (it_mkProd_or_LetIn ind_indices
         (tProd (nNamed (ind_name ind_body))
            (createAppChain
               ((lift0 #|ind_indices|)
                  (mkApps (tInd ind univ)
                     (mapi
                        (fun (i : nat) (_ : context_decl) =>
                         tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                        (skipn
                           (ind_npars mind_body -
                            getParamCount ind_body (ind_npars mind_body))
                           (ind_params mind_body))))) #|ind_indices|)
            (getMaxElim (ind_kelim ind_body)))) ,,,
    rev
      (quantifyCases false
         (map
            (on_snd
               (Init.Nat.add
                  (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
            (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)
    ,,, lift_context (S #|ind_ctors ind_body|) 0 ind_indices
    |- lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
         (createAppChain
            ((lift0 #|ind_indices|)
               (mkApps (tInd ind univ)
                  (mapi
                     (fun (i : nat) (_ : context_decl) =>
                      tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                     (skipn
                        (ind_npars mind_body -
                         getParamCount ind_body (ind_npars mind_body))
                        (ind_params mind_body))))) #|ind_indices|) : 
        TemplateTerm.tSort s.
Proof.
  destruct typingSpineParamIndexRelLiftet.
  eexists.
  unfold createAppChain, createAppChainOff.
  do 3 rewrite lift_mkApps.
  rewrite map_map.
  do 2 rewrite map_mapi.
  do 2 rewrite mkApps_nested.
  rewrite simpl_lift.
  2: cbn.
  2-3: rewrite add_0_r;lia.
  rewrite add_0_r.
  eapply Generation.type_mkApps.
  + cbn.
    eapply type_Ind;try eassumption.
    2: apply consistentInstanceExt.
    apply wf_local_app_inv.
    * apply wfLocalQuantifyCases.
    * pose proof wfLocalRelIndices.
      unfold createAppChain, createAppChainOff in X.
      rewrite lift_mkApps in X.
      rewrite mkApps_nested in X.
      rewrite map_mapi in X.
      apply X.
  + rewrite uniP, sub_diag.
    unfold skipn.
    apply t0.
Qed.


Lemma wfLocalFixEnv:
  wf_local Σ
    (((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
      vass (nNamed "p"%string)
        (it_mkProd_or_LetIn ind_indices
           (tProd (nNamed (ind_name ind_body))
              (createAppChain
                 ((lift0 #|ind_indices|)
                    (mkApps (tInd ind univ)
                       (mapi
                          (fun (i : nat) (_ : context_decl) =>
                           tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                          (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                             (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
      rev
        (quantifyCases false
           (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
              (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ,,,
      lift_context (S #|ind_ctors ind_body|) 0 ind_indices),,
     vass (nNamed (ind_name ind_body))
       (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 #|ind_indices|)
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i : nat) (_ : context_decl) =>
                       tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                      (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                             (ind_params mind_body))))) #|ind_indices|))).
Proof.
  constructor.
  - apply wf_local_app_inv.
    + apply wf_local_app_inv.
      * constructor.
        -- rewrite uniP,sub_diag.
           unfold skipn.
           apply wf_local_app_inv.
           ++ apply Hwf.
           ++ apply wfParams.
        -- cbn.
           destruct maxElimType.
           destruct indAppType.
           destruct typingListIndices.
           eexists.
           apply type_it_mkProd_or_LetIn.
           ++ apply indicesVass.
           ++ apply t2.
           ++ apply type_Prod.
              ** apply t1.
              ** apply t0.
      * rewrite uniP.
        rewrite sub_diag.
        rewrite mapSndAdd0.
        unfold skipn.
        apply wfLocalRelCases.
    + apply wfLocalRelIndices.
  - cbn.
    apply typingLiftAppChain.
Qed.

(* used (wrong) in typingSpineIndices *)
Lemma liftInstIndices:
  vass (nNamed (ind_name ind_body))
    (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
       (createAppChain
          ((lift0 #|ind_indices|)
             (mkApps (tInd ind univ)
                (mapi
                   (fun (i : nat) (_ : context_decl) =>
                    tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                   (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                      (ind_params mind_body))))) #|ind_indices|))
  :: lift_context (S #|ind_ctors ind_body|) 0 ind_indices =
  vass (nNamed (ind_name ind_body))
    (lift (S (#|ind_indices| + S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
       (createAppChain
          ((lift0 #|ind_indices|)
             (mkApps (tInd ind univ)
                (mapi
                   (fun (i : nat) (_ : context_decl) =>
                    tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                   (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                      (ind_params mind_body))))) #|ind_indices|))
    :: lift_context (S (#|ind_indices| + S #|ind_ctors ind_body|)) 0 ind_indices.
Proof.
  admit.
  (* f_equal. *)
  (* - admit. *)
  (* - rewrite liftIndIndices. *)
  (* 1: admit. *)
  (* f_equal. *)
  (* wrong *)
Admitted. (* admit *)


Lemma typingSpineIndices:
  typing_spine Σ
    (((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
      vass (nNamed "p"%string)
        (it_mkProd_or_LetIn ind_indices
           (tProd (nNamed (ind_name ind_body))
              (createAppChain
                 ((lift0 #|ind_indices|)
                    (mkApps (tInd ind univ)
                       (mapi
                          (fun (i : nat) (_ : context_decl) =>
                           tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                          (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                             (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
      rev
        (quantifyCases false
           (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
              (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ,,,
      lift_context (S #|ind_ctors ind_body|) 0 ind_indices),,
     vass (nNamed (ind_name ind_body))
       (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 #|ind_indices|)
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i : nat) (_ : context_decl) =>
                       tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                      (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                         (ind_params mind_body))))) #|ind_indices|)))
    ((lift0 (S (#|ind_indices| + S #|ind_ctors ind_body|)))
       (decl_type
          (vass (nNamed "p"%string)
             (it_mkProd_or_LetIn ind_indices
                (tProd (nNamed (ind_name ind_body))
                   (createAppChain
                      ((lift0 #|ind_indices|)
                         (mkApps (tInd ind univ)
                            (mapi
                               (fun (i : nat) (_ : context_decl) =>
                                tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                               (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                  (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))))))
    (tRel #|ind_indices|
     :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)
    (tSort maxElimSort).
Proof.
  cbn.
  rewrite lift_it_mkProd_or_LetIn.
  cbn.
  rewrite liftMaxElim.
  pose proof getMaxElimSort.
     (* with (ind_body := ind_body). *)
  (* evar (s2:universe). *)
  (* replace 1 with 1. *)
  (* exists s2. *)
  (* eexists. *)
  match goal with
    |- typing_spine _ _ (it_mkProd_or_LetIn ?xs (tProd ?name ?type ?base)) ?rels _ =>
    change (it_mkProd_or_LetIn xs (tProd name type base)) with
      (it_mkProd_or_LetIn (vass name type::xs) base);
    replace rels with (mkRel (vass name type::xs))
  end.
  2: {
    cbn.
    now rewrite lift_context_len.
  }
  unfold snoc, app_context.
  rewrite consMin.
  match goal with
    |- typing_spine _ (?G1 ++ ?G2) (it_mkProd_or_LetIn ?xs ?t) (mkRel ?ys) _ =>
    replace xs with G1
  end.
  2: {
    apply liftInstIndices.
  }
  pose proof typingSpineProdApp.
  unfold snoc, app_context in X.
  apply X.
  cbn.
  rewrite H.
  (* subst s2. *)
  constructor.
Qed.

Lemma typingSpineIndices':
  {s2 &
  typing_spine Σ
    (((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
      vass (nNamed "p"%string)
        (it_mkProd_or_LetIn ind_indices
           (tProd (nNamed (ind_name ind_body))
              (createAppChain
                 ((lift0 #|ind_indices|)
                    (mkApps (tInd ind univ)
                       (mapi
                          (fun (i : nat) (_ : context_decl) =>
                           tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                          (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                             (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
      rev
        (quantifyCases false
           (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
              (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ,,,
      lift_context (S #|ind_ctors ind_body|) 0 ind_indices),,
     vass (nNamed (ind_name ind_body))
       (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 #|ind_indices|)
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i : nat) (_ : context_decl) =>
                       tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                      (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                         (ind_params mind_body))))) #|ind_indices|)))
    ((lift0 (S (#|ind_indices| + S #|ind_ctors ind_body|)))
       (decl_type
          (vass (nNamed "p"%string)
             (it_mkProd_or_LetIn ind_indices
                (tProd (nNamed (ind_name ind_body))
                   (createAppChain
                      ((lift0 #|ind_indices|)
                         (mkApps (tInd ind univ)
                            (mapi
                               (fun (i : nat) (_ : context_decl) =>
                                tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                               (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                  (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))))))
    (tRel #|ind_indices|
     :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)
    (tSort s2)}.
Proof.
  eexists.
  now apply typingSpineIndices.
Qed.


Lemma fixTypeTypes :
  ∑ s : universe,
    Σ;;;
    (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
    vass (nNamed "p"%string)
      (it_mkProd_or_LetIn ind_indices
         (tProd (nNamed (ind_name ind_body))
            (createAppChain
               ((lift0 #|ind_indices|)
                  (mkApps (tInd ind univ)
                     (mapi
                        (fun (i : nat) (_ : context_decl) =>
                         tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                        (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                           (ind_params mind_body))))) #|ind_indices|) (getMaxElim (ind_kelim ind_body)))) ,,,
    rev
      (quantifyCases false
         (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
            (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)
    |- it_mkProd_or_LetIn (lift_context (S #|ind_ctors ind_body|) 0 ind_indices)
         (tProd (nNamed (ind_name ind_body))
            (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
               (createAppChain
                  ((lift0 #|ind_indices|)
                     (mkApps (tInd ind univ)
                        (mapi
                           (fun (i : nat) (_ : context_decl) =>
                            tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                           (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                              (ind_params mind_body))))) #|ind_indices|))
            (tApp (tRel (#|ind_indices| + S #|ind_ctors ind_body|))
               (tRel #|ind_indices|
                :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                     #|ind_indices|))) : TemplateTerm.tSort s.
Proof.
  destruct typingLiftAppChain.
  destruct typingSpineIndices'.
  destruct typingListIndices2.
  eexists.
  apply type_it_mkProd_or_LetIn.
  - apply liftIndicesVass.
  - apply t2.
  - apply type_Prod.
    + apply t0.
      (* apply t0. *)
    + eapply type_App.
      * apply type_Rel.
        -- apply wfLocalFixEnv.
          (* apply wfLocalFixEnv. *)
        -- cbn.
           unfold app_context.
           unfold snoc.
           rewrite <- plus_n_Sm.
           cbn.
           rewrite nth_error_app_ge.
           2: rewrite lift_context_len; lia.
           rewrite nth_error_app_ge.
           2: {
             rewrite revLen, quantifyCasesLen, mapLen, lift_context_len.
             lia.
           }
           assert(
#|ind_indices| + #|ind_ctors ind_body| - #|lift_context (S #|ind_ctors ind_body|) 0 ind_indices| -
     #|rev
         (quantifyCases false
            (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
               (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)| = 0
           ) as ->.
           {
             rewrite revLen, quantifyCasesLen, mapLen, lift_context_len.
             lia.
           }
           cbn.
           reflexivity.
      * reflexivity.
      * congruence.
      * apply t1.
Qed.

Lemma fixEnvWf :
  wf_local Σ
    ((Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
     vass (nNamed "p"%string)
       (replaceLastProd
          (tProd (nNamed (ind_name ind_body))
             (createAppChain
                ((lift0
                    (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                   (mkApps (tInd ind univ)
                      (mapi
                         (fun (i : nat) (_ : context_decl) =>
                          tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                         (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                            (ind_params mind_body)))))
                (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
             (getMaxElim (ind_kelim ind_body)))
          (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))) ,,,
     rev
       (quantifyCases false
          (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
             (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ,,,
     fix_context
       [{|
        dname := nNamed "f"%string;
        dtype := dtype
                   {|
                   dname := nNamed "f"%string;
                   dtype := replaceLastProd'
                              ((lift0 (S #|ind_ctors ind_body|))
                                 (replaceLastProd
                                    (tProd (nNamed (ind_name ind_body))
                                       (createAppChain
                                          ((lift0
                                              (count_prods
                                                 (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                    (ind_type ind_body))))
                                             (mkApps (tInd ind univ)
                                                (mapi
                                                   (fun (i : nat) (_ : context_decl) =>
                                                    tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                                   (skipn
                                                      (ind_npars mind_body -
                                                       getParamCount ind_body (ind_npars mind_body))
                                                      (ind_params mind_body)))))
                                          (count_prods
                                             (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                (ind_type ind_body)))) (getMaxElim (ind_kelim ind_body)))
                                    (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                       (ind_type ind_body))))
                              (createAppChain
                                 (tRel
                                    (count_prods
                                       (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                          (ind_type ind_body)) + S #|ind_ctors ind_body|))
                                 (S
                                    (count_prods
                                       (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                          (ind_type ind_body)))));
                   dbody := replaceLastLambda'
                              (mapProdToLambda
                                 ((lift0 (S (S #|ind_ctors ind_body|)))
                                    (replaceLastProd
                                       (tProd (nNamed "inst"%string)
                                          (createAppChain
                                             ((lift0
                                                 (count_prods
                                                    (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                       (ind_type ind_body))))
                                                (mkApps (tInd ind univ)
                                                   (mapi
                                                      (fun (i : nat) (_ : context_decl) =>
                                                       tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                                      (skipn
                                                         (ind_npars mind_body -
                                                          getParamCount ind_body (ind_npars mind_body))
                                                         (ind_params mind_body)))))
                                             (count_prods
                                                (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                   (ind_type ind_body)))) (getMaxElim (ind_kelim ind_body)))
                                       (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                          (ind_type ind_body)))))
                              (tCase (ind, ind_npars mind_body)
                                 ((lift0
                                     (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                                    (replaceLastLambda'
                                       (mapProdToLambda
                                          (lift (S (S #|ind_ctors ind_body|))
                                             (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                             (remove_arity
                                                (ind_npars mind_body -
                                                 getParamCount ind_body (ind_npars mind_body))
                                                (replaceLastProd
                                                   (tProd (nNamed "inst"%string)
                                                      (createAppChain
                                                         ((lift0
                                                             (count_prods
                                                                (remove_arity
                                                                   (getParamCount ind_body (ind_npars mind_body))
                                                                   (ind_type ind_body))))
                                                            (mkApps (tInd ind univ)
                                                               (mapi
                                                                  (fun (i : nat) (_ : context_decl) =>
                                                                   tRel
                                                                     (getParamCount ind_body (ind_npars mind_body) -
                                                                      i - 1))
                                                                  (skipn
                                                                     (ind_npars mind_body -
                                                                      getParamCount ind_body (ind_npars mind_body))
                                                                     (ind_params mind_body)))))
                                                         (count_prods
                                                            (remove_arity
                                                               (getParamCount ind_body (ind_npars mind_body))
                                                               (ind_type ind_body))))
                                                      (getMaxElim (ind_kelim ind_body)))
                                                   (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                      (ind_type ind_body))))))
                                       (createAppChain
                                          (tRel
                                             (S
                                                (count_prods
                                                   (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                      (ind_type ind_body)) + 1 + #|ind_ctors ind_body|)))
                                          (S
                                             (count_prods
                                                (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                   (ind_type ind_body))))))) (tRel 0)
                                 (mapi
                                    (fun (i : nat) (x : (ident × term) × nat) =>
                                     let (y, count) := x in
                                     let (_, a) := y in
                                     (count,
                                     replaceLastLambda'
                                       ((lift0
                                           (S
                                              (count_prods
                                                 (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                                          (lift (S (S #|ind_ctors ind_body|))
                                             (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                             ((mapProdToLambda (remove_arity (ind_npars mind_body) a))
                                              {ind_npars mind_body := tInd ind univ})))
                                       (createAppChain
                                          (createAppChainOff
                                             (S
                                                (count_prods
                                                   (remove_arity (ind_npars mind_body) (ind_type ind_body)) +
                                                 count))
                                             (tRel
                                                (S
                                                   (count_prods
                                                      (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                         (ind_type ind_body)) + count +
                                                    (#|ind_ctors ind_body| - i))))
                                             (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)))
                                          count))) (ind_ctors ind_body)));
                   rarg := count_prods
                             (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)) |};
        dbody := replaceLastLambda'
                   (mapProdToLambda
                      ((lift0 (S (S #|ind_ctors ind_body|)))
                         (replaceLastProd
                            (tProd (nNamed "inst"%string)
                               (createAppChain
                                  ((lift0
                                      (count_prods
                                         (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                            (ind_type ind_body))))
                                     (mkApps (tInd ind univ)
                                        (mapi
                                           (fun (i : nat) (_ : context_decl) =>
                                            tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                           (skipn
                                              (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                              (ind_params mind_body)))))
                                  (count_prods
                                     (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                        (ind_type ind_body)))) (getMaxElim (ind_kelim ind_body)))
                            (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))))
                   (tCase (ind, ind_npars mind_body)
                      ((lift0 (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                         (replaceLastLambda'
                            (mapProdToLambda
                               (lift (S (S #|ind_ctors ind_body|))
                                  (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                  (remove_arity
                                     (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                     (replaceLastProd
                                        (tProd (nNamed "inst"%string)
                                           (createAppChain
                                              ((lift0
                                                  (count_prods
                                                     (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                        (ind_type ind_body))))
                                                 (mkApps (tInd ind univ)
                                                    (mapi
                                                       (fun (i : nat) (_ : context_decl) =>
                                                        tRel
                                                          (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                                       (skipn
                                                          (ind_npars mind_body -
                                                           getParamCount ind_body (ind_npars mind_body))
                                                          (ind_params mind_body)))))
                                              (count_prods
                                                 (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                    (ind_type ind_body)))) (getMaxElim (ind_kelim ind_body)))
                                        (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                           (ind_type ind_body))))))
                            (createAppChain
                               (tRel
                                  (S
                                     (count_prods
                                        (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                           (ind_type ind_body)) + 1 + #|ind_ctors ind_body|)))
                               (S
                                  (count_prods
                                     (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                        (ind_type ind_body))))))) (tRel 0)
                      (mapi
                         (fun (i : nat) (x : (ident × term) × nat) =>
                          let (y, count) := x in
                          let (_, a) := y in
                          (count,
                          replaceLastLambda'
                            ((lift0 (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                               (lift (S (S #|ind_ctors ind_body|))
                                  (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                  ((mapProdToLambda (remove_arity (ind_npars mind_body) a)) {
                                   ind_npars mind_body := tInd ind univ})))
                            (createAppChain
                               (createAppChainOff
                                  (S
                                     (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)) + count))
                                  (tRel
                                     (S
                                        (count_prods
                                           (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                              (ind_type ind_body)) + count + (#|ind_ctors ind_body| - i))))
                                  (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))) count)))
                         (ind_ctors ind_body)));
        rarg := count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)) |}]).
Proof.
  intros.
  apply wf_local_app_inv.
  - apply wf_local_app_inv.
    + constructor.
      * apply wf_local_app_inv.
        -- apply Hwf.
        -- rewrite uniP.
           rewrite sub_diag.
           unfold skipn.
           eapply wfParams;eassumption.
      * cbn.
        eapply pType;eassumption.
    + rewrite uniP, sub_diag.
      rewrite mapSndAdd0.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: apply nparCount.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      cbn. rewrite revLen.
      eapply wfLocalRelCases;eassumption.
  - cbn.
    constructor.
    + constructor.
    + cbn.
      rewrite lift0_id.
      unfold replaceLastProd'.
      rewrite liftReplaceLastProd.
      rewrite replaceLastProdReplaceLastProd.
      cbn [lift].
      rewrite replaceOneProd.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP.
      rewrite lift_it_mkProd_or_LetIn.
      rewrite replaceUnderItMkProd.
      2: eapply indicesVass;eassumption.
      rewrite replaceUnderItMkProd.
      2: eapply liftIndicesVass;eassumption.
      cbn.
      rewrite liftMaxElim.
      rewrite replaceProdMaxElim.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: eapply indicesVass;eassumption.
      2: cbn;congruence.
      rewrite revLen.
      eapply fixTypeTypes;eassumption.
Qed.

Lemma countLeb :
(S (#|lift_context (S #|Ast.ind_ctors ind_body|) 0 ind_indices| + 0) <=?
count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + S #|Ast.ind_ctors ind_body|) =
true.
Proof.
  intros.
    apply leb_correct.
    rewrite lift_context_len.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: eapply indicesVass;eassumption.
    2: cbn;congruence.
    rewrite revLen.
    lia.
Qed.

Lemma mapTypeErase :
  map (lift 1 (S (#|lift_context (S #|ind_ctors ind_body|) 0 ind_indices| + 0)))
    (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
     :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
          (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) =
  tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
  :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
       (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))).
Proof.
  intros.
  rewrite lift_context_len.
  cbn.
  unfold count_prods.
  rewrite collectProdMkProd, revLen.
  2: eapply indicesVass;eassumption.
  2: cbn;congruence.
  assert (match #|ind_indices| with
      | 0 => false
      | S m' => #|ind_indices| + 0 <=? m'
          end = false) as -> .
  {
    destruct (#|ind_indices|);trivial.
    apply leb_correct_conv.
    lia.
  }
  f_equal.
  apply mapTypeEraseAux.
  lia.
Qed.


  Section caseBodySec.

  Variable
    (caseBody : term)
    (HeqcaseBody : caseBody =
                  tCase (ind, ind_npars mind_body)
                    ((lift0 (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                      (replaceLastLambda
                          (tApp
                            (tRel
                                (S
                                  (count_prods
                                      (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                        (ind_type ind_body)) + 1 + #|ind_ctors ind_body|)))
                            (tRel
                                (count_prods
                                  (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))
                              :: nat_rec (fun _ : nat => list term) []
                                  (fun (n : nat) (a : list term) => tRel n :: a)
                                  (count_prods
                                      (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                        (ind_type ind_body)))))
                          (mapProdToLambda
                            (lift (S (S #|ind_ctors ind_body|))
                                (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                (remove_arity (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                  (replaceLastProd
                                      (tProd (nNamed "inst"%string)
                                        (createAppChain
                                            ((lift0
                                                (count_prods
                                                  (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                      (ind_type ind_body))))
                                              (mkApps (tInd ind univ)
                                                  (mapi
                                                    (fun (i : nat) (_ : context_decl) =>
                                                      tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                                    (skipn
                                                        (ind_npars mind_body -
                                                        getParamCount ind_body (ind_npars mind_body))
                                                        (ind_params mind_body)))))
                                            (count_prods
                                              (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                                  (ind_type ind_body)))) (getMaxElim (ind_kelim ind_body)))
                                      (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                        (ind_type ind_body)))))))) (tRel 0)
                    (mapi
                      (fun (i : nat) (x : (ident × term) × nat) =>
                        let (y, count) := x in
                        let (_, a) := y in
                        (count,
                        replaceLastLambda
                          (createAppChain
                            (createAppChainOff
                                (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)) + count))
                                (tRel
                                  (S
                                      (count_prods
                                        (remove_arity (getParamCount ind_body (ind_npars mind_body))
                                            (ind_type ind_body)) + count + (#|ind_ctors ind_body| - i))))
                                (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))) count)
                          ((lift0 (S (count_prods (remove_arity (ind_npars mind_body) (ind_type ind_body)))))
                            (lift (S (S #|ind_ctors ind_body|))
                                (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                ((mapProdToLambda (remove_arity (ind_npars mind_body) a)) {
                                    ind_npars mind_body := tInd ind univ}))))) (ind_ctors ind_body))
                    ).



  Lemma rewriteCaseEnv :
  replaceLastLambda caseBody
    (mapProdToLambda
       ((lift0 (S (S #|ind_ctors ind_body|)))
          (replaceLastProd
             (tProd (nNamed "inst"%string)
                (createAppChain
                   ((lift0
                       (count_prods
                          (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                      (mkApps (tInd ind univ)
                         (mapi
                            (fun (i : nat) (_ : context_decl) =>
                             tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                            (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                               (ind_params mind_body)))))
                   (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                (getMaxElim (ind_kelim ind_body)))
             (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))) =
  it_mkLambda_or_LetIn (lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices)
    (tLambda (nNamed "inst"%string)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                (mkApps (tInd ind univ)
                   (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                      (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
             (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
       (mapProdToLambda2 caseBody)).
  Proof.
    intros.
    rewrite uniP.
    rewrite ind_arity_eq.
    rewrite removeArityCount.
    2: eapply indParamVass;eassumption.
    2: apply nparCount.
    rewrite replaceUnderItMkProd.
    rewrite replaceMap.
    2: now subst.
    2: {
      cbn.
      rewrite lift_it_mkProd_or_LetIn.
      rewrite removeMkProd.
      2: eapply liftIndicesVass;eassumption.
      cbn.
      maxElimProof.
    }
    2: eapply indicesVass;eassumption.
    do 2 rewrite lift_it_mkProd_or_LetIn.
    cbn.
    rewrite replaceUnderItMkProd.
    2: eapply liftIndicesVass;eassumption.
    rewrite replaceOneProd.
    repeat rewrite liftMaxElim.
    rewrite replaceProdMaxElim.
    rewrite mapMk.
    2: eapply liftIndicesVass;eassumption.
    rewrite <- mapAgreement.
    cbn.
    reflexivity.
  Qed.



  End caseBodySec.


  Lemma rewriteCaseEnvType :
  (lift0 1)
    (replaceLastProd'
       ((lift0 (S #|ind_ctors ind_body|))
          (replaceLastProd
             (tProd (nNamed "inst"%string)
                (createAppChain
                   ((lift0
                       (count_prods
                          (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                      (mkApps (tInd ind univ)
                         (mapi
                            (fun (i : nat) (_ : context_decl) =>
                             tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                            (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                               (ind_params mind_body)))))
                   (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                (getMaxElim (ind_kelim ind_body)))
             (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
       (tApp
          (tRel
             (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)) +
              S #|ind_ctors ind_body|))
          (tRel (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))
           :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))))) =
  it_mkProd_or_LetIn (lift_context (1 + S #|ind_ctors ind_body|) 0 ind_indices)
    (lift 1 (#|lift_context (S #|ind_ctors ind_body|) 0 ind_indices| + 0)
       (tProd (nNamed "inst"%string)
          (lift (S #|ind_ctors ind_body|) (#|ind_indices| + 0)
             (createAppChain
                ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                   (mkApps (tInd ind univ)
                      (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                         (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
          (tApp
             (tRel
                (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) +
                 S #|ind_ctors ind_body|))
             (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
              :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                   (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))))).
  Proof.
    intros.
    unfold replaceLastProd'.
    rewrite uniP.
    rewrite ind_arity_eq.
    rewrite removeArityCount.
    2: eapply indParamVass;eassumption.
    2: apply nparCount.
    rewrite replaceUnderItMkProd.
    2: eapply indicesVass;eassumption.
    rewrite lift_it_mkProd_or_LetIn.
    cbn.
    rewrite replaceUnderItMkProd.
    2: eapply liftIndicesVass;eassumption.
    rewrite replaceOneProd.
    repeat rewrite liftMaxElim.
    rewrite replaceProdMaxElim.
    rewrite lift_it_mkProd_or_LetIn.
    rewrite liftContextSum.
    reflexivity.
  Qed.

  Lemma typingF:
  ∑ s : universe,
    TemplateTyping.typing config.default_checker_flags Σ
      (rev (quantifyCases false (map (on_snd (fun m : nat => m)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ) ++
       vass (nNamed "p"%string)
         (replaceLastProd
            (tProd (nNamed (ind_name ind_body))
               (mkApps (tInd ind univ)
                  (mapi (fun (i : nat) (_ : context_decl) => tRel (#|rev ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                   nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|)) (getMaxElim (ind_kelim ind_body)))
            (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))) :: ind_params mind_body ++ Γ)
      ((lift0 0)
         (replaceLastProd'
            ((lift0 (S #|ind_ctors ind_body|))
               (replaceLastProd
                  (tProd (nNamed (ind_name ind_body))
                     (mkApps (tInd ind univ)
                        (mapi (fun (i : nat) (_ : context_decl) => tRel (#|rev ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                         nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|)) (getMaxElim (ind_kelim ind_body)))
                  (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
            (tApp (tRel (#|rev ind_indices| + S #|ind_ctors ind_body|))
               (tRel #|rev ind_indices| :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|))))
      (TemplateTerm.tSort s).
  Proof.
    destruct fixTypeTypes as [x X].
    exists x.
    match goal with
      |- TemplateTyping.typing _ ?A ?B ?C ?D =>
      change (A ;;; B |- C : D)
    end.
    rewrite replaceUnderItMkProd.
    2: apply indicesVass.
    cbn. rewrite lift_it_mkProd_or_LetIn.
    unfold replaceLastProd'.
    rewrite replaceUnderItMkProd.
    2: apply liftIndicesVass.
    rewrite lift0_id.
    cbn [lift].
    rewrite replaceOneProd.
    rewrite liftMaxElim.
    rewrite replaceProdMaxElim.
    rewrite revLen.
    unfold createAppChain, createAppChainOff in X.
    do 3 rewrite lift_mkApps in X.
    rewrite mkApps_nested in X.
    rewrite mkApps_nested in X.
    rewrite lift_mkApps.
    cbn.
    rewrite map_mapi in X.
    cbn in X.
    rewrite uniP in X.
    rewrite sub_diag in X.
    unfold skipn in X.
    rewrite map_app.
    unfold snoc, app_context in X.
    apply X.
  Qed.


  Lemma wfLocalRelCasesF:
  wf_local_rel Σ
    (rev (quantifyCases false (map (on_snd (fun m : nat => m)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ) ++
     vass (nNamed "p"%string)
       (replaceLastProd
          (tProd (nNamed (ind_name ind_body))
             (mkApps (tInd ind univ)
                (mapi (fun (i : nat) (_ : context_decl) => tRel (#|rev ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                 nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|)) (getMaxElim (ind_kelim ind_body)))
          (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))) :: ind_params mind_body ++ Γ)
    [vass (nNamed "f"%string)
       ((lift0 0)
          (replaceLastProd'
             ((lift0 (S #|ind_ctors ind_body|))
                (replaceLastProd
                   (tProd (nNamed (ind_name ind_body))
                      (mkApps (tInd ind univ)
                         (mapi (fun (i : nat) (_ : context_decl) => tRel (#|rev ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                          nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|))
                      (getMaxElim (ind_kelim ind_body))) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
             (tApp (tRel (#|rev ind_indices| + S #|ind_ctors ind_body|))
                   (tRel #|rev ind_indices| :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|))))].
  Proof.
      constructor.
      * constructor.
      * cbn.
        apply typingF.
  Qed.


Lemma wfLocalCaseEnvEnv:
  wf_local Σ
    ((skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body) ++ Γ) ,,,
     (lift_context (1 + S #|ind_ctors ind_body|) 0 ind_indices ++
      vass (nNamed "f"%string)
        ((lift0 0)
           (replaceLastProd'
              ((lift0 (S #|ind_ctors ind_body|))
                 (replaceLastProd
                    (tProd (nNamed (ind_name ind_body))
                       (mkApps
                          ((lift0
                              #|collect_prods
                                  (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|)
                             (tInd ind univ))
                          (mapi
                             (fun (i : nat) (_ : context_decl) =>
                              (lift0
                                 #|collect_prods
                                     (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|)
                                (tRel (getParamCount ind_body (ind_npars mind_body) - i - 1)))
                             (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                (ind_params mind_body)) ++
                           nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                             #|collect_prods
                                 (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|))
                       (getMaxElim (ind_kelim ind_body)))
                    (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
              (tApp
                 (tRel
                    (#|collect_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))| +
                     S #|ind_ctors ind_body|))
                 (tRel
                    #|collect_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|
                  :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                       #|collect_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|))))
      :: rev
           (quantifyCases false
              (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
                 (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ) ++
         [vass (nNamed "p"%string)
            (replaceLastProd
               (tProd (nNamed (ind_name ind_body))
                  (mkApps
                     ((lift0
                         #|collect_prods
                             (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|)
                        (tInd ind univ))
                     (mapi
                        (fun (i : nat) (_ : context_decl) =>
                         (lift0
                            #|collect_prods
                                (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|)
                           (tRel (getParamCount ind_body (ind_npars mind_body) - i - 1)))
                        (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                           (ind_params mind_body)) ++
                      nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                        #|collect_prods
                            (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))|))
                  (getMaxElim (ind_kelim ind_body)))
               (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))])).
Proof.
  unfold snoc, app_context.
  rewrite <- app_assoc.
  apply wf_local_app_inv.
  - cbn. constructor.
    + pose proof wfLocalQuantifyCases.
      unfold snoc, app_context in X.
      rewrite <- app_assoc.
      cbn.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP, nparCount.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      cbn.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen.
      apply X.
    + cbn.
      pose proof typingF.
      destruct X.
      exists x.
      rewrite <- app_assoc.
      cbn.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP, nparCount.
      rewrite uniP, sub_diag.
      unfold skipn.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      apply t0.
  - pose proof wfLocalRelIndices.
    cbn.
    rewrite appConsNilFront.
    rewrite <- liftContextSucc.
    pose proof weakeningWfLocalRel.
    unfold app_context in X0.
    apply X0.
    4: reflexivity.
    + pose proof wfLocalQuantifyCases.
      unfold snoc, app_context in X1.
      rewrite <- app_assoc.
      cbn.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP, nparCount.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      cbn.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen.
      apply X1.
    + pose proof wfLocalRelCasesF.
      cbn.
      rewrite uniP.
      rewrite sub_diag.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite nparCount.
      rewrite <- app_assoc.
      cbn.
      unfold skipn.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      apply X1.
    + unfold snoc, app_context in X.
      rewrite <- app_assoc.
      cbn.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP, nparCount.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      cbn.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen.
      unfold createAppChain, createAppChainOff in X.
      rewrite lift_mkApps in X.
      rewrite mkApps_nested in X.
      rewrite map_mapi in X.
      apply X.
Qed.

Print typing.

Lemma liftSubstInstanceConstr2:
  lift 1 #|lift_context (S #|ind_ctors ind_body|) 0 ind_indices| (subst_instance_constr univ (ind_type ind_body)) =
  (lift0 (#|ind_indices| + S (#|ind_ctors ind_body| + 1)))
    (subst_instance_constr univ
       (it_mkProd_or_LetIn (ind_params mind_body) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))).
Proof.
  do 2 rewrite lift_subst_instance_constr.
  f_equal.
  rewrite <- ind_arity_eq.
  do 2 rewrite <- liftIndType.
  reflexivity.
Qed.

  Lemma caseEnvHasType :
  ∑ s2 : universe,
    Σ;;;
    (vass (nNamed "f"%string)
       ((lift0 0)
          (replaceLastProd'
             ((lift0 (S #|ind_ctors ind_body|))
                (replaceLastProd
                   (tProd (nNamed (ind_name ind_body))
                      (createAppChain
                         ((lift0
                             (count_prods
                                (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                            (mkApps (tInd ind univ)
                               (mapi
                                  (fun (i : nat) (_ : context_decl) =>
                                   tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                                  (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                                     (ind_params mind_body)))))
                         (count_prods
                            (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                      (getMaxElim (ind_kelim ind_body)))
                   (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
             (tApp
                (tRel
                   (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)) +
                    S #|ind_ctors ind_body|))
                (tRel
                   (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))
                 :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                      (count_prods
                         (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body)))))))
     :: (Γ ,,, skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body)) (ind_params mind_body)),,
        vass (nNamed "p"%string)
          (replaceLastProd
             (tProd (nNamed (ind_name ind_body))
                (createAppChain
                   ((lift0
                       (count_prods
                          (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                      (mkApps (tInd ind univ)
                         (mapi
                            (fun (i : nat) (_ : context_decl) =>
                             tRel (getParamCount ind_body (ind_npars mind_body) - i - 1))
                            (skipn (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))
                               (ind_params mind_body)))))
                   (count_prods (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))))
                (getMaxElim (ind_kelim ind_body)))
             (remove_arity (getParamCount ind_body (ind_npars mind_body)) (ind_type ind_body))) ,,,
        rev
          (quantifyCases false
             (map (on_snd (Init.Nat.add (ind_npars mind_body - getParamCount ind_body (ind_npars mind_body))))
                (ind_ctors ind_body)) (getParamCount ind_body (ind_npars mind_body)) ind univ)) ,,,
    lift_context (1 + S #|ind_ctors ind_body|) 0 ind_indices
    |- lift (1 + S #|ind_ctors ind_body|) (#|ind_indices| + 0)
         (createAppChain
            ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
               (mkApps (tInd ind univ)
                  (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                     (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
            (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) : 
    tSort s2.
  Proof.
    intros.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: eapply indicesVass;eassumption.
    2: cbn;congruence.
    rewrite revLen.
    rewrite sub_diag.
    unfold skipn at 4.
    unfold createAppChain, createAppChainOff.
    do 2 rewrite lift_mkApps.
    rewrite simpl_lift.
    2: {
      rewrite add_0_r.
      constructor.
    }
    2: {
      rewrite add_0_r.
      lia.
    }
    rewrite lift_mkApps.
    do 2 rewrite mkApps_nested.
    do 2 rewrite map_mapi.
    destruct typingSpineParamIndexRelLiftet.
    eexists.
    eapply Generation.type_mkApps.
    -
      unfold snoc, app_context.
      match goal with
        |- _ ;;; ?L1 ++ ?l2 :: ?L3 ++ ?l4 :: ?L5 ++ ?L6 |- _ : _ =>
        remember L1 as Ls1;
        remember l2 as ls2;
        remember L3 as Ls3;
        remember l4 as ls4;
        remember L5 as Ls5;
        remember L6 as Ls6;
        replace (Ls1 ++ ls2 :: Ls3 ++ ls4 :: Ls5 ++ Ls6) with
                ((Ls1 ++ ls2 :: Ls3 ++ [ls4]) ++ (Ls5 ++ Ls6))
      end.
      2: {
        cbn.
        rewrite <- app_assoc.
        f_equal.
        cbn.
        f_equal.
        rewrite <- app_assoc.
        f_equal.
      }
      replace(1 + S #|ind_ctors ind_body| + #|ind_indices|) with (#| Ls1 ++ ls2 :: Ls3 ++ [ls4] |).
      2: {
        subst Ls1 ls2 Ls3 ls4.
        rewrite appLen. cbn.
        rewrite appLen. cbn.
        rewrite revLen, quantifyCasesLen, mapLen.
        rewrite lift_context_len.
        rewrite add_comm.
        cbn. f_equal.
        lia.
      }
      subst Ls1 ls2 Ls3 ls4 Ls5 Ls6.
      eapply weakening.
      + apply wfSigma.
      + apply wfLocalCaseEnvEnv.
      + rewrite uniP, sub_diag.
        unfold skipn.
        eapply type_Ind.
        * apply wf_local_app_inv.
          -- apply Hwf.
          -- apply wfParams.
        * apply declI.
        * apply consistentInstanceExt.
    - instantiate (1 := x).
      unfold snoc, app_context.
      unfold snoc, app_context in t0.
      rewrite appLen, lift_context_len.
      cbn.
      rewrite appLen, revLen, quantifyCasesLen.
      rewrite mapLen.
      cbn.
      rewrite ind_arity_eq.
      rewrite removeArityCount.
      2: eapply indParamVass;eassumption.
      2: now rewrite uniP, nparCount.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen.

      rewrite <- appCons.
      rewrite <- liftContextSucc.
      set (xs:=lift_context (S #|ind_ctors ind_body|) 0 ind_indices).
      replace ((lift0 (#|ind_indices| + S (#|ind_ctors ind_body| + 1)))
       (subst_instance_constr univ
                              (it_mkProd_or_LetIn (ind_params mind_body) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))) with (lift 1 #|xs| (subst_instance_constr univ (ind_type ind_body))).
      2: {
        subst xs.
        apply liftSubstInstanceConstr2.
      }
      replace (tSort x) with (lift 1 #|xs| (tSort x)) by reflexivity.
      replace (mapi
       (fun (i : nat) (_ : context_decl) =>
        tRel (S (S (#|ind_ctors ind_body| + #|ind_indices| + (ind_npars mind_body - i - 1)))))
       (ind_params mind_body) ++
     map (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0))
     (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
        with
          (map (lift 1 #|xs| )
          (mapi
            (fun (i : nat) (_ : context_decl) =>
             lift (S #|ind_ctors ind_body|) #|ind_indices|
               ((lift0 #|ind_indices|) (tRel (ind_npars mind_body - i - 1)))) (ind_params mind_body) ++
          map (lift (S #|ind_ctors ind_body|) #|ind_indices|)
            (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                     #|ind_indices|))).
      2: {
        rewrite map_app.
        rewrite map_mapi.
        rewrite map_map.
        subst xs.
        rewrite lift_context_len.
        f_equal.
        - apply mapiExt. intros.
          rewrite simpl_lift.
          + rewrite simpl_lift.
            * reflexivity.
            * constructor.
            * lia.
          + lia.
          + constructor.
        - cbn.
          apply mapExt.
          intros.
          rewrite simpl_lift.
          + rewrite add_0_r.
            reflexivity.
          + lia.
          + constructor.
      }
      subst xs.
      pose proof typingSpineLifting.
      unfold app_context in X.
      apply X.
      2: reflexivity.
      rewrite uniP, nparCount, sub_diag.
      unfold skipn.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      (* cbn. *)
      (* cbn in t0. *)
      (* change (tSort x) with (TemplateTerm.tSort x). *)
      rewrite nparCount in t0.
      apply t0.
  Qed.

  Section matchSec.


    Variable
  (Env : list Ast.context_decl)
  (HeqEnv : Env =
           ((Ast.vass (nNamed "f"%string)
               ((lift0 0)
                  (replaceLastProd'
                     ((lift0 (S #|Ast.ind_ctors ind_body|))
                        (replaceLastProd
                           (tProd (nNamed (ind_name ind_body))
                              (createAppChain
                                 ((lift0
                                     (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                                    (mkApps (tInd ind univ)
                                       (mapi
                                          (fun (i : nat) (_ : Ast.context_decl) =>
                                           tRel (ind_npars mind_body - i - 1))
                                          (skipn (Ast.ind_npars mind_body - ind_npars mind_body)
                                             (Ast.ind_params mind_body)))))
                                 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                              (getMaxElim (Ast.ind_kelim ind_body)))
                           (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                     (tApp
                        (tRel
                           (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) +
                            S #|Ast.ind_ctors ind_body|))
                        (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
                         :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                              (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
             :: (Γ ,,, skipn (Ast.ind_npars mind_body - ind_npars mind_body) (Ast.ind_params mind_body)),,
                Ast.vass (nNamed "p"%string)
                  (replaceLastProd
                     (tProd (nNamed (ind_name ind_body))
                        (createAppChain
                           ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                              (mkApps (tInd ind univ)
                                 (mapi
                                    (fun (i : nat) (_ : Ast.context_decl) => tRel (ind_npars mind_body - i - 1))
                                    (skipn (Ast.ind_npars mind_body - ind_npars mind_body)
                                       (Ast.ind_params mind_body)))))
                           (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                        (getMaxElim (Ast.ind_kelim ind_body)))
                     (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))) ,,,
                rev
                  (quantifyCases false
                     (map (on_snd (Init.Nat.add (Ast.ind_npars mind_body - ind_npars mind_body)))
                        (Ast.ind_ctors ind_body)) (ind_npars mind_body) ind univ)) ,,,
            lift_context (S (S #|Ast.ind_ctors ind_body|)) 0 ind_indices),,
           Ast.vass (nNamed "inst"%string)
             (lift (S (S #|Ast.ind_ctors ind_body|)) (#|ind_indices| + 0)
                (createAppChain
                   ((lift0 (count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                      (mkApps (tInd ind univ)
                         (mapi (fun (i : nat) (_ : Ast.context_decl) => tRel (Ast.ind_npars mind_body - i - 1))
                            (skipn (Ast.ind_npars mind_body - Ast.ind_npars mind_body) (Ast.ind_params mind_body)))))
                   (count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))))
  (retType : term)
  (HeqretType : retType =
               tApp
                 (tRel
                    (S
                       (count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) +
                        S #|Ast.ind_ctors ind_body|)))
                 (tRel (count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
                  :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                       (count_prods (Ast.it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
  (matchObj : term)
  (HeqmatchObj : matchObj = tRel 0).

Lemma matchTypeSimpl :
  (lift0 (S (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
    (replaceLastLambda retType
       (mapProdToLambda
          (lift (S (S #|Ast.ind_ctors ind_body|)) (Ast.ind_npars mind_body - ind_npars mind_body)
             (remove_arity (Ast.ind_npars mind_body - ind_npars mind_body)
                (replaceLastProd
                   (tProd (nNamed "inst"%string)
                      (createAppChain
                         ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                            (mkApps (tInd ind univ)
                               (mapi (fun (i : nat) (_ : Ast.context_decl) => tRel (ind_npars mind_body - i - 1))
                                  (skipn (Ast.ind_npars mind_body - ind_npars mind_body)
                                     (Ast.ind_params mind_body)))))
                         (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                      (getMaxElim (Ast.ind_kelim ind_body)))
                   (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))))) =
  it_mkLambda_or_LetIn (lift_context (S #|ind_indices| + S (S #|Ast.ind_ctors ind_body|)) 0 ind_indices)
    (lift (S #|ind_indices|) (#|lift_context (S (S #|Ast.ind_ctors ind_body|)) 0 ind_indices| + 0)
       (tLambda (nNamed "inst"%string)
          (lift (S (S #|Ast.ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i : nat) (_ : Ast.context_decl) =>
                       tRel (#|ind_indices| + (ind_npars mind_body - i - 1))) (Ast.ind_params mind_body)))
                #|ind_indices|)) retType)).
Proof.
  intros.
  rewrite minus_diag.
  rewrite replaceUnderItMkProd.
  2: eapply indicesVass;eassumption.
  rewrite replaceMap.
  2: subst;cbn;congruence.
  2: {
    cbn.
    rewrite lift_it_mkProd_or_LetIn.
    rewrite removeMkProd.
    2: eapply liftIndicesVass;eassumption.
    cbn.
    rewrite liftMaxElim.
    rewrite removeProdMaxElim.
    apply noLambdaMaxElim.
  }
  cbn [remove_arity].
  rewrite lift_it_mkProd_or_LetIn.
  rewrite replaceLastProdNotProd with (t:=(tSort _)).
  2: cbn;congruence.
  cbn [lift].
  rewrite liftMaxElim.
  rewrite replaceUnderItMkProd.
  2: eapply liftIndicesVass;eassumption.
  rewrite replaceOneProd.
  rewrite replaceProdMaxElim.
  unfold count_prods.
  rewrite collectProdMkProd.
  2: eapply indicesVass;eassumption.
  2: cbn;congruence.
  rewrite revLen.
  unfold skipn.
  rewrite lift_mkApps.
  rewrite map_mapi.
  cbn.
  rewrite mapMk.
  2: eapply liftIndicesVass;eassumption.
  rewrite <- mapAgreement.
  cbn.
  assert(mapProdToLambda2 retType=retType) as ->.
  {
    subst.
    reflexivity.
  }
  rewrite lift_it_mkLambda_or_LetIn.
  rewrite liftContextSum.
  reflexivity.
Qed.

    Variable
    (matchType : term)
    (HeqmatchType : matchType =
    it_mkLambda_or_LetIn
    (lift_context (S #|ind_indices| + S (S #|Ast.ind_ctors ind_body|)) 0 ind_indices)
    (lift (S #|ind_indices|)
    (#|lift_context (S (S #|Ast.ind_ctors ind_body|)) 0 ind_indices| + 0)
    (tLambda (nNamed (ind_name ind_body))
    (lift (S (S #|Ast.ind_ctors ind_body|)) (#|ind_indices| + 0)
    (createAppChain
    (mkApps (tInd ind univ)
    (mapi
    (fun (i : nat) (_ : Ast.context_decl) =>
    tRel (#|ind_indices| + (Ast.ind_npars mind_body - i - 1)))
    (Ast.ind_params mind_body))) #|ind_indices|)) retType))).


    Print type_Case.
    (*

  | type_Case : forall (indnpar : inductive × nat) (u : universe_instance) (p c : term) 
                  (brs : list (nat × term)) (args : list term),
                let ind := indnpar.1 in
                let npar := indnpar.2 in
                forall (mdecl : TemplateEnvironment.mutual_inductive_body)
                  (idecl : TemplateEnvironment.one_inductive_body),
                declared_inductive Σ.1 mdecl ind idecl ->
                ind_npars mdecl = npar ->
                let params := firstn npar args in
                forall (ps : universe) (pty : term),
                build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
                Σ;;; Γ |- p : pty ->
                existsb (leb_sort_family (universe_family ps)) (ind_kelim idecl) ->
                Σ;;; Γ |- c : mkApps (tInd ind u) args ->
                forall btys : list (nat × term),
                map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
                All2
                  (fun br bty : nat × term => (br.1 = bty.1 × Σ;;; Γ |- br.2 : bty.2) × Σ;;; Γ |- bty.2 : tSort ps)
                  brs btys -> Σ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c])

     *)

    (*
      matchObj has Type
tInd ind u applied with the args
and in p something of type matchObj is taken (lambda)
params = firstn npar args (args is params ++ ...)

     *)

    Print Env.

    Lemma retTypeLifting:
      lift (S #|ind_indices|) (S #|ind_indices|) retType = retType.
    Proof.
      subst retType.
    Admitted. (* admit *)

    Print type_Case.


Lemma mkAppsExt:
  (* mkApps (tInd ind univ) (map decl_type (ind_params mind_body)) = *)
  (* (lift0 1) *)
  (*   (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0) *)
  (*      (createAppChain *)
  (*         ((lift0 #|ind_indices|) *)
  (*            (mkApps (tInd ind univ) *)
  (*               (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1)) *)
  (*                     (ind_params mind_body)))) #|ind_indices|)). *)
  mkApps (tInd ind univ)
         (map decl_type (
map (vass nAnon)
(map (lift0 (3 + #|ind_ctors ind_body| + #|ind_indices|)) (mkRel (ind_params mind_body)))
              ) ++
     map (lift0 1)
       (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)) =
  (lift0 1)
    (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
       (createAppChain
          ((lift0 #|ind_indices|)
             (mkApps (tInd ind univ)
                (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                   (ind_params mind_body)))) #|ind_indices|)).
Proof.
    (* same as in etaConvRetType3 *)
  (* need to change decl_type params to that on the right hand side *)
  unfold createAppChain, createAppChainOff.
  rewrite lift_mkApps.
  rewrite add_0_r.
  rewrite simpl_lift.
  2-3:cbn;lia.
  rewrite lift_mkApps.
  (* rewrite liftMkRel at 2. *)
  replace (map (lift (S (S #|ind_ctors ind_body|)) #|ind_indices|)
          (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
                   #|ind_indices|)) with (
nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a)
        #|ind_indices|).
  2: {
    symmetry.
    apply liftMkRel.
    constructor.
  }
  do 2 rewrite lift_mkApps.
  do 2 rewrite map_mapi.
  cbn.
  rewrite mkApps_nested.
  do 2 f_equal.
  cbn.
  match goal with
    |- _ = ?H =>
    replace H with (map (lift0 (3+#|ind_ctors ind_body|+#|ind_indices|)) (mkRel (ind_params mind_body)))
  end.
  2: {
    rewrite mapiNatRec, map_mapi.
    cbn.
    rewrite nparCount.
    reflexivity.
  }
  now rewrite mapDeclVass.
Qed.


Lemma wfLocalMatchObjEnv:
  wf_local Σ
    (((vass (nNamed "f"%string)
         ((lift0 0)
            (replaceLastProd'
               ((lift0 (S #|ind_ctors ind_body|))
                  (replaceLastProd
                     (tProd (nNamed (ind_name ind_body))
                        (createAppChain
                           ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                              (mkApps (tInd ind univ)
                                 (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                    (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                           (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                        (getMaxElim (ind_kelim ind_body)))
                     (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
               (tApp
                  (tRel
                     (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) +
                      S #|ind_ctors ind_body|))
                  (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
                   :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                        (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
       :: (Γ ,,, skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)),,
          vass (nNamed "p"%string)
            (replaceLastProd
               (tProd (nNamed (ind_name ind_body))
                  (createAppChain
                     ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                        (mkApps (tInd ind univ)
                           (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                              (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                     (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                  (getMaxElim (ind_kelim ind_body))) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
          ,,,
          rev
            (quantifyCases false
               (map (on_snd (Init.Nat.add (ind_npars mind_body - ind_npars mind_body))) (ind_ctors ind_body))
               (ind_npars mind_body) ind univ)) ,,, lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices),,
     vass (nNamed "inst"%string)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                (mkApps (tInd ind univ)
                   (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                      (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
             (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))).
Proof.
  pose proof wfLocalCaseEnvEnv.
  unfold snoc, app_context.
  unfold snoc, app_context in X.
  constructor.
  -
    rewrite uniP in X.
    rewrite sub_diag.
    unfold count_prods.
    rewrite sub_diag in X.
    rewrite collectProdMkProd.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite ind_arity_eq in X.
    rewrite removeArityCount in X.
    2: eapply indParamVass;eassumption.
    2: apply nparCount.
    rewrite collectProdMkProd in X.
    2: apply indicesVass.
    2: cbn;congruence.
    unfold createAppChain, createAppChainOff.
    cbn.
    rewrite lift_mkApps.
    rewrite map_mapi.
    cbn in X.
    rewrite mkApps_nested.
    revert X.
    match goal with
      |- wf_local _ ?B -> wf_local _ ?A => replace A with B
    end.
    2: {
      match goal with
        |- (?Ls1 ++ ?ls2 :: ?Ls3 ++ [?ls4] ) ++ ?Ls5 ++ _ = _ =>
        remember Ls1 as L1;
        remember ls2 as l2;
        remember Ls3 as L3;
        remember ls4 as l4;
        remember Ls5 as L5
      end.
      match goal with
        |- _ = _ ++ ?ls2' :: _ ++ ?ls4' :: _ ++ _ =>
        remember ls2' as l2';
        remember ls4' as l4'
      end.
      rewrite <- app_assoc.
      cbn.
      rewrite app_assoc.
      f_equal.
      f_equal.
      1: subst; repeat f_equal.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      cbn.
      repeat f_equal.
      subst.
      repeat f_equal.
    }
    trivial.
  - cbn.
    pose proof caseEnvHasType.
    unfold snoc, app_context in X0.
    destruct X0.
    exists x.
    rewrite ind_arity_eq in t0.
    rewrite removeArityCount in t0.
    2: eapply indParamVass;eassumption.
    2: now rewrite uniP, nparCount.
    rewrite uniP in t0.
    apply t0.
Qed.


(* see mkAppsExt for correct decl_type ind_params *)
(*
map (vass nAnon)
(map (lift0 (3 + #|ind_ctors ind_body| + #|ind_indices|)) (mkRel (ind_params mind_body)))

old:
ind_params mind_body
 *)
Lemma etaConvRetType3 t:
  Σ;;;Env |- t : mkApps matchType (skipn (ind_npars mind_body) (
                                          map decl_type (
map (vass nAnon)
(map (lift0 (3 + #|ind_ctors ind_body| + #|ind_indices|)) (mkRel (ind_params mind_body)))
                                              ) ++
                                              map (lift0 (S 0)) (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                       #|ind_indices|)) ++ [matchObj]) ->
  Σ;;;Env |- t : retType.
Proof.
  (* rewrite <- map_skipn. *)
  rewrite nparCount.
  rewrite mapDeclVass.
  erewrite <- mapi_rec_len.
  rewrite mapiNatRec.
  unfold mapi.
  erewrite <- mapLen.
  rewrite skipnApp.

  pose proof wfLocalMatchObjEnv as HwfMatchObj.

  pose proof retTypeLifting as HretLift.
  subst matchType.
  pose proof etaConvTypeGen.
  cbn.
  (* subst retType. *)
  rewrite lift_context_len.
  rewrite add_0_r.
  rewrite simpl_lift.
  2-3: lia.
  unfold count_prods in HeqretType.
  rewrite collectProdMkProd in HeqretType.
  2: apply indicesVass.
  2: cbn;congruence.
  rewrite revLen in HeqretType.
  match goal with
    |- _;;;_ |- _ : mkApps (it_mkLambda_or_LetIn (?xs) (tLambda ?na ?ty ?body)) ?ys -> _ =>
    change (it_mkLambda_or_LetIn xs (tLambda na ty body)) with
              (it_mkLambda_or_LetIn (vass na ty :: xs) body);
      replace ys with (rev(rev ys)) by apply revRev
  end.
  rewrite HretLift.
  apply X.
  1: {
    intros x [].
    - subst x. reflexivity.
    - eapply liftIndicesVass,H.
  }
  rewrite rev_unit.
  constructor.
  - subst matchObj Env.
    Check type_Rel.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: apply indicesVass.
    2: cbn;trivial.
    rewrite sub_diag.
    unfold skipn.
    rewrite revLen.
    rewrite lift_mkApps, map_mapi.
    cbn.
    match goal with
      |- _;;;_ |- _ : ?T =>
      replace T with (lift0 (S 0)
                            (
decl_type
      (vass (nNamed "inst"%string)
         (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
       (createAppChain
          (mkApps (tInd ind univ)
             (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                (ind_params mind_body))) #|ind_indices|)))
                            )
                     )
    end.
    2: {
      cbn.
      (* see mkAppsExt. *)

      (* pose proof mkAppsExt. *)
      (* rewrite lift_mkApps, map_mapi in H. *)
      (* cbn in H. *)
      (* rewrite  <- H. *)

      (* unfold createAppChain, createAppChainOff. *)
      (* rewrite mkApps_nested. *)
      (* do 3 rewrite lift_mkApps. *)
      (* repeat rewrite map_app. *)
      (* repeat rewrite map_mapi. *)
      (* cbn. *)
      (* f_equal. *)
      (* f_equal. *)

      (* problem: createAppChain is under indices *)
      admit.
    }
    eapply type_Rel.
    + unfold snoc, app_context.
      uniapply HwfMatchObj.
      f_equal_wf_local.
      unfold snoc, app_context.
      cbn.
      rewrite sub_diag.
      unfold skipn.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;trivial.
      rewrite revLen.
      rewrite lift_mkApps,map_mapi.
      reflexivity.
    + reflexivity.
      (* cbn. f_equal. *)
      (* f_equal. *)
      (* f_equal. *)
      (* 2: lia. *)
      (* 2: { *)
      (*   unfold count_prods. *)
      (*   rewrite collectProdMkProd. *)
      (*   3: cbn;trivial. *)
      (*   2: apply indicesVass. *)
      (*   f_equal. *)
      (*   2: apply revLen. *)
      (*   rewrite lift_mkApps. *)
      (*   cbn. *)
      (*   rewrite revLen. *)
      (*   rewrite map_mapi. *)
      (*   rewrite sub_diag. *)
      (*   unfold skipn. *)
      (*   reflexivity. *)
      (* } *)
      (* admit. (* wrong position *) *)
  - unfold snoc, app_context in HeqEnv.
    admit.

  Print it_mkProd_or_LetIn.
  (* Print type_Case. *)

  (* rewrite <- mkApps_nested. *)

  (* rewrite mkApps_app. *)

  (* cbv [lift]. *)

  (* eapply etaConvTypeGen. *)
Admitted. (* TODO *)

(* Lemma etaConvRetType2 Σ2 Γ2 t: *)
(*   Σ2;;;Γ2 |- t : mkApps matchType (skipn (ind_npars mind_body) (map decl_type (ind_params mind_body ++ ind_indices)) ++ [matchObj]) -> *)
(*   Σ2;;;Γ2 |- t : retType. *)
(* Proof. *)
(*   rewrite <- map_skipn. *)
(*   subst matchType. *)
(*   pose proof etaConvTypeGen. *)
(*   cbn. *)
(*   (* subst retType. *) *)
(*   rewrite lift_context_len. *)
(*   rewrite add_0_r. *)
(*   rewrite simpl_lift. *)
(*   2-3: lia. *)
(*   unfold count_prods in HeqretType. *)
(*   rewrite collectProdMkProd in HeqretType. *)
(*   2: apply indicesVass. *)
(*   2: cbn;congruence. *)
(*   rewrite revLen in HeqretType. *)
(*   rewrite nparCount. *)
(*   rewrite skipnApp. *)
(*   Print type_Case. *)

(*   (* rewrite <- mkApps_nested. *) *)

(*   (* rewrite mkApps_app. *) *)

(*   (* cbv [lift]. *) *)

(*   (* eapply etaConvTypeGen. *) *)
(* Admitted. (* TODO *) *)


(* Lemma etaConvRetType Σ2 Γ2 t: *)
(*   Σ2;;;Γ2 |- t : mkApps matchType (skipn (ind_npars mind_body) (map decl_type (ind_params mind_body)) ++ [matchObj]) -> *)
(*   Σ2;;;Γ2 |- t : retType. *)
(* Proof. *)
(*   rewrite <- map_skipn. *)
(*   subst matchType. *)
(*   pose proof etaConvTypeGen. *)
(*   cbn. *)
(*   (* subst retType. *) *)
(*   rewrite lift_context_len. *)
(*   rewrite add_0_r. *)
(*   rewrite simpl_lift. *)
(*   2-3: lia. *)
(*   unfold count_prods in HeqretType. *)
(*   rewrite collectProdMkProd in HeqretType. *)
(*   2: apply indicesVass. *)
(*   2: cbn;congruence. *)
(*   rewrite revLen in HeqretType. *)
(*   (* rewrite <- mkApps_nested. *) *)

(*   (* rewrite mkApps_app. *) *)

(*   (* cbv [lift]. *) *)

(*   (* eapply etaConvTypeGen. *) *)
(* Admitted. (* TODO *) *)


(* wrong in this formulation *)
(* idea:
   Σ;Γ ⊢ e : t ↔
   Σ;Γ ⊢ e : (λ x. t) x
 *)
(* Lemma etaConvRetType : *)
(*   retType = mkApps matchType (skipn (ind_npars mind_body) (map decl_type (ind_params mind_body)) ++ [matchObj]). *)
(* Proof. *)
(*   intros. *)
(*   Print red1. *)
(* A dmitted. (* admit *) *)



Lemma wfLocalMatchTypeEnv:
  wf_local Σ
    ((lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices ++
      [vass (nNamed "inst"%string)
         (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
            (mkApps ((lift0 #|rev ind_indices|) (tInd ind univ))
               (mapi (fun (i : nat) (_ : context_decl) => (lift0 #|rev ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a) #|rev ind_indices|)))]) ++
     lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices ++
     vass (nNamed "f"%string)
       ((lift0 0)
          (replaceLastProd'
             ((lift0 (S #|ind_ctors ind_body|))
                (replaceLastProd
                   (tProd (nNamed (ind_name ind_body))
                      (mkApps ((lift0 #|rev ind_indices|) (tInd ind univ))
                         (mapi (fun (i : nat) (_ : context_decl) => (lift0 #|rev ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                          nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a) #|rev ind_indices|)) (getMaxElim (ind_kelim ind_body)))
                   (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
             (tApp (tRel (#|rev ind_indices| + S #|ind_ctors ind_body|))
                (tRel #|rev ind_indices| :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|rev ind_indices|))))
     :: rev (quantifyCases false (map (on_snd (Init.Nat.add 0)) (ind_ctors ind_body)) (ind_npars mind_body) ind univ) ++
        vass (nNamed "p"%string)
          (replaceLastProd
             (tProd (nNamed (ind_name ind_body))
                (mkApps ((lift0 #|rev ind_indices|) (tInd ind univ))
                   (mapi (fun (i : nat) (_ : context_decl) => (lift0 #|rev ind_indices|) (tRel (ind_npars mind_body - i - 1))) (ind_params mind_body) ++
                    nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel (0 + n) :: a) #|rev ind_indices|)) (getMaxElim (ind_kelim ind_body)))
             (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))) :: ind_params mind_body ++ Γ).
Proof.
  unfold snoc, app_context.
  pose proof wfLocalMatchObjEnv.
  unfold snoc, app_context in X.
  rewrite <- app_assoc.
  apply wf_local_app_inv.
  - cbn.
    unfold createAppChain, createAppChainOff in X.
    rewrite lift_mkApps in X.
    rewrite lift_mkApps in X.
    rewrite mkApps_nested, map_mapi in X.
    unfold count_prods in X.
    rewrite collectProdMkProd in X.
    2: apply indicesVass.
    2: cbn;congruence.
    cbn in X.
    rewrite sub_diag in X.
    unfold skipn in X.
    rewrite lift_mkApps.
    cbn.
    cbn in X.
    rewrite lift_mkApps in X.
    rewrite mkApps_nested in X.
    rewrite map_mapi in X.
    rewrite map_app.
    rewrite map_mapi.
    apply X.
  - pose proof wfLocalRelIndices.
    replace (lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices) with
        (lift_context (S (S (#|ind_indices|))) 0 (lift_context (S #|ind_ctors ind_body|) 0 ind_indices)).
    2: {
      rewrite liftContextSum.
      f_equal.
      lia.
    }
    match goal with
      |- wf_local_rel _ (?Ls1 ++ ?Ls2 ++ ?ls3 :: ?Ls4 ++ ?ls5 :: ?Ls6 ++ ?Ls7) _ =>
      remember Ls1 as L1;
      remember Ls2 as L2;
      remember ls3 as l3;
      remember Ls4 as L4;
      remember ls5 as l5;
      remember Ls6 as L6;
      remember Ls7 as L7
    end.
    replace (L1++L2++l3::L4++l5::L6++L7) with
        ((L1++L2++[l3])++L4++l5::L6++L7).
    2: {
      do 2 rewrite <- app_assoc.
      now rewrite appCons.
    }
    subst L1 L2 l3 L4 l5 L6 L7.
    apply weakeningWfLocalRel.
    + pose proof wfLocalQuantifyCases.
      unfold snoc, app_context in X1.
      rewrite uniP, sub_diag in X1.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      unfold skipn in X1.
      cbn.
      rewrite revLen.
      apply X1.
    + cbn.
      apply wf_local_rel_abs.
      * apply wf_local_rel_app_inv.
        -- constructor.
           ++ constructor.
           ++ cbn.
              destruct typingF.
              exists x.
              match goal with
                |- TemplateTyping.typing _ ?A ?B ?C ?D => change (A ;;; B |- C : D)
              end.
              apply t0.
        -- pose proof wfLocalRelIndices.
           unfold snoc, app_context in X1.
           unfold snoc, app_context.
           rewrite <- liftContextSucc.
           pose proof weakeningWfLocalRel.
           unfold snoc, app_context in X2.
           apply X2.
           ++ pose proof wfLocalQuantifyCases.
              unfold snoc, app_context in X3.
              rewrite uniP, sub_diag in X3.
              rewrite replaceUnderItMkProd.
              2: apply indicesVass.
              unfold skipn in X3.
              cbn.
              rewrite revLen.
              apply X3.
           ++ apply wfLocalRelCasesF.
           ++ unfold snoc, app_context in X1.
              rewrite uniP, sub_diag in X1.
              rewrite replaceUnderItMkProd.
              2: apply indicesVass.
              unfold skipn in X1.
              cbn.
              rewrite revLen.
              unfold createAppChain, createAppChainOff in X1.
              rewrite lift_mkApps in X1.
              rewrite map_mapi in X1.
              rewrite mkApps_nested in X1.
              apply X1.
           ++ reflexivity.
      *
        pose proof (indAppType).
        destruct X1.
        pose proof typingSpineIndices2 as t1.
        set (x0 := subst_instance_univ univ ind_sort).
        exists x0.
        match goal with
          |- TemplateTyping.typing _ ?A ?B ?C ?D =>
          change (A ;;; B |- C : D)
        end.
        unfold createAppChain, createAppChainOff in t0.
        rewrite lift_mkApps in t0.
        rewrite mkApps_nested in t0.
        rewrite map_mapi in t0.
        cbn in t0.
        rewrite revLen.
        unfold snoc, app_context.
        rewrite uniP in t0.
        rewrite sub_diag in t0.
        unfold skipn in t0.

        rewrite lift_mkApps.
        eapply Generation.type_mkApps.
        -- cbn. eapply type_Ind;try eassumption.
           ++ pose proof wfLocalCaseEnvEnv.
              rewrite uniP, sub_diag, ind_arity_eq, removeArityCount, collectProdMkProd in X1.
              2: apply indicesVass.
              2: cbn;congruence.
              2: eapply indParamVass;eassumption.
              2: apply nparCount.
              unfold snoc, app_context, skipn in X1.
              rewrite <- app_assoc.
              rewrite <- app_assoc in X1.
              cbn.
              rewrite revLen in X1.
              cbn in X1.
              rewrite <- app_assoc in X1.
              apply X1.
           ++ apply consistentInstanceExt.
        -- rewrite add_0_r.
           rewrite liftSubstInstanceConstrGen with (n:=S (S #|ind_ctors ind_body|)).
           change (TemplateTerm.tSort x0) with (lift (S (S #|ind_ctors ind_body|)) #|ind_indices| (tSort x0)).
           match goal with
             |- typing_spine _ ((?Ls1 ++ ?ls2) ++ ?Ls3 ++ ?ls4 :: ?Ls5 ++ ?Ls6) _ _ _ =>
             remember Ls1 as L1;
             remember ls2 as l2;
             remember Ls3 as L3;
             remember ls4 as l4;
             remember Ls5 as L5;
             remember Ls6 as L6
           end.
           replace ((L1 ++ l2) ++ L3 ++ l4 :: L5 ++ L6) with (L1 ++ (l2 ++ L3 ++ [l4]) ++ (L5 ++ L6) ).
           2: {
             repeat rewrite <- app_assoc.
             reflexivity.
           }
           pose proof typingSpineLifting.
           unfold snoc, app_context in X1.
           subst L1.
           subst l2 L3 l4 L5 L6.
           apply X1.
           2: {
             cbn.
             rewrite appLen, revLen, quantifyCasesLen.
             cbn.
             rewrite mapLen. lia.
           }
           apply t1.
    + clear X.
      unfold snoc, app_context in X0.
      rewrite uniP in X0.
      rewrite sub_diag in X0.
      rewrite replaceUnderItMkProd.
      2: apply indicesVass.
      unfold skipn in X0.
      unfold createAppChain, createAppChainOff in X0.
      rewrite lift_mkApps in X0.
      rewrite mkApps_nested in X0.
      rewrite map_mapi in X0.
      cbn.
      cbn in X0.
      rewrite revLen.
      apply X0.
    + cbn. rewrite appLen, lift_context_len.
      cbn. lia.
Qed.

Lemma wfLocalEnv:
  wf_local Σ Env.
Proof.
  rewrite HeqEnv.
  apply wfLocalMatchObjEnv.
Qed.

(* Lemma liftAfterIndices: *)
(*   (lift0 (S #|ind_indices|)) *)
(*     (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0) *)
(*        (createAppChain *)
(*           (mkApps (tInd ind univ) *)
(*              (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body))) *)
(*           #|ind_indices|)) = *)
(*   lift (S #|ind_indices|) (#|ind_indices| + 0) *)
(*     (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0) *)
(*        (createAppChain *)
(*           (mkApps (tInd ind univ) *)
(*              (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body))) *)
(*           #|ind_indices|)). *)
(* Proof. *)
(*   unfold createAppChain, createAppChainOff. *)
(*   rewrite mkApps_nested. *)
(*   repeat rewrite lift_mkApps. *)
(*   (* do 2 rewrite map_map, map_app. *) *)
(*   (* cbn. *) *)
(*   (* f_equal. *) *)
(*   (* f_equal. *) *)
(*   (* - admit. *) *)
(*   (* -  *) *)

(*   do 2 rewrite map_map, map_app, map_mapi. *)
(*   f_equal. *)
(*   f_equal. *)
(*   - apply mapiExt. *)
(*     intros. *)
(*     cbn. *)
(*     replace (#|ind_indices| + 0 <=? #|ind_indices| + (ind_npars mind_body - i - 1)) with true. *)
(*     2: { *)
(*       symmetry. *)
(*       apply leb_correct. *)
(*       lia. *)
(*     } *)
(*     cbn. *)
(*     replace (#|ind_indices| + 0 <=? S (S (#|ind_ctors ind_body| + (#|ind_indices| + (ind_npars mind_body - i - 1))))) with true. *)
(*     2: { *)
(*       symmetry. *)
(*       apply leb_correct. *)
(*       lia. *)
(*     } *)
(*     reflexivity. *)
(*   - admit. (* is this even true? *) *)
(*   (*   symmetry. *) *)
(*   (*   erewrite mapExt. *) *)
(*   (*   2: { *) *)
(*   (*     intros. *) *)
(*   (*     rewrite simpl_lift. *) *)
(*   (*     2-3:lia. *) *)
(*   (*     reflexivity. *) *)
(*   (*   } *) *)
(*   (*   rewrite liftMkRel. *) *)

(*   (*   pose proof (@liftMkRel term). *) *)
(*   (*   unfold mkRel in H. *) *)


(*   (*   rewrite H. *) *)
(*   (*   apply mapExt. *) *)
(*   (*   intros. *) *)

(*   (* cbn. *) *)

(*   (* symmetry. *) *)
(*   (* rewrite simpl_lift. *) *)
(*   (* -  *) *)
(*   (* cbn. *) *)
(*   (* done somewhere *) *)
(* Admitted. (* admit *) *)


Lemma typeLiftLiftApplication:
  {x &
  Σ;;;
  ((lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices ++
    [vass (nNamed "inst"%string)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                (mkApps (tInd ind univ)
                   (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                      (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
             (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))]) ++
   lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices ++
   vass (nNamed "f"%string)
     ((lift0 0)
        (replaceLastProd'
           ((lift0 (S #|ind_ctors ind_body|))
              (replaceLastProd
                 (tProd (nNamed (ind_name ind_body))
                    (createAppChain
                       ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                          (mkApps (tInd ind univ)
                             (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                       (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                    (getMaxElim (ind_kelim ind_body)))
                 (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
           (tApp
              (tRel
                 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) +
                  S #|ind_ctors ind_body|))
              (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
               :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                    (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
   :: rev
        (quantifyCases false
           (map (on_snd (Init.Nat.add (ind_npars mind_body - ind_npars mind_body))) (ind_ctors ind_body))
           (ind_npars mind_body) ind univ) ++
      vass (nNamed "p"%string)
        (replaceLastProd
           (tProd (nNamed (ind_name ind_body))
              (createAppChain
                 ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                    (mkApps (tInd ind univ)
                       (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                          (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
              (getMaxElim (ind_kelim ind_body))) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
      :: skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body) ++ Γ)
  |- lift (S #|ind_indices|) (#|ind_indices| + 0)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             (mkApps (tInd ind univ)
                (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                      (ind_params mind_body))) #|ind_indices|)) : (lift0 (S #|ind_indices|)) (tSort x)}.
Proof.
  pose proof caseEnvHasType as X0.

    unfold snoc, app_context in X0.
    destruct X0.
    exists x.
    rewrite ind_arity_eq in t0.
    rewrite removeArityCount in t0.
    2: eapply indParamVass;eassumption.
    2: now rewrite uniP, nparCount.
    rewrite uniP in t0.
    cbn in t0.
    unfold count_prods in t0.
    rewrite collectProdMkProd in t0.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite revLen, lift_mkApps in t0.
    rewrite map_mapi, sub_diag in t0.
    unfold skipn in t0.
    cbn in t0.

    match goal with
      |- _ ;;; ((?Γ'1 ++ [?l1]) ++ ?L3 ++ ?L4) |- _ : _ =>
      replace ((Γ'1 ++ [l1]) ++ L3 ++ L4) with (Γ'1 ++ (l1::L3) ++ L4);
        [
          remember (l1::L3) as Γ'';
            remember (lift_context (S(S #|ind_ctors ind_body|)) 0 ind_indices) as Γ';
            replace Γ'1 with (lift_context #|Γ''| 0 Γ')
        |]
    end.
    2: {
      subst Γ''.
      cbn.
      subst Γ'.
      rewrite lift_context_len.
      rewrite simplLiftContext.
      2-3: lia.
      reflexivity.
    }
    2: {
      cbn.
      repeat rewrite <- app_assoc.
      reflexivity.
    }
    match goal with
      |- _ ;;; _ |- _ : ?A =>
      replace A with (lift #|Γ''| #|Γ'| (tSort x))
    end.
    2: {
      reflexivity.
    }
    pose proof weakening_typing as X0.
    unfold snoc, app_context in X0.
    match goal with
      |- _ ;;; _ |- (lift ?A ?B ?C) : _ =>
      replace A with #|Γ''|;
                     [
                       replace B with #|Γ'|
                     |]
    end.
    (* 1-3: subst Γ'' Γ';try rewrite lift_context_len. *)
    (* 2-3:cbn. *)
    (* 2-3: cbn;lia. *)
    3: subst Γ'';cbn.
    2-3: subst Γ';rewrite lift_context_len;lia.
    apply X0;subst Γ'' Γ'.
    + apply wfSigma.
    + clear X0.
      unfold snoc, app_context.
      pose proof wfLocalCaseEnvEnv as X0.
      unfold snoc, app_context in X0.

      (* rewrite revLen in X0. *)
      unfold count_prods, createAppChain, createAppChainOff.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite nparCount, sub_diag.
      unfold skipn.
      rewrite revLen.
      repeat rewrite lift_mkApps.
      rewrite map_mapi.
      rewrite nparCount in X0.
      rewrite mkApps_nested.
      (* rewrite lift_mkApps in X0. *)
      cbn.
      cbn in X0.
      (* rewrite map_app in X0. *)
      (* rewrite map_mapi in X0. *)
      (* rewrite map_mapi. *)
      (* rewrite mkApps_nested. *)
      rewrite <- nparCount in X0.
      rewrite uniP in X0.
      rewrite sub_diag in X0.
      unfold skipn in X0.
      rewrite ind_arity_eq in X0.
      rewrite nparCount in X0.
      rewrite removeArityCount in X0.
      2: eapply indParamVass;eassumption.
      2: reflexivity.
      rewrite collectProdMkProd in X0.
      2: apply indicesVass.
      2: cbn;trivial.
      revert X0.
      match goal with
        |- wf_local _ ?A -> wf_local _ ?B =>
        replace A with B
      end.
      trivial.
      repeat rewrite <- app_assoc.
      f_equal.
      cbn.
      rewrite revLen.
      f_equal.
      repeat rewrite <- app_assoc.
      cbn.
      reflexivity.
    + cbn.
      rewrite lift_context_len.
      pose proof wfLocalMatchTypeEnv as X1.
      revert X1.
      match goal with
        |- wf_local _ ?A -> wf_local _ ?B =>
        replace A with B
      end.
      trivial.
      repeat rewrite <- app_assoc.
      f_equal.
      1: {
        rewrite simplLiftContext.
        2-3: lia.
        reflexivity.
      }
      cbn.
      rewrite revLen.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;trivial.
      f_equal.
      1: do 2 f_equal.
      all: rewrite revLen, sub_diag;unfold skipn.
      2: repeat f_equal.
      all:
        rewrite lift_mkApps;
        rewrite map_mapi;
        cbn;
        unfold createAppChain, createAppChainOff;
        rewrite mkApps_nested;
        reflexivity.
    + rewrite lift_context_len.
      rewrite sub_diag.
      unfold skipn.
      rewrite lift_mkApps, map_mapi.
      cbn.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen.
      rewrite add_0_r in t0.
      apply t0.
Qed.


Lemma wfLocalIndInst:
  wf_local Σ
    ((Env ,,, lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices),,
     vass (nNamed (ind_name ind_body))
       (lift (S #|ind_indices|) (#|ind_indices| + 0)
          (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi
                      (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                      (ind_params mind_body))) #|ind_indices|)))).
Proof.
  pose proof wfLocalMatchTypeEnv.
  unfold snoc, app_context.
  unfold snoc, app_context in X.
  unfold snoc, app_context in HeqEnv.
  constructor.
  - subst Env.
    revert X.
    match goal with
      |- wf_local _ ?A -> wf_local _ ?B =>
      replace A with B
    end.
    2: {
      repeat rewrite <- app_assoc.
      cbn.
      unfold count_prods.
      rewrite collectProdMkProd.
      2: apply indicesVass.
      2: cbn;congruence.
      rewrite revLen, sub_diag.
      repeat f_equal.
      1-3: unfold createAppChain, createAppChainOff;
      cbn;
      rewrite lift_mkApps, map_mapi, mkApps_nested;
      reflexivity.
    }
    trivial.
  - cbn.
    destruct typeLiftLiftApplication.
    exists x.
    rewrite HeqEnv.
    rewrite <- appCons.
    rewrite app_assoc.
    change (TemplateTerm.tSort x) with (lift0 (S #|ind_indices|) (tSort x)).
    apply t0.


    (* pose proof caseEnvHasType. *)
    (* unfold snoc, app_context in X0. *)
    (* destruct X0. *)
    (* exists x. *)
    (* rewrite ind_arity_eq in t0. *)
    (* rewrite removeArityCount in t0. *)
    (* 2: eapply indParamVass;eassumption. *)
    (* 2: now rewrite uniP, nparCount. *)
    (* rewrite uniP in t0. *)
    (* cbn in t0. *)
    (* unfold count_prods in t0. *)
    (* rewrite collectProdMkProd in t0. *)
    (* 2: apply indicesVass. *)
    (* 2: cbn;congruence. *)
    (* rewrite revLen, lift_mkApps in t0. *)
    (* rewrite map_mapi, sub_diag in t0. *)
    (* unfold skipn in t0. *)
    (* cbn in t0. *)
    (* rewrite HeqEnv. *)
    (* rewrite <- appCons. *)
    (* rewrite app_assoc. *)
    (* change (TemplateTerm.tSort x) with (lift0 (S #|ind_indices|) (tSort x)). *)


    (* unfold createAppChain, createAppChainOff. *)
    (* rewrite simpl_lift. *)
    (* 2-3: lia. *)
    (* do 4 rewrite lift_mkApps. *)
    (* eapply Generation.type_mkApps. *)
    (* +  *)
    (* +  *)

    (* lookup parts in caseEnvHasType *)




    (* Check weakening. *)
    (* match goal with *)
    (*   |- _ ;;; _ |- lift ?n ?m ?A : _ => *)
    (*   replace (lift n m A) with (lift0 n A) *)
    (* end. *)
    (* 2: { *)
    (*   apply liftAfterIndices. *)
    (* } *)
    (* match goal with *)
    (*   |- _ ;;; (?G1 ++ ?G2) |- _ : _ => *)
    (*   replace (S #|ind_indices|) with (#|G1|) *)
    (* end. *)
    (* 2: { *)
    (*   rewrite appLen, lift_context_len. *)
    (*   cbn. *)
    (*   lia. *)
    (* } *)
    (* apply weakening. *)
    (* + apply wfSigma. *)
    (* + (* 2+ctor indices ++ f ++ .. *) *)
    (*   unfold snoc, app_context. *)
    (*   pose proof wfLocalMatchTypeEnv. *)
    (*   rewrite revLen in X0. *)
    (*   unfold count_prods, createAppChain, createAppChainOff. *)
    (*   rewrite collectProdMkProd. *)
    (*   2: apply indicesVass. *)
    (*   2: cbn;congruence. *)
    (*   rewrite nparCount, sub_diag. *)
    (*   unfold skipn. *)
    (*   rewrite revLen. *)
    (*   repeat rewrite lift_mkApps. *)
    (*   rewrite map_mapi. *)
    (*   rewrite nparCount in X0. *)
    (*   rewrite mkApps_nested. *)
    (*   rewrite lift_mkApps in X0. *)
    (*   cbn. *)
    (*   cbn in X0. *)
    (*   rewrite map_app in X0. *)
    (*   rewrite map_mapi in X0. *)
    (*   rewrite map_mapi. *)
    (*   rewrite mkApps_nested. *)
    (*   apply X0. *)
    (* + rewrite sub_diag. *)
    (*   unfold skipn. *)
    (*   rewrite lift_mkApps, map_mapi. *)
    (*   cbn. *)
    (*   unfold count_prods. *)
    (*   rewrite collectProdMkProd. *)
    (*   2: apply indicesVass. *)
    (*   2: cbn;congruence. *)
    (*   rewrite revLen. *)
    (*   apply t0. *)
Qed.


(* depends on typingSpineIndices *)
Lemma typingSpineInstInstf:
  typing_spine Σ
    (vass (nNamed (ind_name ind_body))
       (lift (S #|ind_indices|) (#|ind_indices| + 0)
          (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                      (ind_params mind_body))) #|ind_indices|)))
     :: lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices ++
        vass (nNamed "inst"%string)
          (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                   (mkApps (tInd ind univ)
                      (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                         (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
        :: lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices ++
           vass (nNamed "f"%string)
             ((lift0 0)
                (replaceLastProd'
                   ((lift0 (S #|ind_ctors ind_body|))
                      (replaceLastProd
                         (tProd (nNamed (ind_name ind_body))
                            (createAppChain
                               ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                                  (mkApps (tInd ind univ)
                                     (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                        (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                               (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                            (getMaxElim (ind_kelim ind_body))) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                   (tApp (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + S #|ind_ctors ind_body|))
                      (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
                       :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                            (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
           :: rev
                (quantifyCases false (map (on_snd (Init.Nat.add (ind_npars mind_body - ind_npars mind_body))) (ind_ctors ind_body))
                   (ind_npars mind_body) ind univ) ++
              vass (nNamed "p"%string)
                (replaceLastProd
                   (tProd (nNamed (ind_name ind_body))
                      (createAppChain
                         ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                            (mkApps (tInd ind univ)
                               (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                  (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                         (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) (getMaxElim (ind_kelim ind_body)))
                   (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
              :: skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body) ++ Γ)
    ((lift0 (S (S (#|ind_indices| + S (#|ind_indices| + S #|ind_ctors ind_body|)))))
       (decl_type
          (vass (nNamed "p"%string)
             (replaceLastProd
                (tProd (nNamed (ind_name ind_body))
                   (createAppChain
                      ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                         (mkApps (tInd ind univ)
                            (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                               (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                      (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) (getMaxElim (ind_kelim ind_body)))
                (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))))
    (tRel #|ind_indices|
     :: map (lift (S #|ind_indices|) (S (#|ind_indices| + 0)))
       (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)) (tSort maxElimSort).
Proof.
  pose proof typingSpineIndices as t0.
  rewrite replaceUnderItMkProd.
  2: apply indicesVass.
  unfold snoc, app_context.
  unfold snoc, app_context in t0.
  (* destruct X. *)
  rewrite lift_mkApps,map_mapi in t0.
  (* exists (tSort x). *)
  match goal with
    |- typing_spine _ (?A :: ?B ++ ?C :: ?D ++ ?E :: ?F) _ _ _ =>
    replace (A :: B ++ C :: D ++ E :: F) with
      ((A::B) ++ (C::D++[E]) ++ F)
  end.
  2: {
    rewrite consMin.
    f_equal.
    rewrite <- appCons.
    f_equal.
    rewrite consMin.
    f_equal.
    rewrite consMin.
    f_equal.
    cbn.
    f_equal.
    rewrite <- app_assoc.
    f_equal.
  }

  rewrite consMin in t0.

  revert t0.
  match goal with
    |- typing_spine _ (?xs ++ ?G) ?a ?x ?t ->
      typing_spine _ (?xs2 ++ ?ys ++ ?G2) ?a2 ?x2 ?t2 =>
    set (n:=S(S #|ind_indices|));
    change t2 with (lift n #|xs| t);
    replace xs2 with (lift_context n 0 xs);
    [replace a2 with (lift n #|xs| a);
     [replace x2 with (map (lift n #|xs|) x);
      [replace G2 with G|]
     |]
    |]
  end.
  2: {
    rewrite uniP.
    repeat f_equal.
    cbn.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite revLen.
    repeat f_equal.
    rewrite lift_mkApps, map_mapi.
    f_equal.
  }
  2: {
    rewrite succLen, lift_context_len.
    cbn.
    replace (match #|ind_indices| with
      | 0 => false
      | S m' => #|ind_indices| <=? m'
             end) with (false).
    2: {
      destruct #|ind_indices|;trivial.
      symmetry.
      apply leb_correct_conv.
      constructor.
    }
    rewrite add_0_r.
    subst n.
    f_equal.
    rewrite liftMkRel.
    rewrite liftMkRel.
    2-3: lia.
    reflexivity.
  }
  2: {
    subst n.
    cbn.
    rewrite lift_context_len.
    rewrite simpl_lift.
    2-3: lia.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite revLen.
    repeat f_equal.
    rewrite lift_mkApps, map_mapi, uniP, sub_diag.
    unfold skipn.
    cbn.
    reflexivity.
  }
  2: {
    cbn.
    rewrite mapi_rec_app, rev_unit.
    rewrite revLen, lift_context_len.
    rewrite simpl_lift.
    2-3: lia.
    cbn.
    subst n.
    f_equal.
    - unfold map_decl,vass.
      cbn.
      f_equal.
      rewrite simpl_lift.
      2-3: lia.
      f_equal.
      1: lia.
      rewrite uniP, sub_diag.
      unfold skipn.
      reflexivity.
    - pose proof mapiLiftContext.
      unfold mapi in H.

      pose proof (@mapiExt (context_decl) (context_decl)).
      unfold mapi in H0.
      erewrite H0.
      2: {
        intros.
        rewrite add_0_r.
        reflexivity.
      }
      rewrite H.
      f_equal.
      lia.
  }
  intros t0.
  pose proof typingSpineLifting.
  unfold snoc, app_context in X.
  apply X.
  - apply t0.
  - cbn.
    rewrite appLen, lift_context_len.
    cbn. subst n.
    lia.
Qed.


Lemma typingSpineInstInstf':
  { t &
  typing_spine Σ
    (vass (nNamed (ind_name ind_body))
       (lift (S #|ind_indices|) (#|ind_indices| + 0)
          (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                (mkApps (tInd ind univ)
                   (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                      (ind_params mind_body))) #|ind_indices|)))
     :: lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices ++
        vass (nNamed "inst"%string)
          (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
             (createAppChain
                ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                   (mkApps (tInd ind univ)
                      (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                         (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
        :: lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices ++
           vass (nNamed "f"%string)
             ((lift0 0)
                (replaceLastProd'
                   ((lift0 (S #|ind_ctors ind_body|))
                      (replaceLastProd
                         (tProd (nNamed (ind_name ind_body))
                            (createAppChain
                               ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                                  (mkApps (tInd ind univ)
                                     (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                        (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                               (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                            (getMaxElim (ind_kelim ind_body))) (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                   (tApp (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + S #|ind_ctors ind_body|))
                      (tRel (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
                       :: nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a)
                            (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
           :: rev
                (quantifyCases false (map (on_snd (Init.Nat.add (ind_npars mind_body - ind_npars mind_body))) (ind_ctors ind_body))
                   (ind_npars mind_body) ind univ) ++
              vass (nNamed "p"%string)
                (replaceLastProd
                   (tProd (nNamed (ind_name ind_body))
                      (createAppChain
                         ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                            (mkApps (tInd ind univ)
                               (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                                  (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                         (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) (getMaxElim (ind_kelim ind_body)))
                   (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))
              :: skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body) ++ Γ)
    ((lift0 (S (S (#|ind_indices| + S (#|ind_indices| + S #|ind_ctors ind_body|)))))
       (decl_type
          (vass (nNamed "p"%string)
             (replaceLastProd
                (tProd (nNamed (ind_name ind_body))
                   (createAppChain
                      ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                         (mkApps (tInd ind univ)
                            (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                               (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                      (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))) (getMaxElim (ind_kelim ind_body)))
                (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))))
    (tRel #|ind_indices|
     :: map (lift (S #|ind_indices|) (S (#|ind_indices| + 0)))
       (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)) t}.
Proof.
  eexists.
  now apply typingSpineInstInstf.
Qed.


(* depends on typingSpineInstInstf *)
Lemma pAppliedIndType:
  Σ;;;
  (Env ,,, lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices),,
  vass (nNamed (ind_name ind_body))
    (lift (S #|ind_indices|) (#|ind_indices| + 0)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             (mkApps (tInd ind univ)
                (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                   (ind_params mind_body))) #|ind_indices|)))
  |- tApp (tRel (S (#|ind_indices| + S (#|ind_indices| + S #|ind_ctors ind_body|))))
       (tRel #|ind_indices|
        :: map (lift (S #|ind_indices|) (S (#|ind_indices| + 0)))
          (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
       : tSort maxElimSort.
Proof.
  rewrite HeqEnv.
  pose proof typingSpineInstInstf.
  (* evar (t:term). *)
  (* exists x. *)
  (* replace 1 with 1. *)
  (* eexists. *)
  eapply type_App.
  - apply type_Rel.
    + rewrite <- HeqEnv.
      apply wfLocalIndInst.
    + cbn.
      unfold snoc, app_context.
      rewrite nth_error_app_ge.
      2: {
        rewrite lift_context_len.
        lia.
      }
      match goal with
        |- nth_error (?ls1 :: ?Ls2 ++ ?ls3 :: ?Ls4 ++ ?ls5 :: ?Ls6 ++ ?Ls7 ) _ = _ =>
        remember ls1 as l1;
        remember Ls2 as L2;
        remember ls3 as l3;
        remember Ls4 as L4;
        remember ls5 as l5;
        remember Ls6 as L6;
        remember Ls7 as L7;
        replace (l1 :: L2 ++ l3 :: L4 ++ l5 :: L6 ++ L7) with
          ((l1 :: L2 ++ l3 :: L4) ++ (l5 :: L6 ++ L7))
      end.
      2: {
        cbn.
        f_equal.
        rewrite <- app_assoc.
        f_equal.
      }
      subst l1 L2 l3 L4 l5 L6 L7.
      rewrite nth_error_app_ge.
      2: {
        cbn.
        rewrite appLen.
        rewrite lift_context_len.
        cbn.
        rewrite revLen, quantifyCasesLen.
        rewrite mapLen.
        rewrite lift_context_len.
        lia.
      }
      match goal with
        |- nth_error _ ?n = _ =>
        replace n with 0
      end.
      2: {
        cbn.
        rewrite appLen, lift_context_len, revLen.
        cbn. unfold mapi.
        rewrite revLen, quantifyCasesLen, mapi_rec_len.
        rewrite mapLen, revLen.
        lia.
      }
      cbn.
      reflexivity.
  - cbn. congruence.
  - congruence.
  - unfold snoc, app_context.
    (*
      typingSpineIndices
      CaseEnvHasType inner part
      matchTypeEnv inner part
     *)
    revert X.
    match goal with
      |- typing_spine _ ?A1 ?A2 ?A3 _ -> typing_spine _ ?B1 ?B2 ?B3 _ =>
      replace A1 with B1;
      replace A2 with B2;
      replace A3 with B3
    end.
    intros t0.
    apply t0.
    all: try reflexivity.
Qed.


Lemma pAppliedIndType':
  { t &
  Σ;;;
  (Env ,,, lift_context (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) 0 ind_indices),,
  vass (nNamed (ind_name ind_body))
    (lift (S #|ind_indices|) (#|ind_indices| + 0)
       (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
             (mkApps (tInd ind univ)
                (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                   (ind_params mind_body))) #|ind_indices|)))
  |- tApp (tRel (S (#|ind_indices| + S (#|ind_indices| + S #|ind_ctors ind_body|))))
       (tRel #|ind_indices|
        :: map (lift (S #|ind_indices|) (S (#|ind_indices| + 0)))
             (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
    : t}.
Proof.
  eexists.
  now apply pAppliedIndType.
Qed.


(* (* is wrong need to be corrected in matchTypeHasType (indices direct not later on) *) *)
(* Lemma liftingParamApp: *)
(*   (lift0 (S #|ind_indices|)) *)
(*     (lift (S (S #|ind_ctors ind_body|)) #|ind_indices| *)
(*        (mkApps (mkApps (tInd ind univ) (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body))) *)
(*           (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))) = *)
(*   lift (S #|ind_indices|) #|ind_indices| *)
(*     (lift (S (S #|ind_ctors ind_body|)) #|ind_indices| *)
(*        (mkApps (mkApps (tInd ind univ) (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1))) (ind_params mind_body))) *)
(*                (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))). *)
(* Proof. *)
(*       (* repeat rewrite lift_mkApps. *) *)
(*       (* repeat rewrite map_map. *) *)
(*       (* repeat rewrite map_mapi. *) *)

(*       (* rewrite lift_context_lift. *) *)
(*       (* rewrite simpl_lift at 2. *) *)
(*       (* cbn. *) *)
(*       (* rewrite simpl_lift at 2. *) *)
(*       (* admit. *) *)
(* Admitted. (* admit *) *)

Print ind_body.
Print one_inductive_body.

Definition matchTypeType :=
it_mkProd_or_LetIn (lift_context (S #|ind_indices| + S (S #|ind_ctors ind_body|)) 0 ind_indices)
  (* (tProd (nNamed "inst"%string) *)
  (tProd (nNamed (ind_name ind_body))
    (lift (S #|ind_indices|) (#|lift_context (S (S #|ind_ctors ind_body|)) 0 ind_indices| + 0)
        (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
          (createAppChain
              (mkApps (tInd ind univ)
                (mapi
                    (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (ind_npars mind_body - i - 1)))
                    (ind_params mind_body))) #|ind_indices|))) (tSort maxElimSort)).
(* need pAppliedIndType type *)
Lemma matchTypeHasType :
  Σ;;; Env |- matchType : matchTypeType.
Proof.
  intros.
  pose proof pAppliedIndType as t0.
  destruct caseEnvHasType.
  rewrite HeqmatchType.
  rewrite HeqretType.
  rewrite HeqEnv.
  (* evar (mTT:term). *)
  (* exists mTT. *)
  apply type_it_mkLambda_or_LetIn.
  cbn.

  destruct typeLiftLiftApplication.
  (* replace 1 with 1. *)
  eapply type_Lambda.
  - rewrite sub_diag in t1.
    unfold count_prods in t1.
    rewrite collectProdMkProd in t1.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite revLen in t1.
    rewrite uniP in t1.
    rewrite sub_diag in t1.
    rewrite mapSndAdd0 in t1.
    cbn in t1.
    rewrite ind_arity_eq in t1.
    rewrite removeArityCount in t1.
    2: eapply indParamVass;eassumption.
    2: apply nparCount.
    rewrite collectProdMkProd in t1.
    2: apply indicesVass.
    2: cbn;congruence.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: apply indicesVass.
    2: cbn;congruence.
    unfold createAppChain, createAppChainOff.
    rewrite lift_mkApps.
    rewrite mkApps_nested.
    rewrite map_mapi.
    unfold createAppChain in t1.
    unfold createAppChainOff in t1.
    rewrite lift_mkApps in t1.
    rewrite mkApps_nested in t1.
    rewrite map_mapi in t1.
    rewrite sub_diag.
    unfold skipn.
    unfold snoc, app_context.
    unfold snoc, app_context in t1.
    rewrite <- appCons.
    rewrite app_assoc.
    assert(forall s, tSort s = (lift0 (S #|ind_indices|)) (tSort s)) as -> by reflexivity.

    unfold createAppChain, createAppChainOff.
    rewrite revLen, mkApps_nested.
    unfold count_prods in t2.
    rewrite collectProdMkProd in t2.
    2: apply indicesVass.
    2: cbn;trivial.
    unfold createAppChain, createAppChainOff in t2.
    rewrite revLen, mkApps_nested in t2.
    rewrite sub_diag in t2.
    unfold skipn in t2.
    cbn.
    rewrite lift_mkApps in t2.
    rewrite simpl_lift in t2.
    2-3: rewrite add_0_r;cbn;lia.
    cbn in t2.
    rewrite lift_mkApps in t2.
    rewrite map_mapi in t2.
    cbn in t2.
    rewrite mkApps_nested in t2.
    rewrite lift_mkApps in t2.
    rewrite map_mapi in t2.
    rewrite mkApps_nested in t2.
    cbn in t2.
    rewrite lift_mkApps.
    rewrite map_app, map_mapi.
    cbn.
    revert t2.
    match goal with
      |- _;;;?E1 |- ?B1 : ?T1 ->
                        _;;;?E2 |- ?B2 : ?T2 =>
      replace E2 with E1;
        [replace B2 with B1;
         [replace T2 with T1|]
        |]
    end;trivial.
    + rewrite lift_context_len, add_0_r.
      f_equal.
      rewrite lift_mkApps.
      cbn.
      f_equal.
      rewrite map_app, map_mapi.
      cbn.
      reflexivity.
    + do 6 f_equal.
      apply mapiExt.
      intros.
      replace (#|ind_indices| + 0 <=? #|ind_indices| + (ind_npars mind_body - i - 1)) with true.
      2: {
        symmetry.
        apply leb_correct.
        lia.
      }
      f_equal.
      lia.
    (*   reflexivity. *)




    (* trivial. *)
    (* + reflexivity. *)
    (* +  *)
    (* apply t2. *)

    (* rewrite lift_context_len, add_0_r, revLen. *)
    (* match goal with *)
    (*   |- _ ;;; ((?Γ'1 ++ [?l1]) ++ ?L3 ++ ?L4) |- _ : _ => *)
    (*   replace ((Γ'1 ++ [l1]) ++ L3 ++ L4) with (Γ'1 ++ (l1::L3) ++ L4); *)
    (*     [ *)
    (*       remember (l1::L3) as Γ''; *)
    (*         remember (lift_context (S(S #|ind_ctors ind_body|)) 0 ind_indices) as Γ'; *)
    (*         replace Γ'1 with (lift_context #|Γ''| 0 Γ') *)
    (*     |] *)
    (* end. *)
    (* 2: { *)
    (*   subst Γ''. *)
    (*   cbn. *)
    (*   subst Γ'. *)
    (*   rewrite lift_context_len. *)
    (*   rewrite simplLiftContext. *)
    (*   2-3: lia. *)
    (*   reflexivity. *)
    (* } *)
    (* 2: { *)
    (*   cbn. *)
    (*   repeat rewrite <- app_assoc. *)
    (*   reflexivity. *)
    (* } *)
    (* match goal with *)
    (*   |- _ ;;; _ |- _ : ?A => *)
    (*   replace A with (lift #|Γ''| #|Γ'| (tSort x)) *)
    (* end. *)
    (* 2: { *)
    (*   reflexivity. *)
    (* } *)
    (* pose proof weakening_typing. *)
    (* unfold snoc, app_context in X. *)
    (* match goal with *)
    (*   |- _ ;;; _ |- (lift ?A ?B ?C) : _ => *)
    (*   replace A with #|Γ''|; *)
    (*                  [ *)
    (*                    replace B with #|Γ'| *)
    (*                  |] *)
    (* end. *)
    (* (* 1-3: subst Γ'' Γ';try rewrite lift_context_len. *) *)
    (* (* 2-3:cbn. *) *)
    (* (* 2-3: cbn;lia. *) *)
    (* 3: subst Γ'';cbn. *)
    (* 2-3: subst Γ';rewrite lift_context_len;lia. *)
    (* apply X0;subst Γ'' Γ'. *)


    (* match goal with *)
    (*   |- _ ;;; _ |- lift ?ln ?off ?bod : _ => *)
    (*   replace (lift ln off bod) with *)
    (*           (lift0 ln bod) *)
    (* end. *)
    (* 2: { *)
    (*   cbn. *)
    (*   rewrite lift_context_len. *)
    (*   rewrite add_0_r. *)
    (*   apply liftingParamApp. *)
    (* } *)
    (* match goal with *)
    (*   |- _ ;;; (?G1 ++ ?G2) |- _ : _ => *)
    (*   replace (S #|ind_indices|) with *)
    (*               (#| G1 |) *)
    (* end. *)
    (* 2: { *)
    (*   cbn. *)
    (*   rewrite appLen, lift_context_len. *)
    (*   cbn. *)
    (*   lia. *)
    (* } *)
    (* apply weakening. *)
    (* + apply wfSigma. *)
    (* + unfold snoc, app_context. *)
    (*   apply wfLocalMatchTypeEnv. *)
    (* + unfold skipn in t1. *)
    (*   rewrite mapSndAdd0. *)
    (*   repeat rewrite lift_mkApps in t1. *)
    (*   repeat rewrite lift_mkApps. *)
    (*   change ((lift0 #|ind_indices|) (tInd ind univ)) with (tInd ind univ) in t1. *)
    (*   rewrite map_mapi in t1. *)
    (*   apply t1. *)
  - unfold count_prods.
    rewrite collectProdMkProd.
    2: eapply indicesVass;eassumption.
    2: cbn;congruence.
    rewrite lift_context_len,revLen.
    assert(#|ind_indices| + 0 <=? #|ind_indices| + S #|ind_ctors ind_body| = true) as ->.
    {
      apply leb_correct;lia.
    }
    assert(match #|ind_indices| with
            | 0 => false
            | S m' => #|ind_indices| + 0 <=? m'
           end=false) as ->.
    {
      destruct(#|ind_indices|);trivial;apply leb_correct_conv;lia.
    }
    rewrite HeqEnv in t0.
    unfold snoc, app_context in t0.
    unfold snoc, app_context.
    unfold count_prods in t0.
    rewrite collectProdMkProd in t0.
    2: apply indicesVass.
    2: cbn;congruence.
    rewrite revLen in t0.
    apply t0.
Qed.

Lemma matchTypeHasType' :
{ matchTypeType &
  Σ;;; Env |- matchType : matchTypeType}.
Proof.
  eexists.
  apply matchTypeHasType.
Qed.


Lemma matchElimLower :
(* { s3 & *)
  existsb (leb_sort_family (universe_family maxElimSort)) (Ast.ind_kelim ind_body).
    (* }. *)
Proof.
  intros.
  (* eexists. *)
Admitted. (* Universe *)

(* Variable *)
(* (matchTypeType : term) *)
(* (HmatchTypeType : Σ;;; Env |- matchType : matchTypeType) *)
(* (s3 : universe). *)


(* this seems wrong *)
Lemma foldLiftSubstIndices:
  fold_context (fun k' : nat => subst (rev (map decl_type (ind_params mind_body))) (k' + 0))
    (map (map_decl (subst_instance_constr univ)) ind_indices) =
  fold_context (fun k' : nat => lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (k' + 0)) ind_indices.
Proof.
  unfold fold_context.
Admitted. (* admit *)

Lemma mapParamIndRelEq:
  map (lift0 #|ind_indices|) (map decl_type (ind_params mind_body)) ++
  reln [] 0
    (subst_context (rev (map decl_type (ind_params mind_body))) 0
       (map (map_decl (subst_instance_constr univ)) ind_indices)) =
  map (lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (#|ind_indices| + 0))
    (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_indices| + (#|ind_params mind_body| - i - 1)))
       (ind_params mind_body)) ++
  map (lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (#|ind_indices| + 0))
    (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|).
Proof.
Admitted. (* admit *)

Lemma instantiateParams:
  instantiate_params (subst_instance_context univ (ind_params mind_body)) (map decl_type (ind_params mind_body))
    (subst_instance_constr univ (ind_type ind_body)) = Some (
(subst0 (rev (map decl_type (ind_params mind_body)) ++ []))
       (it_mkProd_or_LetIn (subst_instance_context univ ind_indices)
                           (subst_instance_constr univ (TemplateTerm.tSort ind_sort)))).
Proof.
    Print instantiate_params.
    unfold instantiate_params.
    rewrite ind_arity_eq.
    do 2 rewrite subst_instance_constr_it_mkProd_or_LetIn.
    rewrite instParamsSubstSimpl.
    + reflexivity.
    + intros.
      apply in_rev in H.
      eapply substInstParamVass;try eassumption.
  (* Print instantiate_params_subst. *)
    + eapply substInstParamVass;try eassumption.
    + rewrite revLen, mapLen.
      unfold subst_instance_context, map_context.
      now rewrite mapLen.
    + now rewrite revLen.
Qed.

Lemma instantiateParams3:
  instantiate_params (subst_instance_context univ (ind_params mind_body))
    (map (lift0 (S (S (S (#|ind_ctors ind_body| + #|ind_indices|)))))
       (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i - 1)) (ind_params mind_body)))
    (subst_instance_constr univ (ind_type ind_body)) = Some ((subst0
        (rev
           (map (lift0 (S (S (S (#|ind_ctors ind_body| + #|ind_indices|)))))
              (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i - 1))
                 (ind_params mind_body))) ++ []))
       (it_mkProd_or_LetIn (subst_instance_context univ ind_indices)
          (subst_instance_constr univ (TemplateTerm.tSort ind_sort)))).
Proof.
  Print instantiate_params.
  Check instantiateParams.
  unfold instantiate_params.
  rewrite ind_arity_eq.
  do 2 rewrite subst_instance_constr_it_mkProd_or_LetIn.
  rewrite instParamsSubstSimpl.
  + reflexivity.
  + intros.
    apply in_rev in H.
    eapply substInstParamVass;try eassumption.
(* Print instantiate_params_subst. *)
  + eapply substInstParamVass;try eassumption.
  + rewrite revLen, mapLen.
    unfold mapi.
    rewrite mapi_rec_len.
    rewrite substInstanceContextLen.
    reflexivity.
  + now rewrite revLen.
Qed.


(* Lemma instantiateParams2: *)
(* { a & *)
(*             (instantiate_params (subst_instance_context univ (ind_params mind_body)) *)
(*                (map decl_type (ind_params mind_body)) *)
(*                ((subst0 (inds (inductive_mind ind) univ (ind_bodies mind_body))) (subst_instance_constr univ t))) *)
(*   = Some a}. *)
(* Proof. *)
(*     Print instantiate_params. *)
(*     unfold instantiate_params. *)
(*     rewrite ind_arity_eq. *)
(*     do 2 rewrite subst_instance_constr_it_mkProd_or_LetIn. *)
(*     rewrite instParamsSubstSimpl. *)
(*     + reflexivity. *)
(*     + intros. *)
(*       apply in_rev in H. *)
(*       eapply substInstParamVass;try eassumption. *)
(*   (* Print instantiate_params_subst. *) *)
(*     + eapply substInstParamVass;try eassumption. *)
(*     + rewrite revLen, mapLen. *)
(*       unfold subst_instance_context, map_context. *)
(*       now rewrite mapLen. *)
(*     + now rewrite revLen. *)
(* Qed. *)

Lemma foldLiftSubstIndices3:
  fold_context
    (fun k' : nat =>
     subst
       (rev
          (mapi
             (fun (i : nat) (_ : context_decl) =>
              tRel (S (S (S (#|ind_ctors ind_body| + #|ind_indices| + (#|ind_params mind_body| - i - 1))))))
             (ind_params mind_body))) (k' + 0)) (map (map_decl (subst_instance_constr univ)) ind_indices) =
  fold_context (fun k' : nat => lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (k' + 0)) ind_indices.
Proof.
Admitted. (* admit *)


Lemma mapParamIndRelEq3:
  map (lift0 #|ind_indices|)
    (map (lift0 (S (S (S (#|ind_ctors ind_body| + #|ind_indices|)))))
       (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i - 1)) (ind_params mind_body))) ++
  reln [] 0
    (subst_context
       (rev
          (map (lift0 (S (S (S (#|ind_ctors ind_body| + #|ind_indices|)))))
             (mapi (fun (i : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i - 1))
                (ind_params mind_body)))) 0 (map (map_decl (subst_instance_constr univ)) ind_indices)) =
  map (lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (#|ind_indices| + 0))
    (mapi
       (fun (i : nat) (_ : context_decl) =>
        tRel
          (#|ind_indices| +
           (#|mapi_rec (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i0 - 1))
                (ind_params mind_body) 0| - i - 1))) (ind_params mind_body)) ++
  map (lift (S (#|ind_indices| + S (S #|ind_ctors ind_body|))) (#|ind_indices| + 0))
  (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|).
Proof.
  do 3 rewrite map_mapi.
  f_equal.
  - apply mapiExt.
    intros.
    cbn.
    replace (
        #|ind_indices| + 0 <=?
        #|ind_indices| +
        (#|mapi_rec (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i0 - 1))
            (ind_params mind_body) 0| - i - 1)
      ) with true.
    2: {
      symmetry.
      apply leb_correct.
      rewrite add_0_r.
      lia.
    }
    f_equal.
    rewrite mapi_rec_len.
    lia.
  - rewrite reln_alt_eq.
    Print reln_alt.
    Print mkRel.
    Print subst_context.
    rewrite relnMkRel.
    2: {
      apply vassSubstContext.
      intros y H.
      apply in_map_iff in H as (?&?&?).
      apply indicesVass in H0.
      subst y.
      destruct x.
      cbn in H0.
      rewrite H0.
      reflexivity.
    }
    (* rewrite mapiNatRec. *)
    rewrite revRev.
    cbn.
    unfold mkRel.
    rewrite subst_context_len.
    rewrite mapLen, app_nil_r.
    rewrite liftMkRel.
    reflexivity.
    rewrite add_0_r.
    constructor.
Qed.

(* need matchTypeType *)
Lemma matchTypeTypeFit :
  build_case_predicate_type (ind, Ast.ind_npars mind_body).1 mind_body ind_body
                            (firstn (ind, Ast.ind_npars mind_body).2 (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                                                                          )
 ++
        map (lift0 1)
          (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)))
             univ maxElimSort =
Some matchTypeType.
Proof.
  cbn.
  unfold matchTypeType.
  Search build_case_predicate_type.
  Print build_case_predicate_type.
  Print instantiate_params.
  Print destArity.
  Print to_extended_list.
  rewrite nparCount.
  rewrite mapDeclVass.
  erewrite <- mapi_rec_len.
  erewrite <- mapLen.
  rewrite mapiNatRec.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite sub_diag.
  rewrite firstn_O.
  rewrite app_nil_r.
  rewrite mapLen.
  unfold build_case_predicate_type.
  cbn.
  eapply optMonadEq2.
  - apply instantiateParams3.
  - Print destArity.
    rewrite app_nil_r.
    rewrite subst_it_mkProd_or_LetIn.
    cbn.
    rewrite destAritySimpl.
    cbn.
    unfold app_context.
    rewrite app_nil_r.
    reflexivity.
  - cbn.
    rewrite subst_context_len.
    unfold subst_instance_context, map_context.
    rewrite mapLen.
    unfold it_mkProd_or_LetIn.
    unfold createAppChain, createAppChainOff.
    rewrite mkApps_nested.
    cbn.
    f_equal.
    + unfold subst_context.
      unfold lift_context.

      rewrite map_mapi.
      cbn.
      (* Print subst. *)
      (* Print lift. *)
      apply foldLiftSubstIndices3.
    + change (TemplateTerm.tProd) with tProd.
      f_equal.
      (* * apply nameEq. *)
      * rewrite lift_context_len.
        rewrite simpl_lift.
        2-3: lia.
        rewrite lift_mkApps, map_app.
        cbn.
        f_equal.
        apply mapParamIndRelEq3.
Qed.





(*
  Σ;;; Env |- matchObj
  : mkApps (tInd (ind, Ast.ind_npars mind_body).1 univ)
      (map Ast.decl_type (Ast.ind_params mind_body) ++
       map (lift0 1)
         (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|))
 *)

Lemma matchObjTyping :
  Σ;;; Env |- matchObj
  : mkApps (tInd (ind, Ast.ind_npars mind_body).1 univ)
           (map Ast.decl_type (
map (vass nAnon)
(map (lift0 (3 + #|ind_ctors ind_body| + #|ind_indices|)) (mkRel (ind_params mind_body)))
                ) ++
       map (lift0 1)
         (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)).
(* Σ;;; Env |- matchObj *)
(* : mkApps (tInd (ind, Ast.ind_npars mind_body).1 univ) (map decl_type (ind_params mind_body)). *)
Proof.
  intros.
  rewrite HeqmatchObj.
  cbn.
  assert( Σ;;;Env |- tRel 0 :
(lift0 1)
         (decl_type
            (vass (nNamed "inst"%string)
               (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
                  (createAppChain
                     ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                        (mkApps (tInd ind univ)
                           (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                              (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                     (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
        ).
  {
    rewrite HeqEnv.
    eapply type_Rel;cbn.
    - apply wfLocalMatchObjEnv.
    - reflexivity.
  }

  assert(
mkApps (tInd ind univ)
       (map decl_type (
map (vass nAnon)
(map (lift0 (3 + #|ind_ctors ind_body| + #|ind_indices|)) (mkRel (ind_params mind_body)))
            ) ++
       map (lift0 1)
         (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)) =
(* mkApps (tInd ind univ) (map decl_type (ind_params mind_body)) = *)
      (lift0 1)
          (decl_type
             (vass (nNamed "inst"%string)
                (lift (S (S #|ind_ctors ind_body|)) (#|ind_indices| + 0)
                   (createAppChain
                      ((lift0 (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort))))
                         (mkApps (tInd ind univ)
                            (mapi (fun (i : nat) (_ : context_decl) => tRel (ind_npars mind_body - i - 1))
                               (skipn (ind_npars mind_body - ind_npars mind_body) (ind_params mind_body)))))
                      (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))))
  ).
  {
    cbn.
    unfold count_prods.
    rewrite collectProdMkProd.
    2: eapply indicesVass;eassumption.
    2: cbn;congruence.
    rewrite revLen.
    rewrite sub_diag.
    unfold skipn.
    apply mkAppsExt.
  }

  rewrite <- H in X.
  apply X.
Qed.

Lemma substNoApp cshape_args:
  isApp
    (subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                )) ++ [])
       (#|subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
            (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0)
            (subst_instance_context univ cshape_args)| + 0)
       (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
          (#|subst_instance_context univ cshape_args| +
           (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0))
          (subst_instance_constr univ
             (TemplateTerm.tRel
                (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
                                                             #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|))))) = false.
Proof.
              cbn.
              replace (
         #|subst_instance_context univ cshape_args| +
         (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0) <=?
         #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
                                                     #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|) with true.
              2: {
                admit.
              }
              admit.
Admitted. (* Basic *)

(* need assumptions *)
Lemma typeBranch n ctorCount cshape_args (ind_ctors : list ((ident × TemplateTerm.term) × nat)) cshape_indices:
  Σ;;; Env
  |- it_mkLambda_or_LetIn
       (lift_context (S (#|ind_indices| + S (S ctorCount))) 0
          (subst_context [tInd ind univ]
             #|mapi_rec (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i0 - 1))
                 (ind_params mind_body) 0| cshape_args))
       (createAppChain (tRel (S (#|ind_indices| + n + (ctorCount - #|ind_ctors|)))) n)
  : it_mkProd_or_LetIn
      (subst_context (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                     ))) 0
         (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
            #|TemplateEnvironment.ind_params mind_body| (subst_instance_context univ cshape_args)))
      (mkApps ((lift0 #|cshape_args|) matchType)
         (map
            (fun x : term =>
               subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                     ))) #|cshape_args|
               (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
                  (#|cshape_args| + #|TemplateEnvironment.ind_params mind_body|) (subst_instance_constr univ x)))
            cshape_indices ++
          [mkApps (tConstruct ind #|ind_ctors| univ)
             (map
                (fun x : term =>
                   subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                         ))) #|cshape_args|
                   (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
                      (#|cshape_args| + #|TemplateEnvironment.ind_params mind_body|) (subst_instance_constr univ x)))
                (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args|) ++
              to_extended_list
              (subst_context (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                             ))) 0
                   (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
                      #|TemplateEnvironment.ind_params mind_body| (subst_instance_context univ cshape_args))))])).
Proof.
Admitted. (* TODO *)

Lemma branchTypeTypes cshape_args cshape_indices (ind_ctors : list ((ident × TemplateTerm.term) × nat)):
  Σ;;; Env
  |- it_mkProd_or_LetIn
      (subst_context (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                     ))) 0
          (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
             #|TemplateEnvironment.ind_params mind_body| (subst_instance_context univ cshape_args)))
       (mkApps ((lift0 #|cshape_args|) matchType)
          (map
             (fun x : term =>
                subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                      ))) #|cshape_args|
                (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
                   (#|cshape_args| + #|TemplateEnvironment.ind_params mind_body|) (subst_instance_constr univ x)))
             cshape_indices ++
           [mkApps (tConstruct ind #|ind_ctors| univ)
              (map
                 (fun x : term =>
                    subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                          ))) #|cshape_args|
                    (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
                       (#|cshape_args| + #|TemplateEnvironment.ind_params mind_body|)
                       (subst_instance_constr univ x)))
                 (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args|) ++
               to_extended_list
               (subst_context (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                              ))) 0
                    (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
                       #|TemplateEnvironment.ind_params mind_body| (subst_instance_context univ cshape_args))))]))
  : tSort maxElimSort.
Proof.
Admitted. (* TODO *)

Lemma bodyIndApp cshape_args cshape_indices:
  is_ind_app_head
    (subst (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                )) ++ [])
       (#|subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
            (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0)
            (subst_instance_context univ cshape_args)| + 0)
       (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
          (#|subst_instance_context univ cshape_args| +
           (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0))
          (subst_instance_constr univ
             (TemplateTerm.mkApps
                (TemplateTerm.tRel
                   (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
                    #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|))
                (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) #|cshape_args| ++
                                                                                                                    cshape_indices))))).
Proof.
    rewrite subst_instance_constr_mkApps.
    rewrite subst_mkApps.
    rewrite subst_mkApps.
    cbn.
    replace (
  #|subst_instance_context univ cshape_args| +
  (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0) <=?
  #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
  #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|
      ) with true.
    2: {
      symmetry;apply leb_correct.
      rewrite substInstanceContextLen.
      rewrite substInstanceContextLen.
      lia.
    }

    Check is_ind_app_head_mkApps.
    do 2 rewrite map_map.
    cbn.
    rewrite app_nil_r, add_0_r.
    rewrite subst_context_len, substInstanceContextLen.
    rewrite substInstanceContextLen.
    replace (
              (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
               #|TemplateEnvironment.ind_params mind_body| + #|cshape_args| -
               (#|cshape_args| + (#|TemplateEnvironment.ind_params mind_body| + 0)))
      ) with (
  #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind)
          ) by lia.
    Print inds.
    assert(exists n0,
            nth_error (inds (inductive_mind ind) univ (ind_bodies mind_body))
                      (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind)) =
            Some (tInd {| inductive_mind := (inductive_mind ind); inductive_ind := n0|} univ)
          )as [n0 ->].
    {
      (* use findBody
  findBody : nth_error (ind_bodies mind_body) (inductive_ind ind) = Some ind_body
       *)
      Print inds.
      rewrite nthInds.
      2: {
        assert(#|ind_bodies mind_body|>0).
        {
          assert(ind_bodies mind_body <> []).
          {
            destruct ind_bodies.
            - contradict findBody.
              now rewrite nth_error_nil.
            - congruence.
          }
          destruct ind_bodies.
          - now contradict H.
          - cbn. lia.
        }
        lia.
      }
      eexists.
      reflexivity.
    }
    cbn.
    apply is_ind_app_head_mkApps.
Qed.


Lemma branchesHaveFittingTypes :
  (* existsb (leb_sort_family (universe_family maxElimSort)) (ind_kelim ind_body) -> *)
  ∑ branchTypes : list (nat × term),
    (map_option_out
      (build_branches_type (ind, ind_npars mind_body).1 mind_body ind_body
       (firstn (ind, Ast.ind_npars mind_body).2
               (map Ast.decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                    ) ++
           map (lift0 1)
             (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)))
 univ matchType) =
    Some branchTypes)
         *
  All2 (fun br bty : nat × term => (br.1 = bty.1 × Σ;;; Env |- br.2 : bty.2) × Σ;;; Env |- bty.2 : tSort maxElimSort)
    (mapi
       (fun (i : nat) (x : (ident × term) × nat) =>
        let (y, count) := x in
        let (_, a) := y in
        (count,
        replaceLastLambda
          (createAppChain
             (createAppChainOff
                (S (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + count))
                (tRel
                   (S
                      (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + count +
                       (#|ind_ctors ind_body| - i)))) (ind_npars mind_body - ind_npars mind_body)) count)
          ((lift0 (S (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
             (lift (S (S #|ind_ctors ind_body|)) (ind_npars mind_body - ind_npars mind_body)
                ((mapProdToLambda (remove_arity (ind_npars mind_body) a)) {ind_npars mind_body := tInd ind univ})))))
       (ind_ctors ind_body)) branchTypes.
Proof.
  pose proof substNoApp as HnoApp.
  pose proof cshapeArgsVass as HargsVass.
  pose proof indicesVass as HindVass.
  pose proof typeBranch as HtypeBranch.
  pose proof branchTypeTypes as HtypeBranchType.
  pose proof bodyIndApp as HisIndApp.
  (* evar (bt:list (nat×term)). *)
  (* pose proof onConstructorIndBodyNotMatter as onCtorBody. *)
  cbn.
  rewrite nparCount.
  erewrite <- mapi_rec_len.
  erewrite <- mapLen.
  rewrite mapDeclVass.
  rewrite mapiNatRec.
  rewrite firstn_app.
  rewrite firstn_all.
  repeat rewrite sub_diag.
  rewrite firstn_O.
  rewrite app_nil_r.
  rewrite mapLen.
  rewrite build_branches_type_.
  cbn.
  Print map_option_out.
  Print option_map.
  Print onConstructors.
  Print on_constructors.
  Print on_constructor.
  pose proof extendOnConstructors as extOnCtors.

  destruct ind_body.
  cbn in *.
  clear onIndB declI findBody onProjections HeqEnv HeqretType HeqmatchType uniP.
  remember (#|ind_ctors|) as ctorCount.
  induction ind_ctors using rev_elim in onConstructors, ind_ctors_sort, extOnCtors |- *.
  - cbn. eexists. split.
    + reflexivity.
    + constructor.
  - cbn.
      unfold on_constructors in onConstructors.
      apply All2_app_inv in onConstructors.
      destruct onConstructors as [[l1 l2] [[]]].
      (* inv onConstructors. *)
      inv a0.
      inv X.
      cbn in X1, X2.
      Print constructor_shape.
      destruct X2.
      destruct x0.

      destruct x as [[]].

      edestruct IHind_ctors as [xs ?].
      1: {
        eapply extOnCtors.
        eapply a.
      }
      1: {
        apply extOnCtors.
      }
      destruct p as [e0 ?].
      unfold instantiate_params in e0.

      cbn in *.
exists(xs ++ [let '(sign, ccl) :=
          decompose_prod_assum []
                               ((subst0 (rev (map decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + ctorCount + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                                             )) ++ []))
               (it_mkProd_or_LetIn
                  (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body))
                     (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0)
                     (subst_instance_context univ cshape_args))
                  (subst (inds (inductive_mind ind) univ (ind_bodies mind_body))
                     (#|subst_instance_context univ cshape_args| +
                      (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0))
                     (subst_instance_constr univ
                        (TemplateTerm.mkApps cshape_concl_head
                           (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body)
                              #|cshape_args| ++ cshape_indices)))))) in
          let
          '(paramrels, args) := chop (ind_npars mind_body) (decompose_app ccl).2 in
           (n,
           it_mkProd_or_LetIn sign
             (mkApps ((lift0 #|sign|) matchType)
                (args ++ [mkApps (tConstruct ind (#|ind_ctors| + 0) univ) (paramrels ++ to_extended_list sign)])))]
       ).
      split.
      2: {
        rewrite mapi_rec_app.
        apply All2_app.
        - apply a0.
        - constructor.
            rewrite subst_it_mkProd_or_LetIn.
            rewrite decompose_prod_assum_it_mkProd.
            2: { (* need reduction *)
              subst cshape_concl_head.
              cbn.
              apply HisIndApp.
            }
            rewrite subst_instance_constr_mkApps.
            do 2 rewrite subst_mkApps.
            rewrite decompose_app_mkApps.
            2: {
              unfold cshape_concl_head.
              apply HnoApp.
            }
            rewrite map_map.
            rewrite map_map.
            erewrite chop_map.
            2: {
              Print to_extended_list_k.
              Print reln.
              do 2 rewrite map_app.
              Check chop_n_app.
              apply chop_n_app.
              do 2 rewrite mapLen.
              rewrite toExtendedListLenNoBody.
              2: {
                eapply indParamVass;eassumption.
              }
              apply nparCount.
            }
            cbn.
            repeat rewrite app_nil_r.
            repeat rewrite plus_0_r.
            repeat rewrite subst_context_len.
            repeat rewrite substInstanceContextLen.

            rewrite cshape_eq.
            rewrite removeArityCount.
            2: eapply indParamVass;eassumption.
            2: rewrite mapi_rec_len;reflexivity.
            2: constructor.
            rewrite mapProdToLambdaItMkProd.
            rewrite mapProdNoProd.
            2: {
              destruct to_extended_list_k;trivial.
              - destruct cshape_indices;trivial.
            }
            rewrite simpl_lift.
            2-3: lia.
            2: {
              apply HargsVass.
            }
            (* Set Printing All. *)
            unfold subst1.
            rewrite subst_it_mkLambda_or_LetIn.
            rewrite lift_it_mkLambda_or_LetIn.
            rewrite replaceUnderItMkLambda.
            2: {
              intros.
              eapply liftingInVass.
              2: apply H.
              intros.
              unfold subst_context, fold_context in H0.
              apply In_rev in H0.
              apply in_mapi in H0 as(?&?&?&?).
              subst x0.
              apply In_rev in H1.
              apply HargsVass in H1.
              destruct x2.
              cbn in H1.
              rewrite H1.
              reflexivity.
            }
            (* apply type_it_mkLambda_or_LetIn. *)
            rewrite subst_mkApps.
            rewrite lift_mkApps.
            rewrite map_map.
            unfold cshape_concl_head.
            rewrite replaceLastLambdaNoLambda.
            2: {
              apply mkAppNoLambda.
              cbn.
              replace (
         #|cshape_args| + #|ind_params mind_body| <=?
         #|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
         #|TemplateEnvironment.ind_params mind_body| + #|cshape_args|
                ) with true.
              2: {
                symmetry.
                apply leb_correct.
                lia.
              }
              cbn. trivial.
                destruct leb.
                + destruct (#|TemplateEnvironment.ind_bodies mind_body| - S (inductive_ind ind) +
            #|TemplateEnvironment.ind_params mind_body| + #|cshape_args| -
            (#|cshape_args| +
             #|mapi_rec (fun (i0 : nat) (_ : context_decl) => tRel (#|ind_params mind_body| - i0 - 1))
               (ind_params mind_body) 0|));cbn;trivial.
                  rewrite nth_error_nil.
                  cbn. destruct leb;trivial.
                + cbn. destruct leb;cbn;trivial.
            }
            (* rewrite sub_diag. *)
            cbn.
            unfold count_prods.
            rewrite collectProdMkProd.
            2: apply HindVass.
            2: cbn;trivial.
            rewrite revLen.

          repeat split.
          (* + destruct decompose_prod_assum, chop. reflexivity. *)
          +
            (* subst Env. *)
            (* reduction from cshape_concl_head to tInd *)
            Print decompose_prod_assum.
            (* decompose_app_mkApps  *)
            rewrite mapDeclVass in HtypeBranch.
            specialize (HtypeBranch n ctorCount cshape_args ind_ctors cshape_indices).
            uniapply HtypeBranch.
            match goal with
              |- _;;;_|- ?a1 : ?b1 = _;;;_|- ?a2 : ?b2 =>
              replace a1 with a2;
                [replace b1 with b2;[trivial|] |]
            end.
            all: repeat rewrite map_map;
            reflexivity.
          + unfold cshape_concl_head.
            cbn.
            repeat rewrite map_map.
            specialize (HtypeBranchType cshape_args cshape_indices ind_ctors).
            uniapply HtypeBranchType.
            match goal with
              |- _;;;_|- ?a1 : _ = _;;;_|- ?a2 : _ =>
                replace a1 with a2;[trivial|]
            end.
            rewrite mapDeclVass.
            reflexivity.
      }


      (* evar (bt:list (nat×term)). *)
      (* replace 1 with 1. *)
      (* exists bt. *)

    (* pose ( *)
    (*     [let *)
    (*      '(sign, ccl) := *)
    (*       decompose_prod_assum [] *)
    (*         ((subst0 (rev (map decl_type (ind_params mind_body)) ++ [])) *)
    (*            (it_mkProd_or_LetIn *)
    (*               (subst_context (inds (inductive_mind ind) univ (ind_bodies mind_body)) *)
    (*                  (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0) *)
    (*                  (subst_instance_context univ cshape_args)) *)
    (*               (subst (inds (inductive_mind ind) univ (ind_bodies mind_body)) *)
    (*                  (#|subst_instance_context univ cshape_args| + *)
    (*                   (#|subst_instance_context univ (TemplateEnvironment.ind_params mind_body)| + 0)) *)
    (*                  (subst_instance_constr univ *)
    (*                     (TemplateTerm.mkApps cshape_concl_head *)
    (*                        (TemplateEnvironment.to_extended_list_k (TemplateEnvironment.ind_params mind_body) *)
    (*                           #|cshape_args| ++ cshape_indices)))))) in *)
    (*       let *)
    (*       '(paramrels, args) := chop (ind_npars mind_body) (decompose_app ccl).2 in *)
    (*        (n, *)
    (*        it_mkProd_or_LetIn sign *)
    (*          (mkApps ((lift0 #|sign|) matchType) *)
    (*             (args ++ [mkApps (tConstruct ind (#|ind_ctors| + 0) univ) (paramrels ++ to_extended_list sign)])))] *)
    (*   ). *)


    rewrite mapi_rec_app.

    (* erewrite mapOptionOutApp. *)

      rewrite cshape_eq.
      cbn.

    unfold instantiate_params.

    do 2 rewrite subst_instance_constr_it_mkProd_or_LetIn.
    do 2 rewrite subst_it_mkProd_or_LetIn.
    cbn.

    (* rewrite mapOptionOutApp. *)

    rewrite instParamsSubstSimpl.
    + cbn.
      (* rewrite e0. *)
      (* Fail rewrite e. *)
      (* exists bt. *)
      (* eexists. *)
      apply mapOptionOutApp.
      * apply e0.
      * cbn.
        rewrite substInstanceContextLen.
        do 2 f_equal.
        repeat f_equal.
        repeat rewrite map_map.
        rewrite mapiNatRec.
        repeat rewrite map_mapi.
        reflexivity.

      (* * reflexivity. (* point to extract type *) *)
      (* apply e0. *)
      (* admit. *)
    + intros.
      apply in_rev in H.
      eapply substInstParamVass;try eassumption.
  (* Print instantiate_params_subst. *)
    (* + eapply substInstParamVass;try eassumption. *)
    + eapply substContextSubstInstParamVass;eassumption.
    + rewrite revLen, mapLen.
      unfold subst_instance_context, map_context.
      unfold mapi.
      now rewrite mapLen, mapi_rec_len.
    + rewrite revLen.
      rewrite subst_context_len.
(* Show Existentials. *)
      reflexivity.
      (* Grab Existential Variables. *)
Qed.


(* can be proven alone (and was proven) *)
Lemma branchesHaveTypes :
  ∑ branchTypes : list (nat × term),
    map_option_out
      (build_branches_type (ind, ind_npars mind_body).1 mind_body ind_body
       (firstn (ind, Ast.ind_npars mind_body).2
               (map Ast.decl_type (
map (Ast.vass nAnon)
    (map (lift0 (3 + #|Ast.ind_ctors ind_body| + #|ind_indices|)) (mkRel (Ast.ind_params mind_body)))
                    ) ++
           map (lift0 1)
             (nat_rec (fun _ : nat => list term) [] (fun (n : nat) (a : list term) => tRel n :: a) #|ind_indices|)))
 univ matchType) =
    Some branchTypes.
Proof.
  destruct branchesHaveFittingTypes as (bty&H1&H2).
  exists bty.
  apply H1.
Qed.



Definition branchTypes :=
  let (branchesType, a) := branchesHaveFittingTypes in
  let (HeqBranchesType,branchesTypeFit) := a in
  branchesType.

(* Definition HbranchTypes :map_option_out *)
(* (build_branches_type (ind, Ast.ind_npars mind_body).1 mind_body ind_body *)
(* (firstn (ind, Ast.ind_npars mind_body).2 (map Ast.decl_type (Ast.ind_params mind_body))) *)
(* univ matchType) = Some branchTypes. *)
(* Proof. *)
(*   destruct branchesHaveFittingTypes. *)
(*   destruct p. *)
(*   sub *)
(*   apply e. *)
(*   let (branchesType, a) := branchesHaveFittingTypes in *)
(*   let (HBranchesType,branchesTypeFit) := a in *)
(*   HBranchesType. *)


(* Variable *)
(* (branchTypes : list (nat × term)) *)
(* (HbranchTypes : map_option_out *)
(* (build_branches_type (ind, Ast.ind_npars mind_body).1 mind_body ind_body *)
(* (firstn (ind, Ast.ind_npars mind_body).2 (map Ast.decl_type (Ast.ind_params mind_body))) *)
(* univ matchType) = Some branchTypes). *)

(* depends on branchesHaveTypes *)
Lemma branchTypesFit :
  existsb (leb_sort_family (universe_family maxElimSort)) (ind_kelim ind_body) ->
  All2 (fun br bty : nat × term => (br.1 = bty.1 × Σ;;; Env |- br.2 : bty.2) × Σ;;; Env |- bty.2 : tSort maxElimSort)
    (mapi
       (fun (i : nat) (x : (ident × term) × nat) =>
        let (y, count) := x in
        let (_, a) := y in
        (count,
        replaceLastLambda
          (createAppChain
             (createAppChainOff
                (S (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + count))
                (tRel
                   (S
                      (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)) + count +
                       (#|ind_ctors ind_body| - i)))) (ind_npars mind_body - ind_npars mind_body)) count)
          ((lift0 (S (count_prods (it_mkProd_or_LetIn ind_indices (TemplateTerm.tSort ind_sort)))))
             (lift (S (S #|ind_ctors ind_body|)) (ind_npars mind_body - ind_npars mind_body)
                ((mapProdToLambda (remove_arity (ind_npars mind_body) a)) {ind_npars mind_body := tInd ind univ})))))
       (ind_ctors ind_body)) branchTypes.
Proof.
  unfold branchTypes.
  destruct branchesHaveFittingTypes.
  destruct p.
  intros.
  apply a.
  (* use branchesHaveTypes *)
Qed. 

End matchSec.

End MainSec.


Lemma nameEq ind_body: nNamed "inst"%string = nNamed (ind_name ind_body).
Proof.
Admitted. (* admit *)


Import TemplateEnvironment.

Import Ast TemplateEnvironment TemplateEnvTyping.

Lemma Main2 Σ Γ mind_body ind univ ind_body:
  wf_local Σ Γ ->
  on_inductive (lift_typing typing) Σ (inductive_mind ind) mind_body ->
  on_ind_body (lift_typing typing) Σ (inductive_mind ind) mind_body (inductive_ind ind) ind_body ->
  declared_minductive Σ (inductive_mind ind) mind_body ->
  declared_inductive Σ mind_body ind ind_body ->
  getParamCount ind_body (ind_npars mind_body)=ind_npars mind_body ->
  ind_npars mind_body = #|ind_params mind_body| ->
     forall nameF T t name,
       createElim false ind univ mind_body None nameF = Some (t,name) ->
       createElimType false ind univ mind_body None nameF = Some T ->
       Σ ;;; Γ |- t : T.
Proof.
  intros Hwf onInd onIndB declM declI uniP nparCount.
  intros nameF T t name.
  intros H0 H1.
  unfold createElim in H0, H1.
  pose proof (onIndNth _ _ _ _ onIndB) as H2.
  rewrite H2 in H0.
  injection H0 as H3 H4.
  unfold createElimType in H1.
  rewrite H2 in H1.
  injection H1 as H5.
  symmetry in H3;subst t.
  symmetry in H5;subst T.
  symmetry in H4;subst name.
  rename H2 into findBody.
  pose proof onInd as onInd'.
  pose proof onIndB as onIndB'.
  destruct onInd'.
  destruct onIndB'.

  apply type_it_mkLambda_or_LetIn.
  edestruct pType with (univ := univ) (Γ:=Γ) as [s1 H];try eassumption.
  apply type_Lambda with (s2 := s1).
  (* p has type *)
  rewrite <- nameEq in H.
  1: eapply H.
  clear H.
  apply type_it_mkLambda_or_LetIn.
  match goal with
    |- ?Σ ;;; ?Γ |- tFix [?fixB] ?fixN : ?proofT => replace proofT with (dtype fixB)
  end.
  2: cbn; reflexivity. (* type is type of the fixpoint *)
  apply type_Fix.
  1: apply fixGuardAxiom. (* fix guard *)
  1: cbn; reflexivity. (* find some body in fix list *)
  1: {
    erewrite nameEq.
    apply fixEnvWf with (ind_indices:=ind_indices) (ind_sort:=ind_sort) (ind_ctors_sort:=ind_ctors_sort);
      try eassumption.
    (* trivial. *)
    (* pose proof fixEnvWf as HfixEnvWf. *)
    (* apply HfixEnvWf. *)
    (* rewrite <- nameEq in HfixEnvWf. *)
  }
  (* 1: admit. (* eapply fixEnvWf;try eassumption. *) *)
  constructor. (* reduce All from fix to one case *)
  2: constructor.
  split.
  2: cbn; (* body is lambda *)
    now apply RLLambdaIsLambdaOuter,
    mapIsProdLam,
    LiftIsProd,
    RLProdIsProd.
  cbn.
  unfold replaceLastLambda'.
  match goal with
    |- ?Σ ;;; ?Γ |- replaceLastLambda ?tcase ?body : ?type => remember tcase as caseBody
  end.
  erewrite rewriteCaseEnv;try eassumption.
  erewrite rewriteCaseEnvType;try eassumption.
  apply type_it_mkLambda_or_LetIn.
  cbn [lift].
  rewrite simpl_lift.
  2-3: rewrite lift_context_len;lia.
  edestruct caseEnvHasType with (univ := univ) (Γ:=Γ) as [s2 H];try eassumption.
  apply type_Lambda with (s3:=s2).
  rewrite <- nameEq in H.
  1: apply H.
  clear H.
  subst caseBody.

  erewrite countLeb;try eassumption.
  cbn [mapProdToLambda2].
  rewrite uniP.
  rewrite ind_arity_eq.
  rewrite removeArityCount.
  2: eapply indParamVass;eassumption.
  2: apply nparCount.

  erewrite mapTypeErase;try eassumption.

  rewrite <- add_assoc.
  cbn [plus].
  match goal with
    |- ?Σ ;;; ?Γ |- tCase ?indpar ?matchTypeT ?matchObjT ?matchCasesT : ?retTypeT =>
      remember Γ as Env;
      remember retTypeT as retType
  end.

  match goal with
    |- ?Σ ;;; ?Γ |- tCase ?indpar ?matchTypeT ?matchObjT ?matchCasesT : ?retType =>
      remember matchTypeT as matchType;
      remember matchObjT as matchObj
  end.


  erewrite matchTypeSimpl with (Γ:=Γ) in HeqmatchType;try eassumption.

  eapply etaConvRetType3 with (Γ:=Γ)
                                         (Σ:=Σ)(mind_body:=mind_body) (ind:=ind) (univ:=univ)
                                         (ind_body:=ind_body) (ind_indices:=ind_indices) (ind_sort:=ind_sort)
                                         (ind_ctors_sort:=ind_ctors_sort) (Env:=Env)
                                         (retType:=retType) (matchObj:=matchObj)
                                         (matchType:=matchType)
  ;try eassumption;try rewrite <- nameEq;[apply HeqEnv|apply HeqmatchType|].
  edestruct branchesHaveFittingTypes
    with (Γ:=Γ)
                                         (Σ:=Σ)(mind_body:=mind_body) (ind:=ind) (univ:=univ)
                                         (ind_body:=ind_body) (ind_indices:=ind_indices) (ind_sort:=ind_sort)
                                         (ind_ctors_sort:=ind_ctors_sort) (Env:=Env)
                                         (retType:=retType) (matchObj:=matchObj)
                                         (matchType:=matchType)
    as (branchTypes&HbranchTypes&branchTypesFit);try eassumption.
  1-2: rewrite <- nameEq;(apply HeqEnv + apply HeqmatchType).
  eapply type_Case with
      (mdecl := mind_body) (idecl := ind_body)
      (u := univ) (ps := maxElimSort)
      (btys := branchTypes).
  - cbn. apply declI.
  - reflexivity.
  - eapply matchTypeTypeFit with (Γ:=Γ);try eassumption.
  1-2: rewrite <- nameEq;(apply HeqEnv + apply HeqmatchType).
  (* - apply HmatchTypeType. *)
  - eapply matchTypeHasType with (Γ:=Γ);try eassumption.
  1-2: rewrite <- nameEq;(apply HeqEnv + apply HeqmatchType).
  (* - apply Hs3lower. *)
  - eapply matchElimLower with (Γ:=Γ)
                                         (Σ:=Σ)(mind_body:=mind_body) (ind:=ind) (univ:=univ)
                                         (ind_body:=ind_body) (ind_indices:=ind_indices) (ind_sort:=ind_sort)
                                         (ind_ctors_sort:=ind_ctors_sort) (Env:=Env)
                                         (retType:=retType) (matchObj:=matchObj)
                                         (matchType:=matchType)
    ;try eassumption.
  1-2: rewrite <- nameEq;(apply HeqEnv + apply HeqmatchType).
  - eapply matchObjTyping with (Γ:=Γ);try eassumption.
  1-2: rewrite <- nameEq;(apply HeqEnv + apply HeqmatchType).
  - apply HbranchTypes.
  - apply branchTypesFit.
Qed.














Open Scope string_scope.	


Axiom namingEq2: forall x, nNamed x = nAnon.	

Print declared_inductive.	
Print inductive.	



(* From here on concrete example for E_le *)



Print type_Rel.
Lemma type_Rel2 Σ Γ : forall (n : nat) (decl : Ast.context_decl) T,
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    T = (lift0 (S n)) (Ast.decl_type decl) ->
    Σ;;; Γ |- tRel n : T.
Proof.
  intros.
  subst T.
  now apply type_Rel.
Qed.

Lemma type_LambdaL: forall (Σ : global_env_ext) (Γ : context) n1 n2 t1 t2 (b bty : term),
    t1=t2 -> n1=n2 ->
Σ;;; Γ,, vass n1 t1 |- b : bty -> Σ;;; Γ |- tLambda n1 t1 b : tProd n2 t2 bty.
Proof.
  intros.
  subst t2 n2.
  now apply type_Lambda2.
Qed.

Lemma type_LambdaR: forall (Σ : global_env_ext) (Γ : context) n1 n2 t1 t2 (b bty : term),
    t1=t2 -> n1=n2 ->
Σ;;; Γ,, vass n2 t2 |- b : bty -> Σ;;; Γ |- tLambda n1 t1 b : tProd n2 t2 bty.
Proof.
  intros.
  subst t2 n2.
  now apply type_Lambda2.
Qed.


Section LeLemma.


Variable
  (Σ : global_env_ext)
  (Γ : context)
  (Hwf : wf_local Σ Γ)
  (Hmind : declared_minductive Σ (inductive_mind {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |})
        {|
        Ast.ind_finite := Finite;
        Ast.ind_npars := 1;
        Ast.ind_params := [{|
                           Ast.decl_name := nNamed "n";
                           Ast.decl_body := None;
                           Ast.decl_type := tInd
                                              {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}
                                              [] |}];
        Ast.ind_bodies := [{|
                           Ast.ind_name := "le";
                           Ast.ind_type := tProd (nNamed "n")
                                             (tInd
                                                {|
                                                inductive_mind := "Coq.Init.Datatypes.nat";
                                                inductive_ind := 0 |} [])
                                             (tProd nAnon
                                                (tInd
                                                   {|
                                                   inductive_mind := "Coq.Init.Datatypes.nat";
                                                   inductive_ind := 0 |} [])
                                                (tSort (Universe.make'' (Level.lProp, false) [])));
                           Ast.ind_kelim := [InProp];
                           Ast.ind_ctors := [("le_n"%string,
                                             tProd (nNamed "n"%string)
                                               (tInd
                                                  {|
                                                  inductive_mind := "Coq.Init.Datatypes.nat";
                                                  inductive_ind := 0 |} []) (tApp (tRel 1) [tRel 0; tRel 0]), 0);
                                            ("le_S"%string,
                                            tProd (nNamed "n"%string)
                                              (tInd
                                                 {|
                                                 inductive_mind := "Coq.Init.Datatypes.nat";
                                                 inductive_ind := 0 |} [])
                                              (tProd (nNamed "m")
                                                 (tInd
                                                    {|
                                                    inductive_mind := "Coq.Init.Datatypes.nat";
                                                    inductive_ind := 0 |} [])
                                                 (tProd nAnon (tApp (tRel 2) [tRel 1; tRel 0])
                                                    (tApp (tRel 3)
                                                       [tRel 2;
                                                       tApp
                                                         (tConstruct
                                                            {|
                                                            inductive_mind := "Coq.Init.Datatypes.nat";
                                                            inductive_ind := 0 |} 1 []) [
                                                         tRel 1]]))), 2)];
                           Ast.ind_projs := [] |}];
        Ast.ind_universes := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) |})
  (Hind : declared_inductive Σ
         {|
         Ast.ind_finite := Finite;
         Ast.ind_npars := 1;
         Ast.ind_params := [{|
                            Ast.decl_name := nNamed "n";
                            Ast.decl_body := None;
                            Ast.decl_type := tInd
                                               {|
                                               inductive_mind := "Coq.Init.Datatypes.nat";
                                               inductive_ind := 0 |} [] |}];
         Ast.ind_bodies := [{|
                            Ast.ind_name := "le";
                            Ast.ind_type := tProd (nNamed "n")
                                              (tInd
                                                 {|
                                                 inductive_mind := "Coq.Init.Datatypes.nat";
                                                 inductive_ind := 0 |} [])
                                              (tProd nAnon
                                                 (tInd
                                                    {|
                                                    inductive_mind := "Coq.Init.Datatypes.nat";
                                                    inductive_ind := 0 |} [])
                                                 (tSort (Universe.make'' (Level.lProp, false) [])));
                            Ast.ind_kelim := [InProp];
                            Ast.ind_ctors := [("le_n",
                                              tProd (nNamed "n")
                                                (tInd
                                                   {|
                                                   inductive_mind := "Coq.Init.Datatypes.nat";
                                                   inductive_ind := 0 |} []) (tApp (tRel 1) [tRel 0; tRel 0]), 0);
                                             ("le_S",
                                             tProd (nNamed "n")
                                               (tInd
                                                  {|
                                                  inductive_mind := "Coq.Init.Datatypes.nat";
                                                  inductive_ind := 0 |} [])
                                               (tProd (nNamed "m")
                                                  (tInd
                                                     {|
                                                     inductive_mind := "Coq.Init.Datatypes.nat";
                                                     inductive_ind := 0 |} [])
                                                  (tProd nAnon (tApp (tRel 2) [tRel 1; tRel 0])
                                                     (tApp (tRel 3)
                                                        [tRel 2;
                                                        tApp
                                                          (tConstruct
                                                             {|
                                                             inductive_mind := "Coq.Init.Datatypes.nat";
                                                             inductive_ind := 0 |} 1 []) [
                                                          tRel 1]]))), 2)];
                            Ast.ind_projs := [] |}];
         Ast.ind_universes := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) |}
         {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}
         {|
         Ast.ind_name := "le";
         Ast.ind_type := tProd (nNamed "n")
                           (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                           (tProd nAnon
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                              (tSort (Universe.make'' (Level.lProp, false) [])));
         Ast.ind_kelim := [InProp];
         Ast.ind_ctors := [("le_n",
                           tProd (nNamed "n")
                             (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                             (tApp (tRel 1) [tRel 0; tRel 0]), 0);
                          ("le_S",
                          tProd (nNamed "n")
                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                            (tProd (nNamed "m")
                               (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                               (tProd nAnon (tApp (tRel 2) [tRel 1; tRel 0])
                                  (tApp (tRel 3)
                                     [tRel 2;
                                     tApp
                                       (tConstruct
                                          {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1
                                          []) [tRel 1]]))), 2)];
         Ast.ind_projs := [] |}).

Lemma typeNat Γ':
  { s &
  Σ;;; Γ'
    |- tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [] : tSort s}.
Proof.
  eexists.
Admitted.

Lemma wfLocalLeParams:
  wf_local Σ
           (Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])).
Proof.
  constructor.
  apply Hwf.
  cbn.
  apply typeNat.
Qed.

Lemma wfLocalindInst:
  wf_local Σ
    (((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
      Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
     Ast.vass (nNamed "inst")
     (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])).
Proof.
  constructor.
  2: {
    cbn.
    admit. (* Le applied *)
  }
  constructor.
  2: {
    cbn.
    apply typeNat.
  }
  apply wfLocalLeParams.
Admitted.


Lemma wfLocalP:
  wf_local Σ
    ((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
     vass (nNamed "p")
       (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
          (tProd (nNamed "inst")
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
             (tSort (NEL.sing (Level.lProp, false)))))).
Proof.
  edestruct typeNat.
  edestruct typeNat.
  constructor.
  2: {
    cbn.
    eexists.
    apply type_Prod.
    - apply t0.
    - apply type_Prod.
      + admit. (* leApplied *)
      + apply type_Sort.
        2: admit. (* universe *)
        apply wfLocalindInst.
  }
  apply wfLocalLeParams.
Admitted.


Lemma wfLocalBaseCase:
  wf_local Σ
    (((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
      vass (nNamed "p")
        (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
           (tProd (nNamed "inst")
              (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
              (tSort (NEL.sing (Level.lProp, false)))))),,
     vass (nNamed "H_le_n")
       (tApp (tRel 0)
          [tRel 1;
             tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])).
Proof.
  edestruct typeNat.
  constructor.
  + apply wfLocalP.
  + cbn.
    eexists.
    eapply type_App.
    * apply type_Rel.
      -- apply wfLocalP.
      -- cbn. reflexivity.
    * reflexivity.
    * congruence.
    * econstructor.
      3: {
        apply type_Rel.
        apply wfLocalP.
        reflexivity.
      }
      2: {
        cbn.
        apply cumul_refl.
        constructor.
        - constructor.
          constructor.
        - admit. (* reduce universe *)
      }
      1: {
        cbn.
        apply type_Prod.
        apply t0.
        admit. (* depends on B *)
      }
      econstructor.
      3: {
        eapply type_App.
        - eapply type_Construct.
          2-3: admit. (* le inductive prop *)
          apply wfLocalP.
        - reflexivity.
        - congruence.
        - econstructor.
          4: constructor.
          3: {
            apply type_Rel.
            apply wfLocalP.
            reflexivity.
          }
          2: {
            cbn.
            Print type_of_constructor.
            admit. (* peano constructor *)
          }
          cbn.
          apply type_Prod.
          + apply t0.
          + admit. (* depends on B *)
      }
      2: {
        constructor.
        admit.
      }
      2: {
        admit. (* cant unify existential *)
      }
      apply type_Prod.
      -- admit. (* depends on B *)
      -- admit. (* depends on B *)
Admitted.

Lemma wfLocalBaseCaseSndArgs:
  wf_local Σ
    (((((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
        vass (nNamed "p")
          (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
             (tProd (nNamed "inst")
                (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
                (tSort (NEL.sing (Level.lProp, false)))))),,
       vass (nNamed "H_le_n")
         (tApp (tRel 0)
            [tRel 1;
            tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])),,
      Ast.vass (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
     Ast.vass nAnon
     (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])).
Proof.
  constructor.
  - constructor.
    + apply wfLocalBaseCase.
    + cbn.
      apply typeNat.
  - admit. (* le applied *)
Admitted.


Lemma wfLocalCases:
  wf_local Σ
    ((((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
       vass (nNamed "p")
         (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
            (tProd (nNamed "inst")
               (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
               (tSort (NEL.sing (Level.lProp, false)))))),,
      vass (nNamed "H_le_n")
        (tApp (tRel 0)
           [tRel 1;
           tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])),,
     vass (nNamed "H_le_S")
       (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
          (tProd nAnon
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])
             (tApp (tRel 3)
                [tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                   [tRel 1];
                tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                     [tRel 4; tRel 1; tRel 0]])))).
Proof.
  constructor.
  - apply wfLocalBaseCase.
  - cbn.
    edestruct typeNat.
    eexists.
    apply type_Prod.
    + apply t0.
    + apply type_Prod.
      * admit. (* le apply *)
      * eapply type_App.
        -- apply type_Rel.
           ++ apply wfLocalBaseCaseSndArgs.
           ++ reflexivity.
        -- reflexivity.
        -- congruence.
        -- cbn.
           admit. (* typing_spine application *)
Admitted.

Lemma typeF:
  ∑ s : universe,
    Σ;;;
    (vass (nNamed "H_le_S")
       (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
          (tProd nAnon
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])
             (tApp (tRel 3)
                [tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                   [tRel 1];
                tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                  [tRel 4; tRel 1; tRel 0]])))
     :: vass (nNamed "H_le_n")
          (tApp (tRel 0)
             [tRel 1;
             tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])
        :: vass (nNamed "p")
             (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                (tProd (nNamed "inst")
                   (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                      [tRel 1; tRel 0]) (tSort (NEL.sing (Level.lProp, false)))))
           :: Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
              :: Γ)
    |- tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
         (tProd (nNamed "inst")
            (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 4; tRel 0])
            (tApp (tRel 4) [tRel 1; tRel 0])) : TemplateTerm.tSort s.
Proof.
  edestruct typeNat.
  eexists.
  apply type_Prod.
  + apply t0.
  + admit. (* instance typed *)
Admitted.


Lemma wfLocalFixContext:
  wf_local Σ
    ((((Γ,, Ast.vass (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])),,
       vass (nNamed "p")
         (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
            (tProd (nNamed "inst")
               (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
               (tSort (NEL.sing (Level.lProp, false)))))),,
      vass (nNamed "H_le_n")
        (tApp (tRel 0)
           [tRel 1;
           tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])),,
     vass (nNamed "H_le_S")
       (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
          (tProd nAnon
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])
             (tApp (tRel 3)
                [tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                   [tRel 1];
                tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                  [tRel 4; tRel 1; tRel 0]]))) ,,,
     fix_context
       [{|
        dname := nNamed "f";
        dtype := tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                   (tProd (nNamed "inst")
                      (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                         [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0]));
        dbody := tLambda nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                   (tLambda (nNamed "inst")
                      (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                         [tRel 5; tRel 0])
                      (tCase ({| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}, 1)
                         (tLambda nAnon
                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                            (tLambda (nNamed "inst")
                               (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                  [tRel 7; tRel 0]) (tApp (tRel 7) [tRel 1; tRel 0]))) 
                         (tRel 0)
                         [(0, tRel 4);
                         (2,
                         tLambda (nNamed "m")
                           (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                           (tLambda nAnon
                              (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                 [tRel 7; tRel 0]) (tApp (tRel 5) [tRel 1; tRel 0])))]));
        rarg := 1 |}]).
Proof.
  constructor.
  - apply wfLocalCases.
  - cbn.
    apply typeF.
Qed.

Lemma wfLocalF:
  wf_local Σ
    ( Ast.vass (nNamed "f")
             (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                (tProd (nNamed "inst")
                   (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                      [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0])))
           :: vass (nNamed "H_le_S")
                (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                   (tProd nAnon
                      (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                         [tRel 3; tRel 0])
                      (tApp (tRel 3)
                         [tApp
                            (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                            [tRel 1];
                         tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                           [tRel 4; tRel 1; tRel 0]])))
              :: vass (nNamed "H_le_n")
                   (tApp (tRel 0)
                      [tRel 1;
                      tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 [])
                        [tRel 1]])
                 :: vass (nNamed "p")
                      (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                         (tProd (nNamed "inst")
                            (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                               [tRel 1; tRel 0]) (tSort (NEL.sing (Level.lProp, false)))))
                    :: Ast.vass (nNamed "n")
                    (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) :: Γ).
Proof.
  constructor.
  - apply wfLocalCases.
  - cbn.
    apply typeF.
Qed.


Lemma wfLocalFmInst:
  wf_local Σ
    (Ast.vass (nNamed "inst")
       (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 5; tRel 0])
     :: Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
        :: Ast.vass (nNamed "f")
             (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                (tProd (nNamed "inst")
                   (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                      [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0])))
           :: vass (nNamed "H_le_S")
                (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                   (tProd nAnon
                      (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                         [tRel 3; tRel 0])
                      (tApp (tRel 3)
                         [tApp
                            (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                            [tRel 1];
                         tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                           [tRel 4; tRel 1; tRel 0]])))
              :: vass (nNamed "H_le_n")
                   (tApp (tRel 0)
                      [tRel 1;
                      tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 [])
                        [tRel 1]])
                 :: vass (nNamed "p")
                      (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                         (tProd (nNamed "inst")
                            (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                               [tRel 1; tRel 0]) (tSort (NEL.sing (Level.lProp, false)))))
                    :: Ast.vass (nNamed "n")
                    (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) :: Γ).
Proof.
  constructor.
  - constructor.
    + apply wfLocalF.
    + cbn.
      apply typeNat.
  - cbn.
    admit. (* le applied *)
Admitted.

Lemma wfLocalFmInstmInst:
  wf_local Σ
    (vass (nNamed "inst")
       (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 7; tRel 0])
     :: Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
        :: Ast.vass (nNamed "inst")
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 5; tRel 0])
           :: Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
              :: Ast.vass nAnon
                   (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                      (tProd (nNamed "inst")
                         (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                            [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0])))
                 :: vass (nNamed "H_le_S")
                      (tProd (nNamed "m")
                         (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                         (tProd nAnon
                            (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                               [tRel 3; tRel 0])
                            (tApp (tRel 3)
                               [tApp
                                  (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}
                                     1 []) [tRel 1];
                               tApp
                                 (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                                 [tRel 4; tRel 1; tRel 0]])))
                    :: vass (nNamed "H_le_n")
                         (tApp (tRel 0)
                            [tRel 1;
                            tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 [])
                              [tRel 1]])
                       :: vass (nNamed "p")
                            (tProd nAnon
                               (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                               (tProd (nNamed "inst")
                                  (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                     [tRel 1; tRel 0]) (tSort (NEL.sing (Level.lProp, false)))))
                          :: Ast.vass (nNamed "n")
                          (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) :: Γ).
Proof.
  admit. (* wfLocal weakening with wfLocalFmInst *)
Admitted.

Lemma wfLocalFmInstmInstmInst:
  wf_local Σ
    (Ast.vass (nNamed "inst")
       (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 7; tRel 0])
     :: Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
        :: Ast.vass nAnon
             (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 7; tRel 0])
           :: Ast.vass (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
              :: Ast.vass (nNamed "inst")
                   (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                      [tRel 5; tRel 0])
                 :: Ast.vass nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                    :: Ast.vass nAnon
                         (tProd nAnon
                            (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                            (tProd (nNamed "inst")
                               (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                  [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0])))
                       :: vass (nNamed "H_le_S")
                            (tProd (nNamed "m")
                               (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                               (tProd nAnon
                                  (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                     [tRel 3; tRel 0])
                                  (tApp (tRel 3)
                                     [tApp
                                        (tConstruct
                                           {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1
                                           []) [tRel 1];
                                     tApp
                                       (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}
                                          1 []) [tRel 4; tRel 1; tRel 0]])))
                          :: vass (nNamed "H_le_n")
                               (tApp (tRel 0)
                                  [tRel 1;
                                  tApp
                                    (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0
                                       []) [tRel 1]])
                             :: vass (nNamed "p")
                                  (tProd nAnon
                                     (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                     (tProd (nNamed "inst")
                                        (tApp
                                           (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}
                                              []) [tRel 1; tRel 0]) (tSort (NEL.sing (Level.lProp, false)))))
                                :: Ast.vass (nNamed "n")
                                     (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   :: Γ).
Proof.
  admit. (* wfLocal weakening with wfLocalFmInst *)
Admitted.




End LeLemma.






Lemma leElimTyping Σ Γ ind_body mind_body ind:
  ind= mkInd "Coq.Init.Peano.le" 0 ->
  ind_body={|
               ind_name := "le";
               ind_type := tProd (nNamed "n")
                             (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                             (tProd nAnon
                                (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                (tSort (Universe.make'' (Level.lProp, false) [])));
               ind_kelim := [InProp];
               ind_ctors := [("le_n",
                             tProd (nNamed "n")
                               (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                               (tApp (tRel 1) [tRel 0; tRel 0]), 0);
                            ("le_S",
                            tProd (nNamed "n")
                              (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                              (tProd (nNamed "m")
                                 (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                 (tProd nAnon (tApp (tRel 2) [tRel 1; tRel 0])
                                    (tApp (tRel 3)
                                       [tRel 2;
                                       tApp
                                         (tConstruct
                                            {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1
                                            []) [tRel 1]]))), 2)];
               ind_projs := [] |} ->

  mind_body = {|
ind_finite := Finite;
ind_npars := 1;
ind_params := [{|
               decl_name := nNamed "n";
               decl_body := None;
               decl_type := tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [] |}];
ind_bodies := [ind_body];
ind_universes := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) |} ->

  wf_local Σ Γ ->
  declared_minductive Σ (inductive_mind ind) mind_body ->
  declared_inductive Σ mind_body ind ind_body ->
  Σ;;;Γ |-
(tLambda (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
   (tLambda (nNamed "p")
      (tProd nAnon (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
         (tProd (nNamed "inst")
            (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
            (tSort (NEL.sing (Level.lProp, false)))))
      (tLambda (nNamed "H_le_n")
         (tApp (tRel 0)
            [tRel 1;
            tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])
         (tLambda (nNamed "H_le_S")
            (tProd (nNamed "m"%string) (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
               (tProd nAnon
                  (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])
                  (tApp (tRel 3)
                     [tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                        [tRel 1];
                     tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                       [tRel 4; tRel 1; tRel 0]])))
            (tFix
               [{|
                dname := nNamed "f"%string;
                dtype := tProd nAnon
                           (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                           (tProd (nNamed "inst"%string)
                              (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                 [tRel 4; tRel 0]) (tApp (tRel 4) [tRel 1; tRel 0]));
                dbody := tLambda nAnon
                           (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                           (tLambda (nNamed "inst"%string)
                              (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                 [tRel 5; tRel 0])
                              (tCase ({| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |}, 1)
                                 (tLambda nAnon
                                    (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                    (tLambda (nNamed "inst"%string)
                                       (tApp
                                          (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                          [tRel 7; tRel 0]) (tApp (tRel 7) [tRel 1; tRel 0]))) 
                                 (tRel 0)
                                 [(0, tRel 4);
                                 (2,
                                 tLambda (nNamed "m"%string)
                                   (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
                                   (tLambda nAnon
                                      (tApp
                                         (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} [])
                                         [tRel 7; tRel 0]) (tApp (tRel 5) [tRel 1; tRel 0])))]));
                rarg := 1 |}] 0)))))
:
tProd (nNamed "n") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
  (tProd (nNamed "p")
     (tProd (nNamed "H") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
        (tProd nAnon
           (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 1; tRel 0])
           (tSort (Universe.make'' (Level.lProp, false) []))))
     (tProd nAnon
        (tApp (tRel 0)
           [tRel 1;
           tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 0 []) [tRel 1]])
        (tProd nAnon
           (tProd (nNamed "m") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
              (tProd (nNamed "H")
                 (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 3; tRel 0])
                 (tApp (tRel 3)
                    [tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 [])
                       [tRel 1];
                    tApp (tConstruct {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} 1 [])
                      [tRel 4; tRel 1; tRel 0]])))
           (tProd (nNamed "H") (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} [])
              (tProd (nNamed "inst")
                 (tApp (tInd {| inductive_mind := "Coq.Init.Peano.le"; inductive_ind := 0 |} []) [tRel 4; tRel 0])
                 (tApp (tRel 4) [tRel 1; tRel 0])))))).
Proof.
  intros -> -> -> Hwf Hmind Hind.
  edestruct typeNat as [x Hnat];try eassumption.
  cbn.
  (* repeat rewrite namingEq2. *)
  apply type_Lambda2. (* param *)
  apply type_LambdaL. (* p *)
  1-2: now repeat rewrite namingEq2.
  apply type_LambdaL. (* le_n Case *)
  1-2: now repeat rewrite namingEq2.
  apply type_LambdaL. (* le_S Case *)
  1-2: now repeat rewrite namingEq2.
  match goal with
    |- _ ;;; _ |- tFix [ ?Body ] 0 : ?T =>
    replace T with (dtype Body)
  end.
  2: cbn;now repeat rewrite namingEq2.
  apply type_Fix.
  1: admit. (* fix guard *)
  1: reflexivity. (* find function *)
  1: { (* wf_local env *)
    now apply wfLocalFixContext.
  }
  constructor.
  2: constructor.
  split.
  2: reflexivity. (* isLambda *)
  cbn.
  apply type_Lambda2. (* index *)
  apply type_Lambda2. (* instance *)

  (* evar (args:list term). *)
  set (args:=[tRel 6;tRel 1]).
  match goal with
    |- _;;;_ |- tCase (?ind, ?npar) ?p ?c ?brs : ?t =>
    replace t with (mkApps p (skipn npar args ++ [c]))
  end.
  2: admit. (* eta possible *)
  subst args.
  (* cbn in H. *)
  (* cbn in H0. *)
  eapply type_Case.
  - cbn.
    apply Hind.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - apply type_Lambda2.
    rewrite namingEq2.
    apply type_LambdaL.
    1-2: now repeat rewrite namingEq2.
    eapply type_App.
    + apply type_Rel.
      * unfold snoc, app_context.
        now apply wfLocalFmInstmInst.
      * cbn. reflexivity.
    + reflexivity.
    + congruence.
    + cbn. (* typing_spine *)
      econstructor.
      * admit.
      * admit.
      * apply type_Rel.
        -- admit.
        -- cbn. reflexivity.
      * econstructor.
        -- admit.
        -- admit.
        -- apply type_Rel.
           ++ admit.
           ++ cbn. reflexivity.
        -- admit.
  - cbn. (* le_sort_family *)
    admit.
  - cbn.
    match goal with
      |- _ ;;; _,,?X |- _ :
                    tApp ?b ?xs =>
      replace (tApp b xs) with (lift0 1 (decl_type X))
    end.
    2: {
      cbn.
      reflexivity.
    }
    apply type_Rel.
    2: {
      cbn. reflexivity.
    } (* wf_local *)
    unfold snoc, app_context.
    now apply wfLocalFmInst.
  - cbn. reflexivity.
  - constructor.
    2: constructor.
    3: constructor.
    + cbn.
      repeat split.
      * unfold snoc, app_context.
        eapply type_Rel2.
        2: {
          reflexivity.
        }
        2: {
          cbn.
          admit. (* needs eta conversion *)
        }
        now apply wfLocalFmInst.
      * admit. (* app *)
    + cbn.
      repeat split.
      * rewrite namingEq2.
        do 2 apply type_Lambda2.
        eapply Generation.type_mkApps.
        -- do 2 apply type_Lambda2.
           eapply type_App.
           ++ apply type_Rel.
              ** unfold snoc, app_context.
                 now apply wfLocalFmInstmInstmInst.
              ** cbn. reflexivity.
           ++ reflexivity.
           ++ congruence.
           ++ cbn. admit. (* typing_spine *)
        -- admit. (* typing_spine *)
      * cbn.
        apply type_Prod.
        -- apply Hnat.
        -- apply type_Prod.
           ++ admit. (* app *)
           ++ admit. (* app *)
Admitted.

(*

  | type_Case : forall (indnpar : inductive × nat) (u : universe_instance) (p c : term) 
                  (brs : list (nat × term)) (args : list term),
                let ind := indnpar.1 in
                let npar := indnpar.2 in
                forall (mdecl : mutual_inductive_body) (idecl : one_inductive_body),
                declared_inductive Σ.1 mdecl ind idecl ->
                Ast.ind_npars mdecl = npar ->
                let params := firstn npar args in
                forall (ps : universe) (pty : term),
                build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
                Σ;;; Γ |- p : pty ->
                existsb (leb_sort_family (universe_family ps)) (Ast.ind_kelim idecl) ->
                Σ;;; Γ |- c : mkApps (tInd ind u) args ->
                forall btys : list (nat × term),
                map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
                All2
                  (fun br bty : nat × term => (br.1 = bty.1 × Σ;;; Γ |- br.2 : bty.2) × Σ;;; Γ |- bty.2 : tSort ps)
                  brs btys -> Σ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c])

 *)
