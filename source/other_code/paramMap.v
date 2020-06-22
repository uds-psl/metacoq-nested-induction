Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.

Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.

Open Scope list_scope.
Open Scope nat_scope.

Require Import de_bruijn_print.





Definition hasSat (xs:list bool) := fold_left orb xs false.

Fixpoint findRel (nested: kername -> nat -> option (term×term)) (k:nat) (u:term) :=
  match u with
  | tRel n => Nat.eqb n k
  | tEvar ev args => hasSat(map (findRel nested k) args)
  | tProd na A B => orb (findRel nested k A) (findRel nested (S k) B)
  | tLambda na T M => orb (findRel nested k T) (findRel nested (S k) M)
  | tLetIn na b ty b' => orb (orb (findRel nested k b) (findRel nested k ty)) (findRel nested (S k) b')
  | tApp t1 t2 =>
    orb (findRel nested k t1) (findRel nested k t2)
  | tCase ind p c brs => orb (orb (findRel nested k p) (findRel nested k c)) (hasSat (map (fun p => findRel nested k p.2) brs))
  | tProj p c => (findRel nested k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel nested k) (findRel nested k')) mfix) in hasSat mfix'
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel nested k) (findRel nested k')) mfix) in hasSat mfix'
  | _ => false
  end.


Definition trans := TemplateToPCUIC.trans.

Definition trivialPred (X:Type) (x:X) := True.
Definition trivialProof (X:Type) (x:X) : trivialPred X x := I.
Definition tr1 := trans <% trivialPred %>.
Definition tr2 := trans <% trivialProof %>.





Definition extendName pre na :=
  match na with
    nAnon => nAnon
  | nNamed s => nNamed (pre +s s)
  end.

Definition generatePCall2 paramCount recpos ppos app appList n args : option term :=
      if Nat.eqb n recpos then
        Some(
            mkApps
              (
                mkApps (tRel ppos) (skipn paramCount args)
              )
              [mkApps app appList]
          )
      else
        None.

From MetaCoq.PCUIC Require Import PCUICSize.


Lemma fold_right_map {X Y Z:Type} (f:X->Y) (g:Y->Z->Z) a xs:
  fold_right (fun t x => g (f t) x) a xs =
  fold_right (fun t x => g t x) a (map f xs).
Proof.
  induction xs.
  - reflexivity.
  - cbn.
    f_equal.
    apply IHxs.
Defined.

Definition isProd t :=
match t with 
tProd _ _ _ => true
| _ => false
end.


Fixpoint termsize (t:term) : nat :=
  match t with
    tEvar _ xs => 1+fold_right (fun t x => termsize t + x) 0 xs
  | tProd _ t1 t2 => 1+termsize t1 + termsize t2
  | tLambda _ t1 t2 => 1+termsize t1 + termsize t2
  | tLetIn _ t1 t2 t3 => 1+termsize t1 + termsize t2 + termsize t3
  | tApp t1 t2 => 1+termsize t1 + termsize t2
  | tCase _ t1 t2 xs => 1+fold_right (fun t x => termsize (snd t) + x) (termsize t1 + termsize t2) xs
  | tProj _ t1 => 1+ termsize t1
  | _ => 1
  end.

Lemma termSizeLifting t n k: 
  termsize (lift n k t) = termsize t.
Proof.
  induction t in k |- * using term_forall_list_ind;cbn;try congruence.
  - f_equal.
    induction X.
    + reflexivity.
    + cbn. now rewrite IHX.
  - f_equal.
    rewrite fold_right_map.
    symmetry;rewrite fold_right_map;symmetry.
    f_equal.
    + now rewrite IHt1, IHt2.
    + induction X.
      * reflexivity.
      * cbn. rewrite IHX.
        f_equal.
        destruct x.
        unfold on_snd.
        simpl in *.
        now rewrite p0.
Qed.

Require Import Lia.

Lemma fold_right_sum_leq {X} (f:X->nat) a n xs:
  In a xs ->
  f a <= fold_right (fun t (x : nat) => f t + x) n xs.
Proof.
  intros H.
  induction xs.
  - now contradict H.
  - destruct H as [<- | H].
    + cbn.
      lia.
    + cbn.
      specialize (IHxs H).
      lia.
Defined.


Lemma size_induction X (f:X->nat) (P:X->Type):
  (forall x, (forall y, f y<f x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros. apply X0.
  assert(forall n y, f y < n -> P y).
  {
    induction n.
    - lia.
    - intros.
      apply X0.
      intros.
      apply IHn.
      lia.
  }
  apply X1.
Defined.

Definition term_size_ind := size_induction term termsize.


Fixpoint getInner (t:term) (xs:list term) : term*list term :=
  match t with
  | tApp t1 t2 => getInner t1 (t2::xs)
  | _ => (t,xs)
  end.

    Require Import Arith.

Lemma lt_plus_S_l n m: n<S(n+m).
Proof.
  apply le_lt_n_Sm, le_plus_l.
Defined.

Lemma lt_plus_S_r n m: n<S(m+n).
Proof.
  apply le_lt_n_Sm, le_plus_r.
Defined.

Import ListNotations.

Open Scope list_scope.

Definition generateInductiveAssumptions
  (paramCount : nat) (nested : kername -> nat -> option (term × term))
  (generateInduction : bool) (recpos ppos fpos : nat) 
  (app : term) (appList : list term)
  (generateDummy generateProof mainApp isInner : bool) 
  (body : term) : option term.
revert 
  paramCount nested 
  generateInduction recpos ppos fpos 
  app appList 
  generateDummy generateProof mainApp isInner.
refine (term_size_ind _ _ body).
clear body.
intros.
rename x into body.
revert X.
refine(
  let dummyResult :=
      if generateDummy then
        if generateProof then
          Some (mkApps (tApp tr2 body) [mkApps app appList])
        else
          Some (mkApps (tApp tr1 body) [mkApps app appList])
      else
        None
  in
    match body with
    | tRel n => (* inductive *)
      fun generateInductiveAssumptions =>
      if mainApp then
        Some (mkApps app appList)
      else
        generatePCall2 paramCount recpos (if generateProof then fpos else ppos) app appList n []

    | tInd {| inductive_mind := name; inductive_ind := idx |} u =>
      fun generateInductiveAssumptions =>
      if isInner then
        match nested name idx with
          None => dummyResult
        | Some (t1,t2) =>
          Some (if generateProof then t2 else t1)
        end
      else
        dummyResult
    | tConst name u =>
      fun generateInductiveAssumptions =>
      if isInner then
        match nested name 0 with
          None => dummyResult
        | Some (t1,t2) =>
          Some (if generateProof then t2 else t1)
        end
      else
        dummyResult

    | tApp t1 t2 =>
      fun generateInductiveAssumptions =>
      match getInner body [] with
      | (tRel n, args) => (* don't apply all but only indices *)
        if mainApp then
          Some(mkApps app appList)
        else
          generatePCall2 paramCount recpos (if generateProof then fpos else ppos) app appList n args
      | (tInd _ _, _) | (tConst _ _, _) =>
        let isRec := findRel nested recpos body in
        if andb (negb isInner) (negb isRec) then
          dummyResult
        else
          match generateInductiveAssumptions t1 _ paramCount nested generateInduction (recpos) (ppos) (fpos) (tRel 0) [] false generateProof mainApp true with
            None => dummyResult
          | Some x =>
            Some (mkApps x
                    ([t2] ++
                    match generateInductiveAssumptions (lift0 1 t2) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] true false mainApp false with
                      None => []
                    | Some a => [(tLambda nAnon t2 a)]
                    end
                    ++
                    (if generateProof then
                    match generateInductiveAssumptions (lift0 1 t2) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] true generateProof mainApp false with
                      None => []
                    | Some a => [(tLambda nAnon t2 a)]
                    end
                     else [])
                    ++
                    (
                      if negb isInner then
                        [mkApps app appList]
                        else []
                    ))
                 )
          end
    | _ => None
      end
    | tProd na α inner => (* normal ArgumentChain *)
      fun generateInductiveAssumptions =>
      if generateProof then
        let appList2 := map (lift0 1) appList ++ [tRel 0] ++
        match (if generateInduction then generateInductiveAssumptions (lift0 1 α) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] false generateProof false false else None) with
          None => []
        | Some fα =>
          [fα]
        end in
        innerBody <- generateInductiveAssumptions inner _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (lift0 1 app) appList2 generateDummy generateProof mainApp false;;
        Some (tLambda na α innerBody)
      else
        (
      innerBody <- generateInductiveAssumptions inner _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (lift0 1 app) ((map (lift0 1) appList)++[tRel 0]) generateDummy generateProof mainApp false ;;
      match (if generateInduction then generateInductiveAssumptions (lift0 1 α) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] false generateProof false false else None) with
        None => Some (tProd na α innerBody)
      | Some IHα => Some (
                    tProd na α
                    (
                      tProd (extendName "IH_" na) (IHα) (lift0 1 innerBody)
                    )
                  )
      end
      )


     | _ => fun _ => None
    end
).
  Unshelve.
  all: simpl;try rewrite termSizeLifting;(apply lt_plus_S_l + apply lt_plus_S_r).
Defined.


