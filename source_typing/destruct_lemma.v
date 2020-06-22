

Require Import MetaCoq.Template.All.
Require Import List String.
Import ListNotations MonadNotation.
Require Import MetaCoq.Template.Pretty.

Load de_bruijn_print.
Load non_uniform.

Require Import Even.
Require Import Recdef.

Scheme Equality for sort_family.

Definition canElim (s : sort_family) (xs:list sort_family) : bool.
Proof.
  induction xs as [|x xs].
  - exact false.
  - destruct (sort_family_eq_dec s x).
    + exact true.
    + exact IHxs.
Defined.

Goal forall x xs, canElim x xs = true <-> In x xs.
Proof.
  induction xs;simpl canElim;simpl In.
  - split;auto.
  - split.
    + destruct sort_family_eq_dec  as [->|];auto.
      now intros H%IHxs.
    + intros [-> | H%IHxs];destruct sort_family_eq_dec;congruence.
Qed.

Unset Strict Unquote Universe Mode. (* for universe errors todo: should be done properly *)
Definition getMaxElim (xs:list sort_family) :=
  if canElim InType xs then <% Type %> else (* todo: is this always the correct Level? *)
    if canElim InSet xs then <% Set %> else
      <% Prop %>.

Fixpoint remove_lambdas (t:term) : term :=
  match t with
  | tLambda _ _ t2 => remove_lambdas t2
  | _ => t
  end.
Fixpoint remove_prods (t:term) : term :=
  match t with
  | tProd _ _ t2 => remove_prods t2
  | _ => t
  end.

Fixpoint collect_prods (t:term) : list (context_decl) :=
  match t with
  | tProd n t1 t2 => (vass n t1)::collect_prods t2
  | _ => []
  end.
Fixpoint collect_lambdas (t:term) : list (context_decl) :=
  match t with
  | tLambda n t1 t2 => (vass n t1)::collect_lambdas t2
  | _ => []
  end.

Definition count_prods (t : term) : nat := #|collect_prods t|.

Fixpoint replaceLastOffset (f:nat -> term -> term) (off:nat) (u:term) :=
  match u with
  | tProd n h t => tProd n h (replaceLastOffset f (S off) t)
  | tLambda na T M => tLambda na T (replaceLastOffset f (S off) M)
  | tLetIn na b ty b' =>
      tLetIn na b ty (replaceLastOffset f (S off) b')
  | _ => (f off u)
  end.


Definition replaceLastLambda (t:term) (u:term) := it_mkLambda_or_LetIn (rev(collect_lambdas u)) t.
Definition replaceLastProd (t:term) (u:term) := it_mkProd_or_LetIn (rev(collect_prods u)) t.
Definition replaceLastLambda' (t:term) (u:term) := replaceLastLambda u t.
Definition replaceLastProd' (t:term) (u:term) := replaceLastProd u t.

Definition mapProdToLambda (u:term) : term :=
  let prods := collect_prods u in
  it_mkLambda_or_LetIn (rev prods) (remove_arity #|prods| u).


Definition createAppChainOff (o:nat) (t:term) (count:nat) :=
              (mkApps t
                (nat_rec
                    _
                    []
                    (fun n a => cons (tRel (o+n)) a)
                    count
                )
              ).

Definition createAppChain := createAppChainOff 0.

Definition id {X:Type} := fun (x:X) => x.

Definition hasSat (xs:list bool) := fold_left orb xs false.

Fixpoint findRel (k:nat) (u:term) :=
  match u with
  | tRel n => n =? k
  | tEvar ev args => hasSat(map (findRel k) args)
  | tCast c kind ty => orb (findRel k c) (findRel k ty)
  | tProd na A B => orb (findRel k A) (findRel (S k) B)
  | tLambda na T M => orb (findRel k T) (findRel (S k) M)
  | tLetIn na b ty b' => orb (orb (findRel k b) (findRel k ty)) (findRel (S k) b')
  | tApp u0 v => findRel k u0
  | tCase ind p c brs => orb (orb (findRel k p) (findRel k c)) (hasSat (map (fun p => findRel k p.2) brs))
  | tProj p c => (findRel k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel k) (findRel k')) mfix) in hasSat mfix'
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel k) (findRel k')) mfix) in hasSat mfix'
  | _ => false
  end.

Fixpoint substApp (s : term) (a:list term) (k : nat) (off:nat) (u : term) {struct u} : term :=
  match u with
  | tRel n =>
    if k =? n then (lift0 k) (tApp s a)
    else tRel n
  | tEvar ev args => tEvar ev (map (substApp s a k off) args)
  | tCast c kind ty => tCast (substApp s a k off c) kind (substApp s a k off ty)
  | tProd na A B => tProd na (substApp s a k off A) (substApp s a (S k) (S off) B)
  | tLambda na T M => tLambda na (substApp s a k off T) (substApp s a (S k) (S off) M)
  | tLetIn na b ty b' => tLetIn na (substApp s a k off b) (substApp s a k off ty) (substApp s a (S k) (S off) b')
  | tApp (tRel n) v => if k=? n then tApp (lift0 k s) ((map (substApp s a k off) v)++map (lift0 k) a) else mkApps (tRel n) (map (substApp s a k off) v)
  | tApp u0 v => mkApps (substApp s a k off u0) (map (substApp s a k off) v)
  | tCase ind p c brs => let brs' := map (on_snd (substApp s a k off)) brs in tCase ind (substApp s a k off p) (substApp s a k off c) brs'
  | tProj p c => tProj p (substApp s a k off c)
  | tFix mfix idx =>
    let off' := #|mfix| + off in
      let k' := #|mfix| + k in let mfix' := map (map_def (substApp s a k off) (substApp s a k' off')) mfix in tFix mfix' idx
  | tCoFix mfix idx =>
    let off' := #|mfix| + off in
      let k' := #|mfix| + k in let mfix' := map (map_def (substApp s a k off) (substApp s a k' off')) mfix in tFix mfix' idx
  | _ => u
  end.

Definition addHelper (repl:nat) (dest:term) (rest:term) (n:name) (h:term) (f:name->term->term->term) :=
  let newName :=
      match n with
        nAnon => "IH"
      | nNamed s => "IH_"+s s
      end
  in
  if findRel repl h then
    tProd
      (nNamed newName)
      (substApp dest [tRel 0] repl 0 h)
      rest
  else rest.

Fixpoint substAdd (repl:nat) (dest:term) (u:term) :=
  match u with
  | tProd n h t => tProd n h (addHelper repl dest (substAdd (S repl) dest t) n h tProd)
  | tLambda n h t => tLambda n h (addHelper repl dest (substAdd (S repl) dest t) n h tLambda)

  | tEvar ev args => tEvar ev (map (substAdd repl dest) args)
  | tCast c kind ty => tCast c kind (substAdd repl dest ty)
  | tLetIn na b ty b' =>
      tLetIn na b ty (substAdd (S repl) dest b')
  | tCase ind p c brs =>
      let brs' := map (on_snd (substAdd repl dest)) brs in
      tCase ind p c brs'
  | tProj p c => tProj p (substAdd repl dest c)
  | tFix mfix idx =>
      let k' := #|mfix| + repl in
      let mfix' := map (map_def (substAdd k' dest) (substAdd k' dest)) mfix in
      tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + repl in
      let mfix' := map (map_def (substAdd k' dest) (substAdd k' dest)) mfix in
      tCoFix mfix' idx
  | _ => u
  end.


Definition constrMapping (type:term) (paramCount:nat) (cons: (ident × term) × nat) (paramOffset:nat) (last:term->term) :=
          let (y,count) := cons in (* count=arguments of constructor case *)
          let (name,a) := y in
          replaceLastOffset (* replace tpye construction with call of p *)
            (fun _ => last)
            0
            (
              lift0 paramOffset (* lift parameter call over other cases *)
              (subst1 type paramCount (* tRel => inductive type *)
              (
              (remove_arity (* remove param quantification in constructor *)
                  paramCount
                  a
              )))
            ).

(* todo: split in enumerate and filteri *)
Fixpoint filteri {A} (f:nat->A->bool) (s0:nat) (l:list A) : list (nat×A) :=
  match l with
  | [] => []
  | x :: l0 => if f s0 x then (s0,x) :: filteri f (S s0) l0 else filteri f (S s0) l0
  end.

Definition addInductiveHypothesis (a:term) (tyLift:nat) (argCount:nat) (paramCount:nat) (lCount:nat) (rest:term) :=
  let recArgs :=
      (filteri
          (fun n t => findRel (n+paramCount+tyLift) (decl_type t))
          0
          (collect_prods (lift0 tyLift (remove_arity paramCount a)))
       ) in
  it_mkProd_or_LetIn
    (rev (mapi
       (fun k (y:(nat × context_decl)) =>
          let (a,t) := y in
          let name := decl_name t in
          let ty := decl_type t in
          let argDiff := k+argCount-a in
          {|
            decl_body := None;
            decl_name := nNamed (match name with nAnon => "IH" | nNamed n => "IH_" +s n end);
            decl_type :=
              replaceLastOffset
              (fun n t =>
                tApp
                  (tRel (n+argCount+k+lCount)) (* p *)
                  (match t with
                    | tApp _ a => skipn paramCount a (* indices *)
                    | _ => []
                    end ++
                        [
                          createAppChain
                            (* k inductive hypothesis before, n recursion guards, ath argument in chain *)
                            (tRel (n+argDiff-1)) (* the corresponding argument *)
                            n
                        ]
                  )
              )
              0
              (lift0 argDiff ty)
          |}
       )
       recArgs
    ))
    (lift0 #|recArgs| rest).


Definition quantifyCases (isInductive:bool) (ctors : list ((ident×term)×nat)) (paramCount:nat) (ind:inductive) (univ:universe_instance) :=
  let ctorCount := #|ctors| in
  let type := tInd ind univ in
      (* fold over constructors for cases *)
  (* can be omitted with type inference *)
        mapi
        (fun n (x:(ident × term) × nat) =>
          let (y,count) := x in (* count=arguments of constructor case *)
          let (name,a) := y in
          let lcount := n in (* how many cases before this *)
           vass
             (nNamed ("H_" +s name))
             (
               constrMapping type paramCount x (S lcount)
               (* replace tpye construction with call of p *)
               (fun type_app =>
                  let rest :=
                   tApp
                     (tRel (count+lcount)) (* p (after cases and arguments) *)
                      (match type_app with
                      | tApp _ xs => skipn paramCount xs (* transfer indices from type call to call of p *)
                      | _ => []
                      end
                      ++
                      [ (* last argument is instance *)
                        (* todo: empty apply *)
                        (* get constructor of type *)
                        createAppChain
                          (* apply with parameter *)
                          (* parameter is before p, arguments, cases and other parameter *)
                          (lift0
                             (1+count+lcount)
                             (createAppChain
                                (tConstruct ind lcount univ)
                                paramCount
                             )
                          )
                          (* apply with arguments *)
                          count
                      ])
                  in
                  if isInductive then
                    addInductiveHypothesis a (S lcount) count paramCount lcount rest
                  else rest
               )
             )
        ) ctors.

Definition getInductiveCalls (ctor:(ident×term)×nat) (paramExtraLift nuParamLift:nat) (trueParamCount nonUniformArgCount:nat) (fOff:nat) (argCount:nat) : list term :=
    let (y,count) := ctor in (* count=arguments of constructor case *)
    let (_,a) := y in
    let recArgs :=
        (filteri
              (fun n t => findRel (n+trueParamCount+nonUniformArgCount+paramExtraLift+nuParamLift) (decl_type t))
            0
            (collect_prods
               (lift0 nuParamLift
               (lift paramExtraLift nonUniformArgCount
                      (remove_arity (trueParamCount+nonUniformArgCount) a)
               )
               )
            )
            (* (collect_prods (remove_arity paramCount a)) *)
        ) in
    map
      (fun (y:(nat × context_decl)) =>
         let (a,t) := y in
         let name := decl_name t in
         let ty := decl_type t in
            replaceLastOffset
            (fun n t =>
              tApp
                (tRel (n+fOff)) (* f *)
                (match t with
                  | tApp _ a => skipn trueParamCount a (* indices *)
                  | _ => []
                  end ++
                      [
                        createAppChain
                          (tRel (n+(argCount-a-1))) (* the corresponding argument *)
                          n
                      ]
                )
            )
            0
            (mapProdToLambda (lift0 (argCount-a) ty))
            (* (mapProdToLambda (lift0 tyLift (remove_arity paramCount ty))) *)
      ) recArgs.

Print one_inductive_body.

Definition createElim (isInductive:bool) (ind:inductive) (univ:universe_instance) (ind_body:mutual_inductive_body) (returnType:option term) (nameFun:name->term->name) :=
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
  let allParamCount := ind_body.(ind_npars) in
  let trueParamCount := getParamCount one_body ind_body.(ind_npars) in
  let nonUniformArgCount := ind_body.(ind_npars) - trueParamCount in

  let allParams := ind_body.(ind_params) in
  let nonUniformParams := firstn nonUniformArgCount allParams in
  let trueParams := skipn nonUniformArgCount allParams in

  let trueParamCtors := one_body.(ind_ctors) in
  let allParamCtors := map (on_snd (plus nonUniformArgCount)) one_body.(ind_ctors) in

  let type := tInd ind univ in
  let ind_applied := (* typ applied with params *)
      mkApps type (mapi (fun i _ => tRel (trueParamCount-i-1)) trueParams)
  in
  let nuIndex_type := remove_arity trueParamCount one_body.(ind_type) in
  let trueIndex_type := remove_arity allParamCount one_body.(ind_type) in
  let allIndCount := (* count of indices and non Uniform *)
      count_prods nuIndex_type
  in
  let trueIndCount := (* count of indices *)
      count_prods trueIndex_type
  in
  let ctorCount := #|trueParamCtors| in
  let predType :=
       replaceLastProd
         (
            (* add ∀ for instance *)
            (tProd (nNamed "inst")
                   (createAppChain (lift0 allIndCount ind_applied) allIndCount)
                 (* if prop => elim over prop *)
                 (* if type => elim over type *)
               (match returnType with None => getMaxElim one_body.(ind_kelim) | Some t => t end)
          )
         )
         (* quantify over indices but not over params *)
         nuIndex_type in
  (* quantify over all params *)
  it_mkLambda_or_LetIn trueParams
  (tLambda
     (* predicate *)
     (nNamed "p")
     (* the type of p is a transformation of the type
      todo: fold indices for type of p or use the type in index construction below
      for consistency*)
     predType
     (
       it_mkLambda_or_LetIn (rev (quantifyCases isInductive allParamCtors trueParamCount ind univ))
        (*
          theoretically recursive fix after cases
         *)
         (
              tFix
            [{|
             dname := nNamed "f"%string;
             dtype := (* could be omitted using type inference *)
               (* lift over cases for constructor and p *)
               replaceLastProd'
               (lift0 (S ctorCount) predType)
               (createAppChain (tRel (allIndCount + S ctorCount)) (S allIndCount))
              (* return p of instace *)
              (* p is after indices and cases *)
              ;
              dbody := (* take all indicies *)
              (* lift over cases for constructor and p and f? *)
                replaceLastLambda'
                  (mapProdToLambda (lift0 (2+ctorCount) predType))
                  (
                    (* match on instance *)
                    (* todo: handle non uniform matches *)
                    (* use change match return type, case application and access to non uniform *)
                        (tCase (ind, allParamCount)
                            (* return type of match *)
                            (
                              (lift0 (S trueIndCount)
                              (replaceLastLambda'
                                (mapProdToLambda
                              (lift (2+ctorCount) nonUniformArgCount
                                          (remove_arity nonUniformArgCount predType)
                                ))
                                (* apply p with indices and instace *)
                                (* p is after instance, indices, f, arguments (indices and instance) and cases *)
                                (* trueInd from above, nonUniformArgCount, f,  *)
                                (createAppChain (tRel (1+allIndCount+1+ctorCount) (* 1+trueIndCount *)
                                (* (createAppChain (tRel (1+trueIndCount+allIndCount+1+ctorCount) *)
                                                      (* (ctorCount+1+nonUniformArgCount+1+nonUniformArgCount) *)
                                                ) (S allIndCount))
                              ))
                            )
                           (* on instance *)
                            (tRel 0)
                            (* [(0,tRel 42)] *)
                            (* map case for each constructor *)

  (*  currently here   *)
                           (mapi
                              (fun i (x:(ident × term) × nat) =>
                                 let (y,count) := x in (* count for arguments of constructor *)
                                 let (_,a) := y in
                                 (count,
                                  (* constrMapping type allParamCount mapProdToLambda x (1+trueIndCount+2+ctorCount) *)
                                  replaceLastLambda'
                                  (
                                    (lift0 (S trueIndCount)
                                    (lift (2+ctorCount) nonUniformArgCount
                                      (subst1 type allParamCount (* tRel => inductive type *)
                                        (mapProdToLambda
                                          (remove_arity allParamCount a)
                                        )
                                      )
                                    )
                                    )
                                  )
                                  (* case for constructor is after f, indices, constructor arguments and other cases *)
                                  (* apply all arguments of constructor to case *)
                                  (
                                     let callChain :=
                                        (createAppChain (
                                             createAppChainOff
                                               (S trueIndCount+count)
                                               (tRel (1+allIndCount+count+(ctorCount -i)))
                                               nonUniformArgCount
                                        ) count) in
                                     if isInductive then
                                      mkApps callChain
                                              (getInductiveCalls x (2+ctorCount) (1+trueIndCount) trueParamCount nonUniformArgCount (count+1+allIndCount) count)
                                      else callChain
                                  )
                                 )
                              )
                              trueParamCtors
                           )
                        )
                )
             ;
             (* recursion over instance (last argument) *)
             rarg := allIndCount |}] 0)
    )) 
  , one_body.(ind_name) +s (if isInductive then "_ind_MC" else "_case_MC") ) end.

(* POLYMORPHIC *)
Definition runElim {A:Type} (indTm : A) (isInductive:bool) (create:bool) (nameOpt:option ident) (returnType:option term)
  : TemplateMonad unit
  := p <- tmQuoteRec indTm;;
     let (env,tm) := (p:program) in
     match tm with
     | tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
            let lemma := createElim isInductive ind0 univ decl returnType (fresh_name (empty_ext env) []) in
            evaluated <- tmEval lazy lemma;;
            if create then
              match evaluated with
                None => tmFail "invalid inductive"
              | Some (x,name') =>
                let name := match nameOpt with None => name' | Some s => s end
                in
                         y <- tmUnquote x;;
                         z <- tmEval lazy (y.(my_projT2));;
                        tmPrint y;;
                        tmPrint "";;
                        tmPrint z;;
                        tmDefinitionRed name (Some lazy) z;;(* simplified type *)
                        tmPrint "";;
                        tmPrint x
              end
            else
              match evaluated with
                None => tmPrint "failed"
                | Some (x,_) =>
                  tmPrint x;;
                  bruijn_print x
              end
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.

Definition create {A:Type} (tm:A) (isInductive:bool) (create:bool) :=
  runElim tm isInductive create None None.

Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x ;; match t with tLambda (nNamed na) _ _ => ret na | _ => ret "" end.

Notation name_of n := (ltac:(let k x := exact x in run_template_program (getName (fun n : nat => 0)) k)).

Notation "'Scheme' 'Elimination' 'for' T" := (runElim T false true None None)(at level 8).
Notation "'Scheme' 'Elimination' 'for' T 'Sort' 'Type'" := (runElim T false true None (Some <% Type %>))(at level 8).
Notation "'Scheme' n ':=' 'Elimination' 'for' T 'Sort' 'Type'" := (runElim T false true (Some (name_of n)) (Some <% Type %>))(at level 8).
Notation "'Scheme' n ':=' 'Elimination' 'for' T 'Sort' 'Type'" := (runElim T false true (Some "nat_caset2") (Some <% Type %>))(at level 8).
