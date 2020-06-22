
(** Skeleton to derive show instances for inductive types (unfinished) **)

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

Require Import MetaCoq.Induction.non_uniform.
Require Import MetaCoq.Induction.de_bruijn_print.

Require Import Even.
Require Import Recdef.

Require Import String.
Open Scope string_scope.

About term.
Print term.

Definition trans := TemplateToPCUIC.trans.
Definition stringQ : term := (TemplateToPCUIC.trans <% string %>).
Definition lift01 := lift0 1.
Definition pretty := print_term (empty_ext []) [] true true.

Fixpoint deriveShowType (t:term) (app:term) (args:list term) : option term :=
match t with
| tProd na t1 t2 => 
    match deriveShowType t1 (tRel 0) [] with
      None => 
        t2r <- deriveShowType t2 app (map (lift0 1) args++[tRel 0]);;
        Some(tProd na t1 t2r)
    | Some t1r =>
        t2r <- deriveShowType t2 app (map (lift0 1) args++[tRel 0]);;
        Some (tProd na t1 
              (tProd na t1r
                (lift0 1 t2r)))
    end
| tSort _ => 
    Some (
      tProd (nNamed "x")
      (mkApps app args)
      stringQ
    )
| _ => None
end.

Fixpoint extendList (xs:context) : context * (nat -> term -> term) :=
  match xs with
    [] => ([],fun _ t => t)
  | t::tr => 
      let (ys,f) := extendList tr in
      let lf := fun n => f (S n) in
      match deriveShowType (decl_type t) (tRel 0) [] with
        None => (t::ys,lf)
      | Some y => (t::vass (decl_name t) y::map_context (lift0 1) ys, fun n t => lift 1 n (lf n t))
      end
  end.

(*Test*)
Definition xs1 := [vass nAnon (trans <% nat %>)].
Definition xs2 := [vass nAnon (trans <% Prop %>)].
Definition xs3 := [
  vass (nNamed "A") (trans <% Type %>);
  vass (nNamed "n") (trans <% nat %>);
  vass (nNamed "B") (trans <% Type %>)
  ].
Definition xs4 := [vass nAnon (trans <% Type %>);vass nAnon (tRel 0)].

Compute (
let (xs,f) := extendList 
  xs4
in
(xs,
f 0 (tRel 0),
f 0 (tRel 1),
f 0 (tRel 2),
f 0 (tRel 3)
)
).


(*Test*)
Compute (option_map pretty (deriveShowType (trans <% Type %>) (trans <% nat %>) [])).
Compute (option_map pretty (deriveShowType (trans <% Type -> Type %>) (trans <% list %>) [])).
Compute (option_map pretty (deriveShowType (trans <% forall (A:Type), A -> Type %>) (trans <% nat %>) [])).

Print tFix.
Print tCase.

MetaCoq Run (tmQuoteInductive "Acc" >>= tmPrint).





Require Import MetaCoq.Induction.destruct_lemma.

(* mind oind inductive universes *)

(* Test *)
Print replaceLastProd.
Print reln.
Print to_extended_list_k.
Compute (reln [] 5 []).
Print to_extended_list.
Compute (to_extended_list [vass nAnon (tRel 9);vass nAnon (tRel 9);vass nAnon (tRel 9)]).


Open Scope list_scope.

Print mutual_inductive_body.
Print one_inductive_body.
Print collect_prods.

(* map_context (f 0) *)
Fixpoint map_context_lifting (f:nat->term->term) (n:nat) (xs:context) :=
  match xs with
    [] => []
  | x::xr => map_decl (f n) x::map_context_lifting f (S n) xr
  end.

Compute (lift_context 1 0 [vass nAnon (tRel 0);vass nAnon (tRel 0)]).

(* Lemma lift_fun a b xs: lift_context a b (rev xs) = rev (map_context_lifting (lift a) b xs). *)
(* Proof. *)
(*   unfold lift_context,fold_context,mapi. *)
(*   remember 0 as n. *)
(*   clear Heqn. *)
(*   induction xs in n |- *;trivial. *)
(*   cbn. *)
(*   - rewrite rev_unit;cbn. *)

Compute (<% append %>).
Check getInner.

(* use print function *)
(* Fixpoint printCtor (t:term) (recpos:nat) (fpos:nat) (str:term) (nestedFun:term->string) :=
  match t with
  | tProd na t1 t2 => 
      let s1 := printTerm t1 recpos fpos nestedFun (tRel 0) in
      tLambda na t1 (printCtor t2 (S recpos) (S fpos) (tApp (tApp <% @append %> str) s1))
  | tApp t1 t2 => 
      let (_,xs) := getInner t [] in
      let ys := skipn (* params *)
  | _ => str
  end. *)

Definition createFunction (mind:mutual_inductive_body) (oind:one_inductive_body) (induct:inductive) (u:Instance.t) :=
  let kname := induct.(inductive_mind) in
  let idx := induct.(inductive_ind) in

  let ind := tInd induct u in
  let ctors := oind.(ind_ctors) in

  let allParamCount := mind.(ind_npars) in
  let trueParamCount := getParamCount oind allParamCount in
  let nonUniformArgCount := allParamCount - trueParamCount in

  let allParams := rev mind.(ind_params) in
  let trueParams := firstn trueParamCount allParams in
  let nonUniform := skipn trueParamCount allParams in

  let indices := skipn allParamCount (collect_prods oind.(ind_type)) in

  let (trueParamsExtended,trueParamsExtFun) := extendList trueParams in
  let trueParamsExtCount := #|trueParamsExtended| in

  let (nonUniformExtended,nonUniformExtFun) := extendList nonUniform in
  let nonUniformExtCount := #|nonUniformExtended| in

  let (indicesExtended,indicesExtFun) := extendList indices in
  let indicesExtCount := #|indicesExtended| in

  let instance := mkApps ind (to_extended_list (trueParams++nonUniform++indices)) in
  let instAss := vass (nNamed "inst") instance in
  let args :=
    map_context_lifting trueParamsExtFun 0 (nonUniformExtended ++ 
    map_context_lifting nonUniformExtFun 0 (indicesExtended ++ 
    [
    map_decl (indicesExtFun 0) instAss
    ]))
  in

  (* (allParams,trueParams,nonUniform). *)


  it_mkLambda_or_LetIn (rev trueParamsExtended)
  (
  tFix 
  [{|
      dname := nNamed "f";
      dtype :=
      it_mkProd_or_LetIn (rev args)
      stringQ
      ;
      dbody :=
      (* it_mkLambda_or_LetIn (rev (map_context (lift 1 (nonUniformExtCount+indicesExtCount)) args)) *)
      it_mkLambda_or_LetIn ((lift_context 1 0 (rev args)))
      (
      (* (trans <% "" %>) *)
      tCase
      (induct, #|allParams|)
      (* (it_mkLambda_or_LetIn (lift_context (1+nonUniformExtCount+indicesExtCount) 0 (rev(map_context_lifting trueParamsExtFun 0 (nonUniform++indices++[instAss])))) stringQ) *)
      (it_mkLambda_or_LetIn
        (rev
        (* lifte über instance *)
        (* lifte über indicesExt *)
        (* lifte über f *)
        (* nutze paramExt *)
        (* nutze nonUniformExt *)
        (map_context_lifting (lift 1) 0
        (map_context_lifting (lift indicesExtCount) 0
        (map_context_lifting (lift 1) (nonUniformExtCount)
        (map_context_lifting (trueParamsExtFun) (nonUniformExtCount)
        (map_context_lifting nonUniformExtFun 0
        (indices++[instAss])
        ))))))
        stringQ
      )
      (tRel 0)
      (
      mapi
        (fun i (x:(ident × term) × nat) =>
           let (y,count) := x in (* count for arguments of constructor *)
           let (_,a) := y in
           (count,
                     let fpos := 1+nonUniformExtCount+indicesExtCount in
                     let paramOffset := 1+fpos in
                     let recPos := paramOffset + trueParamsExtCount in
                     let ctorType :=
                       (
        (lift 1 0
        (lift indicesExtCount 0
        (lift 1 (nonUniformExtCount)
        (trueParamsExtFun (nonUniformExtCount)
        (nonUniformExtFun 0
                          (remove_arity (allParamCount) a)
                       )))))
                       )
                                  (* ( (lift0 (S #|indicesExtended|) *)
                                  (*   (lift 1 #|nonUniform| *)
                                  (*         (remove_arity #|allParams| a) *)
                                  (*   ))) *)
                         in
                       mapProdToLambda
                       (* ((replaceLastProd (tRel recPos) ctorType)) *)
                       (subst1 ind recPos (replaceLastProd (trans <% "" %>) ctorType))
                       (* and prod -> lambda *)
           )
        )
      ctors
      )
      )
      ;
      rarg :=  #|nonUniformExtended| + #|indicesExtended|
  |}] 0
  ).

Print tmMkDefinition.
Definition showFunction {T} (ind:T) : TemplateMonad unit :=
  qind <- tmQuote ind;;
  match qind with
  | Ast.tInd ((mkInd kname idx) as induct) u =>
      mind <- tmQuoteInductive kname;;
      match nth_error (Ast.ind_bodies mind) idx with
        None => tmFail "inductive body not found"
      | Some oind =>
          let result := 
            createFunction 
              (TemplateToPCUIC.trans_minductive_body mind) 
              (TemplateToPCUIC.trans_one_ind_body oind) 
              induct 
              u 
          in
          tmMsg (pretty result);;
          bruijn_print result;;
          r <- tmEval all (PCUICToTemplate.trans result);;
          name1 <- tmEval all (append (Ast.ind_name oind) "_show");;
          name <- tmFreshName name1;;
          tmMsg ""
          (* tmMkDefinition name r *)
          (* print_nf result *)
      end
  | _ => tmFail "Inductive expected"
  end.


  MetaCoq Run (showFunction nat).
  (* Print nat_show. *)
  MetaCoq Run (showFunction list).
  (* Print list_show. *)
  (* MetaCoq Run (tmQuoteInductive "le" >>= print_nf). *)
  (* MetaCoq Run (showFunction le). *)
  (* Print le_show. *)
  (* MetaCoq Run (tmQuoteInductive "VectorDef.t" >>= print_nf). *)
  (* MetaCoq Run (showFunction VectorDef.t). *)
  MetaCoq Run (showFunction Acc).



Definition createShow (isInductive:bool) (ind:inductive) (univ:Instance.t) (ind_body:mutual_inductive_body) (returnType:option term) (nameFun:name->term->name) (nested: kername -> nat -> option (term×term)) :=
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
  (     (
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
               predType
               stringQ
              (* return p of instace *)
              (* p is after indices and cases *)
              ;
              dbody := (* take all indicies *)
              (* lift over cases for constructor and p and f? *)
                replaceLastLambda'
                  (mapProdToLambda (lift0 1 predType))
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
                              (lift 1 nonUniformArgCount
                                          (remove_arity nonUniformArgCount predType)
                                ))
                                stringQ
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


                     let fpos := 1+allIndCount in
                     let Hstart := fpos in
                     (* let Hpos := Hstart+(ctorCount -i) in *)

                     (* let ppos := 1+Hstart in *)
                     let paramOffset := 1+Hstart in
                     let recPos := paramOffset + trueParamCount in

                     let ctorType :=
                                  (
                                    (lift0 (S trueIndCount)
                                    (lift 1 nonUniformArgCount
                                        (* (mapProdToLambda *)
                                          (remove_arity allParamCount a)
                                        (* ) *)
                                    )
                                    )
                                  )
                         in

                     (* tApp (tRel 420) [tRel fpos;tRel Hpos;tRel ppos;tRel paramOffset;tRel recPos] *)
                     (* ctorType *)

                     (* match *)
                     (*   generateInductiveAssumptions trueParamCount nested isInductive recPos ppos fpos (tRel Hpos) (map (lift0 (1+trueIndCount)) (mkRelNum nonUniformArgCount)) false true true false ctorType *)
                     (* with *)
                     (*   None => tVar "this can't happen (proof)" *)
                     (* | Some t => *)
                       subst1 type recPos (ctorType)
                     (* end *)
                                 )
                              )
                              trueParamCtors
                           )
                        )
                )
             ;
             (* recursion over instance (last argument) *)
             rarg := allIndCount |}] 0)
    )) ) end.

Require Import MetaCoq.Induction.helperGen.


Definition runShow {A:Type} (indTm : A) (isInductive:bool) (create:bool) (nameOpt:option ident) (returnType:option Ast.term)
  : TemplateMonad unit
  := p <- tmQuoteRec indTm;;
     let (env,tm) := (p:Ast.program) in
     match tm with
     | Ast.tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       nestedFunc <- extractFunction (TemplateToPCUIC.trans_minductive_body decl) (inductive_ind ind0);;
            let namingFun : name -> term -> name :=
                fresh_name
                  (empty_ext
                     (TemplateToPCUIC.trans_global_decls env)
                  )
                  []
            in
            let lemma : option (term) := createShow isInductive ind0 univ (TemplateToPCUIC.trans_minductive_body decl) (option_map trans returnType) namingFun nestedFunc in
            evaluated <- tmEval lazy lemma;;
            if create then
            let name' := "Show" in
              match evaluated with
                None => tmFail "invalid inductive"
              | Some (x) =>
                let name := match nameOpt with None => name' | Some s => s end
                in
                        tmMsg ("created " +s name);;
                         y <- tmUnquote (PCUICToTemplate.trans x);;
                         z <- tmEval lazy (y.(my_projT2));;
                        oldName <- tmEval all name;;
                        newName <- tmFreshName oldName;;
                        tmDefinitionRed newName (Some lazy) z;;(* simplified type *)
                        tmReturn tt
              end
            else
              match evaluated with
                None => tmPrint "failed"
                | Some (x) =>
                  tmPrint x;;
                  bruijn_print x;;
                  tmMsg "";;
                  tmMsg (print_term (empty_ext (TemplateToPCUIC.trans_global_decls env)) [] true false x)
              end
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.

Definition createShowFunc {A:Type} (tm:A) (isInductive:bool) (create:bool) :=
  runShow tm isInductive create None None.

MetaCoq Run (createShowFunc list true false).


