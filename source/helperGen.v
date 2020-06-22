
(** Find container and build the nesting function **)

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

Require Import Modes.

Open Scope string_scope.

Definition nestedMode := "Nested_Inductives".



Class registered {X} (ty:X) :=
{
  assumptionType: Type;
  assumption: assumptionType;
  proofType: Type;
  proof: proofType
}.

Check registered.


Fixpoint isAugmentable (isMain:bool) (t:term) : bool := 
  match t with
  | tSort _ => negb isMain
  | tProd _ t1 t2 => 
      orb 
      (isAugmentable false t1)
      (isAugmentable isMain t2)
  | _ => false
  end.

Open Scope string_scope.

Definition errorMessage (name:string) : TemplateMonad unit :=
  (* tmPrint tE;; *)
  tmMsg (name ++ " is not a registered container and won't generate nested inductive hypothesis.");;
  tmMsg ("Use `MetaCoq Run Derive Container for " ++ name ++ "` to register " ++ name ++ " as container.").
  (* tmMsg "was not found in the registered database and thus will be ignored.";; *)


Definition createFunction (inds:list (kername * option nat * Instance.t)) : TemplateMonad( kername -> nat -> option (term×term) ) :=
  monad_fold_left
  (fun acc '(kname,no,u) =>
    let object :=
      match no with
        None => Ast.tConst kname u
      | Some n => Ast.tInd (mkInd kname n) u
      end
    in
    tt <- tmUnquote object;;
    let t := tt.(my_projT2) in
    inst <- tmInferInstance None (registered t);;
    tE <- tmEval lazy t;;
    match inst with
    | my_None => 
        match no with
          None => (* TODO check augmentable constant *)
            errorMessage kname;;
            tmReturn acc
        | Some n =>
          mind <- tmQuoteInductive kname;;
          match nth_error (Ast.ind_bodies mind) n with
          | Some oind => 
              match isAugmentable true (trans (Ast.ind_type oind)) with
              | true => 
                  errorMessage (Ast.ind_name oind);;
                  tmReturn acc
              | false => 
                  (* tmMsg "not found and not augmentable";; *)
                  tmReturn acc
              end
          | None => tmReturn acc
          end
        end
    | my_Some a => 
        (* tmMsg "was found in the registered database.";; *)
        assumI <- tmQuote (@assumption _ _ a);;
        proofI <- tmQuote (@proof _ _ a);;
        assumE <- tmEval lazy assumI;;
        proofE <- tmEval lazy proofI;;
        tmReturn
          (fun name i => 
            if name =? kname then (* TODO use i and no for mutual *)
              Some (
                TemplateToPCUIC.trans assumE,
                TemplateToPCUIC.trans proofE
              )
            else
              acc name i
          )
    end
  )
  inds
  (fun _ _ => None).


Fixpoint findRec (k:nat) (u:term) :=
  match u with
  | tRel n => Nat.eqb n k
  | tProd na A B => orb (findRec k A) (findRec (S k) B)
  | tLambda na T M => orb (findRec k T) (findRec (S k) M)
  | tLetIn na b ty b' => orb (orb (findRec k b) (findRec k ty)) (findRec (S k) b')
  | tApp t1 t2 =>
    orb (findRec k t1) (findRec k t2)
  | _ => false
  end.


Fixpoint findRecInd (rec:nat) (forceAdd:bool) (t:term) : list (kername * option nat * Instance.t) :=
  match t with
  | tProd _ t1 t2 => findRecInd rec false t1 ++
      findRecInd (S rec) forceAdd t2
  | tLambda _ t1 t2 => findRecInd rec false t1 ++
      findRecInd (S rec) forceAdd t2
  | tLetIn _ t1 t2 t3 => findRecInd rec false t1 ++
      findRecInd rec false t2 ++
      findRecInd (S rec) forceAdd t3
  | tApp t1 t2 =>
      findRecInd rec (orb forceAdd (findRec rec t2)) t1 ++
      findRecInd rec forceAdd t2
  | tInd (mkInd kname n) u => 
      if forceAdd then
        [(kname, Some n, u)]
      else
        []
  | tConst kname u => 
      if forceAdd then
        [(kname, None, u)]
      else
        []
  | _ => []
  end.


Definition getInd (oind:one_inductive_body) : list (kername * option nat * Instance.t) :=
  List.concat (map (fun '(n,t,i) => findRecInd 0 false t) oind.(ind_ctors)).

Definition getInds (oind:one_inductive_body) : TemplateMonad (list (kername * option nat * Instance.t)) :=
        monad_fold_left 
        (fun acc '(n,t,i) =>
          et <- tmEval all t;;
          let inds := findRecInd 0 false et in
          tmReturn (app acc inds)
        )
        oind.(ind_ctors)
        [].

Definition extractFunction (mind:mutual_inductive_body) (n:nat) : TemplateMonad( kername -> nat -> option (term×term) )  :=
  isNested <- getMode nestedMode;;
  if isNested:bool then
    match nth_error mind.(ind_bodies) n with
      None => tmFail "mutual inductive body was not found"
    | Some oind => 
        inds <- getInds oind;;
        createFunction inds
    end
  else
    tmMsg "Nested recursion will be ignored.";;
    tmReturn (
      fun _ _ => None
    ).


