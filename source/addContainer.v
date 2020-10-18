(** adds a container to the registered database (using the unary parametricity translation) **)


Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.


Require Import List String.
Import ListNotations MonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.


Open Scope string_scope.

Require Import helperGen.
Require Import removeNonAug.

Definition nameAppend (n:name) (s:ident) :=
  match n with
    nAnon => nNamed s
  | nNamed s2 => nNamed (append s2 s)
  end.

(*
manage nested, guarded
A:T
P: A -> T
H: forall a:A, P a

P:A->T
P2: forall a:A, P a -> T
H: forall a:A, forall x:P a, P2 a x

All rT ...
isAll rT P
pAll rT P f

All nat (fun n => rT)
isAll nat TA (fun n => rT) (fun n => P)
pAll nat TA TP (fun n => rT) (fun n => P) (fun n => f)
P a is rT

use eta conversion
f = fun x:rT, f x

vec: T -> N -> T
vecAss: forall (X:T) (P:X->T) (n:nat), vec X n -> T
vecProof: forall (X:T) (P:X->T) (H:forall x^X, P x) (n:nat) (xs:vec X n), is_vec P n xs

assumption not needed
only application body
and isProof, args

appBody args -> T for assumption
and 
appBody args (with one argument missing) for proof

cases:
tProd => augment
tSort => body
_ => None

needed ideas:
what with nesting
list Type

applied: list A
only if container in Parameter

T1: X -> list X -> Type

usage:
rtB: T1 rT xs
isT1 rT P xs (isL rT P)

could be ignored


this function is very close to the one in destruct_lemma
*)

(* assumption also indicates if proof is generated *)
Fixpoint augmentType (ind:term) (assumption:option term) (args fullargs:list term) (t:term) : term := 
      let (_,concl) := decompose_prod t in
  match t with
  | tProd na t1 t2 =>
      let sortType :=
      match t1 with
        tSort _ => true
      | _ => false
      end in
      (* let newArgs := if sortType then (if assumption then 2 else 1) else 0 in *)
      let arguments :=
        vass na t1::
        if sortType then 
          vass (nameAppend na "P") (tProd nAnon (* P:X->Type *)
            (tRel 0)
            (* (trans <% Prop %>) *)
            (* (trans <% nat %>) *)
            t1
            (* concl2 *)
          )::
          (
            if assumption then
              [vass (nameAppend na "H")
              (tProd (nNamed "x") (* H:forall (x:X), P x *)
                (tRel 1)
                (tApp (tRel 1) (tRel 0))
              ) ]
            else
              []
          )
        else
          []
      in
      let newArgs := #|arguments| - 1 in
      it_mkProd_or_LetIn (rev arguments)
      (
          augmentType ind assumption 
          (map (lift0 (S newArgs)) args ++ [tRel newArgs]) (* X *)
          (map (lift0 (S newArgs)) fullargs ++ 
          [tRel newArgs] ++
          if Nat.eqb newArgs 0 then
            []
          else
            [tRel (newArgs-1)]
          )
          (* [tRel newArgs;tRel (newArgs-1)]) *) 
          (* X, P *) (* can be invalid if assumption=None *)
          t2
      )
  | _ => 
      tProd nAnon 
        (mkApps ind args)
        (
          match assumption with
            None =>  (* at conclusion *)
              (* (trans <% Prop %>) *)
              (* (trans <% nat %>) *)
              (* (trans <% Type %>) *)
              concl
          | Some ass => mkApps ass (map (lift0 1) fullargs ++ [tRel 0])
          (* | Some ass => mkApps ass (fullargs) *)
          end
        )
  end.



Unset Strict Unquote Universe Mode.

Print Ast.tInd.
Print inductive.
Print typed_term.

Print tmEval.

Search TemplateMonad kername.
Print tmLocate.
Print qualid.
(* Print tmAbout. *)
Definition tmAbout' (k:ident) : TemplateMonad (option global_reference) :=
  H <- tmLocate k;;
  match H with
  | x::_ => tmReturn (Some x)
  | _ => tmReturn None
  end.

Definition tmAbout (k:kername) : TemplateMonad (option global_reference) :=
  tmAbout' (snd k).

Definition getIndProp (kname:kername) (TL:tsl_table) :=
      H <- tmAbout kname;;
      (match H with
         Some((IndRef (mkInd kn n)) as R) => 
        match lookup_tsl_table TL R with
        | Some(Ast.tInd (mkInd kname idx) u) =>
            tmReturn (kname,idx,u)
            (* tmMsg ("New inductive: "++kname) *)
        | _ => tmFail "No inductive was not found in the translation" 
        end
      | _ => tmFail "The inductive was not found in the translation"
      end).

Print IndRef.
Print tmUnquote.
Print typed_term.

Require Import de_bruijn_print.

Definition addType {X} (t:X) :TemplateMonad unit :=
  tq <- tmQuote t;;
  match tq with
  | Ast.tInd ((mkInd kname idx) as ind) _ => 
      mind <- tmQuoteInductive (inductive_mind ind);;
      let name := 
        match nth_error (Ast.ind_bodies mind) (inductive_ind ind) with
        | None => "noName"
        | Some oind => Ast.ind_name oind
        end
      in

      inst <- tmInferInstance None (registered t);;
      match inst with
        my_Some _ => tmMsg "An instance was already found. The new instance will overwrite the old one."
      | _ => tmReturn tt
      end;;
      T <- tmQuote X;;

      TL <- TranslateRec emptyTC t;;

      newInd <- getIndProp kname TL.2;;

      let (newIndP1,u) := newInd : kername*nat*Instance.t in
      let (kname,idx) := newIndP1 in

      kname2' <- cleanInd kname idx u;;
      kname2 <- tmEval all (kname2');;
      H2 <- tmAbout' kname2;;
      newInd2 <- (match H2 with
        Some ((IndRef (mkInd kn n)) as R) => 
        tmReturn (kn,n)
      | _ => tmFail "no inductive after cleaning"
      end);;
      let (kname3,idx3) := newInd2 : kername * nat in
      let h := Ast.tInd (mkInd kname3 idx3) u in

      let assTt := augmentType (trans tq) None [] [] (trans T) in
      assT <- tmUnquoteTyped Type (PCUICToTemplate.trans assTt);; 
      assI <- tmUnquoteTyped (assT:Type) h;;
      (* tp <- tmUnquote h;; *)
      (* let (assT,assI) := tp : typed_term in *)
      (* print_nf assT';; *)
      (* print_nf assT;; *)
      (* print_nf assI;; *)

      (* let (assTE,assIE) := assI : typed_term in *)
      (* assIE <- tmEval all (assI.(my_projT2));; *)

      (* tmMsg "Please provide the assumption predicate.";; *)
      (* nameString <- tmEval lazy (append name "_assumption");; *)
      (* newName <- tmFreshName nameString;; (1* T_assumption *1) *)
      (* let assTt := augmentType (trans tq) None [] [] (trans T) in *)
      (* assT <- tmUnquoteTyped Type (PCUICToTemplate.trans assTt);; *)
      (* assI2 <- tmLemma newName (assT : Type);; *)

      tmMsg "Please provide a proof for the predicate.";;
      nameString2 <- tmEval lazy (append name "_proof");;
      newName2 <- tmFreshName nameString2;; (* T_proof *)
      (* h2 <- tmQuote assI2;; *)
      let proofTt := augmentType (trans tq) (Some (trans h)) [] [] (trans T) in
      (* print_nf h;; *)
      (* print_nf proofTt;; *)
      (* tmReturn tt *)
      tmMsg "T1";;
      proofT <- tmUnquoteTyped Type (PCUICToTemplate.trans proofTt);;
      print_nf proofT;;
      (* tmMsg "T1.5";; *)
      proofI <- tmLemma newName2 (proofT : Type);;
      (* proofI <- tmLemma newName2 False;; *)
      (* proofI <- tmLemma "H" nat;; *)
      (* proofI <- tmLemma "noName" (proofT : Type);; *)
      tmMsg "T2";;


      nameString3 <- tmEval lazy (append name "_inst");;
      newName3 <- tmFreshName nameString3;; (* T_inst *)
      tmDefinition newName3 (
        {|
            (* assumptionType := assTE; *)
            (* assumptionType := assT; *)
            assumption := @assI;
            proof := @proofI
        |} : registered t
      );;
      tmExistingInstance (VarRef newName3);;

      tmMsg (append (append "New instance " newName3) " was created")

      (* tmMsg "Fin" *)

  | _ => 
      @tmFail unit "inductive type is expected"
  end.

(*

      tmMsg "Fin"

  | _ => 
      @tmFail unit "inductive type is expected"
  end.














      kname2' <- cleanInd kname idx u;;
      kname2 <- tmEval all (kname2');;
      H2 <- tmAbout' kname2;;

      newInd2 <- (match H2 with
        Some ((IndRef (mkInd kn n)) as R) => 
        tmReturn (kn,n)
      | _ => tmFail "no inductive after cleaning"
      end);;


      let (kname3,idx3) := newInd2 : kername * nat in
      let h := Ast.tInd (mkInd kname3 idx3) u in

      let assTt := augmentType (trans tq) None [] [] (trans T) in
      print_nf assTt;;
      bruijn_print assTt;;
      print_nf h;;
      (* bruijn_print h;; *)

      (* assT <- tmUnquoteTyped Type (PCUICToTemplate.trans assTt);; *) 
      (* assI <- tmUnquoteTyped (assT:Type) h;; *)

      (* tmMsg "Please provide a proof for the predicate.";; *)
      (* nameString2 <- tmEval lazy (append name "_proof");; *)
      (* newName2 <- tmFreshName nameString2;; (1* T_proof *1) *)
      let proofTt := augmentType (trans tq) (Some (trans h)) [] [] (trans T) in
      (* proofT <- tmUnquoteTyped Type (PCUICToTemplate.trans proofTt);; *)
      (* print_nf proofT;; *)
      print_nf proofTt;;
      bruijn_print proofTt;;


      (* proofI <- tmLemma newName2 (proofT : Type);; *)

      (* nameString3 <- tmEval lazy (append name "_inst");; *)
      (* newName3 <- tmFreshName nameString3;; (1* T_inst *1) *)
      (* tmDefinition newName3 ( *)
      (*   {| *)
      (*       (1* assumptionType := assTE; *1) *)
      (*       (1* assumptionType := assT; *1) *)
      (*       assumption := @assI; *)
      (*       proof := @proofI *)
      (*   |} : registered t *)
      (* );; *)
      (* tmExistingInstance newName3;; *)

      (* tmMsg (append (append "New instance " newName3) " was created") *)

      tmMsg "Fin"
  | _ => 
      @tmFail unit "inductive type is expected"
  end.

*)