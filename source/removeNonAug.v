(** Post-processing of unary parametricity translation to remove unneeded arguments **)


From MetaCoq Require Import Template.All.
Require Import List String.
Import ListNotations MonadNotation.
Require Import MetaCoq.Template.Pretty.


From MetaCoq.Checker Require Import All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Translations Require Import param_original.




Fixpoint isAugmentable (isMain:bool) (t:term) : bool := 
  match t with
  | tSort _ => negb isMain
  | tProd _ t1 t2 => 
      orb 
      (isAugmentable false t1)
      (isAugmentable isMain t2)
  | _ => false
  end.

Print tmQuoteInductive.

Fixpoint nonAugInd (t:term) : TemplateMonad bool :=
  match t with
  | tInd (mkInd kname idx) u =>
    mind <- tmQuoteInductive kname;;
    match nth_error (mind.(ind_bodies)) idx with
      None => tmReturn true
    | Some oind => tmReturn (negb (isAugmentable true oind.(ind_type)))
    end
  | tApp t1 _ => nonAugInd t1
  | tProd _ t1 t2 =>
      b1 <- nonAugInd t1;;
      b2 <- nonAugInd t2;;
      tmReturn (orb b1 b2)
  | _ => tmReturn false
  end.

Definition deLift01 := subst [tRel 0] 0.

Fixpoint removeNonAugList (xs:list context_decl) :=
  match xs with
  | t1::t2::xr =>
    b <- nonAugInd t1.(decl_type);;
    tl <- removeNonAugList xr;;
    tmReturn(
      if b : bool then 
        t1::tl
      else
        t1::t2::tl
    )
  | _ => tmReturn xs
  end.


Fixpoint removeNonAugmentable (t:term) (c:nat)
  :=
match t with
| tProd na t1 (tProd na2 t2 t3) => 
    rt3p <- removeNonAugmentable t3 (S (S c));;
    let (rt3,xs) := rt3p : term * list nat in
    b <- nonAugInd t1;;
    tmReturn(
      if b:bool then
        (tProd na t1 (deLift01 rt3), S c::xs) (* lift -1 *)
      else
        (tProd na t1 (tProd na2 t2 rt3), xs)
    )
| _ => tmReturn (t,[])
end.

Fixpoint removeElements (xs:list term) (ys:list nat) (n:nat) :=
  match ys,xs with
  | y::yr,t::tr => 
      if Nat.eqb y n then 
        removeElements tr yr (S n)
      else
        t::removeElements tr (y::yr) (S n)
  | _,_ => xs
  end.

(* & tRel0 calls in arguments are missing *)
(* is not working properly *)
Fixpoint removeArgList (t:term) (xs:list nat) (rec:nat) :=
  match t with
  | tProd na t1 t2 =>
      tProd na (removeArgList t1 xs rec) (removeArgList t2 xs (S rec))
  | tApp (tRel n) tl => 
      if Nat.eqb n rec then
        mkApps (tRel n) (removeElements tl xs 0)
      else 
        t
  | _ => t
  end.

Print one_inductive_body.
Check Build_one_inductive_body.

Print monad_map.

Definition cleanOInd (ind:one_inductive_body) :=
  xp <- removeNonAugmentable ind.(ind_type) 0;;
  let (t,xs) := xp : term * list nat in
  (* tmPrint xs;; *)
  ctors <- monad_map 
    (fun '(na,t,n) => 
      tp <- removeNonAugmentable t 0;;
      newName <- tmFreshName na;;
let rmt := removeArgList tp.1 xs 0 in
      tmReturn (newName,rmt,n)
    )
    ind.(ind_ctors);;
    (* tmMsg "A". *)
  oldName <- tmEval all ind.(ind_name);;
  newName <- tmFreshName oldName;;
  tmReturn(
    Build_one_inductive_body 
      newName
      t
      ind.(ind_kelim)
      (* ind.(ind_ctors) *)
      ctors
      ind.(ind_projs)
  ).

Definition cleanInd (kname:kername) (idx:nat) (u:Instance.t) :=
    mind <- tmQuoteInductive kname;;
    nparam <- (removeNonAugList (rev mind.(ind_params)));;
    noinds <- monad_map cleanOInd mind.(ind_bodies);;
    (* tmMsg "Fin" *)
    tmMkInductive (mind_body_to_entry {|
      ind_finite := mind.(ind_finite);
      ind_npars := #|nparam|;
      ind_params := rev nparam;
      ind_bodies := noinds;
      ind_universes := mind.(ind_universes);
      ind_variance := mind.(ind_variance)
    |});;
    match nth_error noinds idx with
      None => tmFail "no inductive was constructed"
    | Some oind => tmReturn oind.(ind_name)
    end.

Definition cleanIndTop {T} (t:T) :=
  tq <- tmQuote t;;
  match tq with
  | tInd (mkInd kname idx) u => 
      cleanInd kname idx u
  | _ => tmFail "inductive expected"
  end.

(* TODO get name/ind somehow *)

