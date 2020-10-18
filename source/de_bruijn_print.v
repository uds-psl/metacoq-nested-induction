(*
Pretty print for terms with bruijn indices
(it might be easier to go the other way
and print coq terms with indices)

For a complete pretty print with names
unquote and use Coqs Print Command

It is useful as debugging if a term does not type
 *)

Require Import MetaCoq.Template.All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.


From MetaCoq.PCUIC Require Import TemplateToPCUIC.

Require Import List String.
Require Import Ascii.
Require Import Program Arith Lia PeanoNat.
Import ListNotations MonadNotation Nat.

Definition ascii_to_string (a:ascii) : string := String a (EmptyString).
Definition natToChar (n:nat) : ascii := ascii_of_nat(48+n).

Program Fixpoint natToString (n:nat) {measure n} : string :=
  match leb n 9 with
    true =>
    ascii_to_string (natToChar n)
  | false =>
    append (natToString (Nat.div n 10)) (ascii_to_string(natToChar(Nat.modulo n 10)))
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply leb_complete_conv in Heq_anonymous.
  pose proof (divmod_spec n 9 0 9).
  destruct divmod.
  destruct H;trivial.
  cbn. lia.
Qed.

Infix ":s" := String (at level 73).
Infix "+s" := append (at level 72).
Definition linebreak := ascii_to_string(ascii_of_nat 10).

Definition join (xs:list string) : string :=
  fold_left append xs EmptyString.

Require Import String.
Open Scope string_scope.

(* needed for mutual inductive types *)
Definition getInductiveName (ind:kername) (indIndex:nat) :TemplateMonad string :=
  ind <- tmQuoteInductive ind;;
  tmEval lazy match nth_error (trans_minductive_body ind).(ind_bodies) indIndex with
           | None => ""
           | Some b => b.(ind_name)
              end.

Definition getConstructName (ind:kername) (indIndex:nat) (consIndex:nat) :TemplateMonad string :=
  ind <- tmQuoteInductive ind;;
  tmEval lazy match nth_error (trans_minductive_body ind).(ind_bodies) indIndex with
           | None => ""
           | Some b => match nth_error b.(ind_ctors) consIndex with
                        None => ""
                      | Some (s,_,_) => s
                      end
           end.

Definition nameToString (s:name) : string :=
  match s with
    nAnon => "_"
  | nNamed s => s
  end.

Definition concatString (xs:list string) : string :=
  fold_left (fun a b => a +s b) xs "".

(* Print kername.
Print ident.
Print tmQuoteInductive. *)

Fixpoint bruijn_print_aux (t:term) : TemplateMonad string :=
  match t with
  | tRel n => tmReturn("R" :s (natToString n))
  | tVar ident => tmReturn(ident)
  | tEvar n xs => tmReturn "TODO:EVAR"
  | tSort univ => 
    tmReturn "tSort ?"
  | tProd n t t2 => match n with
                   | nAnon => s1 <- bruijn_print_aux t;;
                             s2 <- bruijn_print_aux t2;;
                             tmReturn("(":s append s1 (append ") -> " s2))
                   | nNamed s => s1 <- bruijn_print_aux t;;
                                s2 <- bruijn_print_aux t2;;
                                tmReturn("∀ (" +s s +s (" : "+s s1) +s "), " +s s2)
                   end
  | tLambda s t t2 => s1 <- bruijn_print_aux t;;
                    s2 <- bruijn_print_aux t2;;
                    tmReturn("λ ("+s match s with
                        nAnon => "_"
                      | nNamed s => s
                      end
                     +s " : "+s s1+s"). "+s s2)
  | tLetIn name t1 t2 t3 =>
    s1 <- bruijn_print_aux t1;;
    s2 <- bruijn_print_aux t2;;
    s3 <- bruijn_print_aux t3;;
    tmReturn("let "+s (nameToString name) +s " := "+s s1 +s " : " +s s2 +s " in "+s linebreak +s s3)
  | tApp t1 t2 =>
    s1 <- bruijn_print_aux t1;;
    s2 <- bruijn_print_aux t2;;
    tmReturn("(" +s s1 +s " " +s s2 +s ")")
  | tConst kn ui => let (_,name) := kn in tmReturn name
  | tInd ind ui => getInductiveName ind.(inductive_mind) ind.(inductive_ind)
  | tConstruct ind n ui => getConstructName ind.(inductive_mind) ind.(inductive_ind) n
  | tCase (ind,n) p c brs =>
    sc <- bruijn_print_aux c;;
    sp <- bruijn_print_aux p;;
    sb <- fold_left (fun sa x => match x with (n,t) => st <- bruijn_print_aux t;;sb <- sa;;tmReturn (sb +s " | ("+s(natToString n)+s") " +s st +s linebreak) end) brs (tmReturn "");;
    tmReturn(linebreak +s "match (P:" +s (natToString n) +s ") "+s sc +s " return " +s sp +s " with" +s linebreak +s
            sb +s
             "end")
  | tProj p t => tmReturn "TODO:Proj"
  | tFix mf n =>
    (fix f xs := match xs with
                  nil => tmReturn ""
                | mfb::xs =>
                  sr <- f xs;;
          stype <- bruijn_print_aux (mfb.(dtype));;
          sbody <- bruijn_print_aux (mfb.(dbody));;
          tmReturn (linebreak +s "(fix "+s (nameToString mfb.(dname)) +s " : " +s stype +s " := " +s linebreak +s sbody +s ") "+s sr)
                end
    ) mf
  | _ => tmReturn "TODO"
  end.




Definition bruijn_print (t:term) : TemplateMonad unit :=
  s <- bruijn_print_aux t;;
  val <- tmEval lazy s;;
  tmMsg val.



MetaCoq Quote Definition printTest := 
  (forall (P:nat->Prop) (H0:P 0) (HS: forall n, P n -> P (S n)) (n:nat), P n).

(* MetaCoq Run (bruijn_print (trans printTest)). *)
