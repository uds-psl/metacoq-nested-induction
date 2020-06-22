Require Import String.
Require Import List.
Import ListNotations.

Class registered {X} (ty:X) :=
(* {assumptionType proofType} := *)
{
  assumptionType: Type;
  assumption: assumptionType;
  proofType: Type;
  proof: proofType
}.


Definition listAssumption {X} (P:X->Prop) (xs:list X) := forall t, In t xs -> P t.

Definition listProof {X} (P:X->Prop) (f:forall x, P x) (xs:list X) : listAssumption P xs :=
(list_ind (fun xs0 : list X => listAssumption P xs0)
            (fun (t : X) (H0 : In t []) => match H0 return (P t) with
                                                  end)
            (fun (a : X) (xs0 : list X) (IHxs : listAssumption P xs0)
               (t : X) (H0 : In t (a :: xs0)) =>
             match H0 with
             | or_introl H1 => Coq.Init.Logic.eq_ind a (fun t0 : X => P t0) (f a) t H1
             | or_intror H1 => IHxs t H1
             end) xs).

Instance test : registered list := 
{|
    assumption := @listAssumption;
    proof := @listProof
|}.

Goal registered list.
Proof.
  refine (_).
Qed.



