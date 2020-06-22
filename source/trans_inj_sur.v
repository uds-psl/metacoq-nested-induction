
(** This proof shows that PCUICToTemplate is injective
    and TemplateToPCUIC is surjective
**)


From Coq Require Import Bool String List Program BinPos Compare_dec ZArith.

From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.

From MetaCoq.PCUIC Require Import 
  PCUICToTemplate
  TemplateToPCUIC.
From MetaCoq.PCUIC Require Import 
  (* PCUICToTemplateCorrectness. *)
  TemplateToPCUICCorrectness.

Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.


Lemma inj_sur (t:PCUICAst.term):
  TemplateToPCUIC.trans (PCUICToTemplate.trans t) = t.
Proof.
  induction t using PCUICInduction.term_forall_list_ind;cbn;try congruence.
  - f_equal.
    induction X;cbn;trivial.
    now rewrite IHX.
  - now rewrite trans_mkApp,IHt1,IHt2.
  - rewrite IHt1, IHt2.
    f_equal.
    induction X;cbn;trivial.
    rewrite IHX.
    destruct x; unfold on_snd; cbn in *; now rewrite p0.
  - f_equal.
    induction X;cbn;trivial.
    rewrite IHX.
    destruct x;
    unfold map_def;
    cbn in *.
    destruct p.
    now do 2 f_equal.
  - f_equal.
    induction X;cbn;trivial.
    rewrite IHX.
    destruct x;
    unfold map_def;
    cbn in *.
    destruct p.
    now do 2 f_equal.
Qed.

