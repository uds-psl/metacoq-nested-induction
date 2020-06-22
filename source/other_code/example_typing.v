Abort All.
Load typing.


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
