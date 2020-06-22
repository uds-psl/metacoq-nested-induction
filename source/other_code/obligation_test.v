(* Ltac induction := idtac "HI". *)

Ltac ind_on_last :=
  lazymatch goal with
  | |- forall x y, ?H => intros ?;ind_on_last
  | |- forall y, ?H => 
      let inst := fresh "x" in
      intros inst;induction inst (* using database *)
  | _ => fail "not applicable"
  end.

Obligation Tactic := cbn;ind_on_last;auto.
Goal forall (y:nat) (x:nat), x=0.
ind_on_last.
Admitted.

Goal forall (x:nat), x=0.
Proof.
  intros x;induction x.
  Restart.
  induction x.
  Restart.
  match goal with
  |- forall y, ?H => induction y
  end.
  Restart.
