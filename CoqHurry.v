Require Import Arith.
Require Import Omega.
Require Import List.

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
  induction n.
  reflexivity.
  assert (SnSn : S n * S n = n * n + 2 * n + 1).
  ring.
  rewrite SnSn.
  rewrite <- IHn.
  simpl.
  ring.
Qed.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Lemma evenb_p : forall n, evenb n = true ->
      exists x, n = 2 * x.
  assert (Main :  
    forall n,
    (evenb n = true -> exists x, n = 2 * x) /\
    (evenb (S n) = true -> exists x, S n = 2 * x)).
  induction n.
  split. exists 0. ring.
  simpl; intros H; discriminate H.
  split.
    destruct IHn as [_ IHn']; exact IHn'.
  simpl evenb; intros H; destruct IHn as [IHn' _].
  assert (H' : exists x, n = 2 * x).
    apply IHn'; exact H.
  destruct H' as [x q]; exists (x + 1); rewrite q; ring.
  intros n ev.
  destruct (Main n) as [H _].  apply H. exact ev.
Qed.

(*

Exercise on addition, alternative definition We can define a new
addition function on natural numbers:

Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.

Prove the following statements.
forall n m, add n (S m) = S (add n m)
forall n m, add (S n) m = S (add n m)
forall n m, add n m = n + m

Remember that you may use a lemma you just proved when proving a new exercise

*)

Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.

Lemma add_assoc : forall n m, add n (S m) = S (add n m).
  induction n.
  simpl; reflexivity.
  induction m.
  simpl.
  apply IHn.
  simpl.
  rewrite <- IHn with (m := S (S m)).
  reflexivity.
Qed.
