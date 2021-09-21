Import Init.Nat.
Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Nat.

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

Lemma add_assoc_l : forall n m, add n (S m) = S (add n m).
  induction n.
  simpl; reflexivity.
  induction m.
  simpl.
  apply IHn.
  simpl.
  rewrite <- IHn with (m := S (S m)).
  reflexivity.
Qed.

Lemma add_assoc_r : forall n m, add (S n) m = S (add n m).
  induction n.
  simpl; reflexivity.
  induction m; simpl; apply IHn.
Qed.

Lemma add_plus : forall n m, add n m = n + m.
  induction n.
  intros m.
  simpl.
  reflexivity.
  intros m.
  simpl.
  rewrite IHn.
  ring.
Qed.

Fixpoint sum_odd_n (n : nat) : nat :=
  match n with
    0 => 0
  | S p => 1 + 2 * p + sum_odd_n p 
  end.

Lemma sum_odd_n_lemma :  forall n : nat, sum_odd_n n = n * n.
  induction n; simpl. reflexivity.
  f_equal.
  replace (n + 0) with n.
  rewrite IHn.
  ring.
  ring.
Qed.

Definition is_zero (n : nat) : bool :=
    match n with
      0 => true
    | _ => false
    end.

Lemma not_is_zero_pred : 
    forall x, is_zero x = false -> S (Nat.pred x) = x.
  intros x.
  unfold is_zero, Nat.pred.
  case x.
  discriminate.
  reflexivity.
Qed.

(* Chap 6 *)

Require Import List.
Import ListNotations.

Fixpoint insert n l :=
  match l with
    [] => n::nil
  | a :: tl => if n <=? a
                then n :: l
                else a :: insert n tl
  end.

Fixpoint sort l :=
  match l with 
    [] => []
  | a :: tl => insert a (sort tl)
  end.

Fixpoint count n l :=
  match l with
    [] => 0
  | a :: tl => 
      let r := count n tl 
        in if n =? a then 1+r else r
  end.

Lemma insert_incr : forall n l, count n (insert n l) = 1 + count n l.
  intros n l ; induction l.
  { simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  }
  { simpl.
    case (n <=? a).
    { simpl. 
      rewrite Nat.eqb_refl.
      reflexivity.
    }
    { simpl.
      case (n =? a).
      - rewrite IHl; reflexivity.
      - rewrite IHl; reflexivity.
    }
  }
Qed.
          
