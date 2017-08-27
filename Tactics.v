Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
    (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
  (forall (n : nat), evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4= true.
Proof.
  intros eq1 eq2.
  apply eq1.
  apply eq2.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | 0, _ => false
  | _, 0 => false
  | S n', S m' => beq_nat n' m'
  end.

Theorem silly3_firsttry : forall (n: nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n eq1.
  simpl.
  symmetry.
  apply eq1.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite <- rev_involutive.
  rewrite -> rev_involutive.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c e d f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o: X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2.
  apply eq1.
Qed.

Theorem S_injective : forall (n m :nat),
    S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] -> n = m.
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m o : nat),
    [n] = [m] -> n = m.
Proof.
  intros n m o H.
  inversion H as [Hnm].
  reflexivity.
Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq2.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
  intros n H.
  destruct n as [|n'].
  - reflexivity.
  - inversion H.
Qed.

Theorem inversion_ex4 : forall n,
    S n = 0 ->
    2 + 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
  intros n m H.
  inversion H.
Qed.

Example inversion_ex6 : forall (X:Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
  intros A B f x y H.
  rewrite -> H. reflexivity. Qed.

Theorem S_inj : forall (n m :nat) (b :bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H. apply H. Qed.

Theorem silly3' : forall (n: nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry.
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl.
    induction m as [|m' IHm'].
    + reflexivity.
    + intros H.
      rewrite <- plus_n_Sm in H.
      inversion H.
  - simpl.
    induction m as [|m' IHm'].
    + simpl. intros H. inversion H.
    + simpl. intros H. inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn' in H2.
      rewrite -> H2.
      reflexivity.
Qed.

Theorem double_injective' : forall n m,
    double n = double m -> n = m.
Proof.
  intros n.  induction n.
  - simpl. intros m H.
    destruct m.
    + reflexivity.
    + inversion H.
  - simpl.
    destruct m.
    + intros H. inversion H.
    + intros H.
      apply f_equal.
      apply IHn.
      simpl in H.
      inversion H.
      reflexivity.
Qed.

Theorem double_injective'' : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m H.
  rewrite -> double_plus in H.
  rewrite -> double_plus in H.
  apply plus_n_n_injective.
  apply H.
Qed.

Theorem double_injective_FAILED : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  induction n as [|n'].
  - simpl. intros H. destruct m as [|m'].
    + reflexivity.
    + inversion H.
  - simpl. intros H. destruct m as [|m'].
    + simpl in H. inversion H.
    + apply f_equal.
      rewrite -> double_plus in H.
      rewrite -> double_plus in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply plus_n_n_injective in H1.
      rewrite -> H1.
      reflexivity.
Qed.


Theorem beq_nat_true : forall n m,
    beq_nat n m = true ->
    n = m.
Proof.
  induction n as [|n' IHn'].
  - simpl. destruct m.
    + reflexivity.
    + intros H.
      inversion H.
  - simpl. destruct m.
    + intros H.
      inversion H.
    + intros H.
      apply f_equal.
      apply IHn'.
      apply H.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  - destruct n.
    + reflexivity.
    + simpl.
      intros H.
      inversion H.
  - destruct n.
    + simpl.
      intros H.
      inversion H.
    + simpl.
      intros H.
      apply f_equal.
      apply IHm'.
      inversion H.
      reflexivity.
Qed.

Theorem beq_id_true : forall x y,
    NatList.beq_id x y = true -> x = y.
Proof.
  intros [m] [n].
  simpl.
  intros H.
  assert(H' : m = n).
  {
    apply beq_nat_true.
    apply H.
  }
  rewrite H'.
  reflexivity.
Qed.

Theorem nth_error_after_last : forall (n:nat) (X:Type) (l:list X),
    length l = n ->
    nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|h l' IHl'].
  - intros n H.
    reflexivity.
  - intros n H.
    destruct n.
    + inversion H.
    + apply IHl'.
      inversion H.
      reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m,
    square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  {
    rewrite mult_comm. apply mult_assoc.
  }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition bar x :=
  match x with
  | 0 => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.

Fact silly_fact_2 : forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.

Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H.
Abort.  
