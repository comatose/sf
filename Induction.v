Theorem plus_n_O : forall n : nat,
    n = n + 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n : nat,
    minus n n = 0.
Proof.
  induction n as [].
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
    n * 0 = 0.
Proof.
  induction n as [].
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn.
    induction m as [].
    + simpl. reflexivity.
    + simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn.
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (evenb n')
  end.

Theorem evenb_s : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  induction n as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m: nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  {
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). {
    rewrite -> plus_comm. reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
  intros n m p.
  rewrite <- plus_comm.
  assert (H: p + n = n + p). {
    rewrite <- plus_comm. reflexivity.
  }
  rewrite <- H.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_1_n : forall n : nat,
    n * 1 = n.
Proof.
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn.
    reflexivity.
Qed.

Lemma mult_plus : forall n m : nat,
    n + n * m = n * S m.
Proof.
  intros n m.
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite -> plus_swap. rewrite -> IHn. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
    m * n = n * m.
  intros m n.
  induction m as [].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - induction n as [].
    + simpl. rewrite -> mult_0_r.
      reflexivity.
    + simpl. rewrite -> IHm.
      simpl. rewrite -> plus_swap.
      rewrite -> mult_plus.
      reflexivity.
Qed.

Inductive bin : Type :=
| O
| I
| T : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
  | O => I
  | I => T O
  | T n' => T (incr n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | O => 0
  | I => 1
  | T n' => 2 + (bin_to_nat n')
  end.

Theorem bin_to_nat_pres_incr : forall n : bin,
    bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  induction n as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => O
  | S 0 => I
  | S (S n') => T (nat_to_bin n')
  end.
Theorem bin_to_nat_equal : forall n : bin,
    nat_to_bin (bin_to_nat n) = n.
Proof.
  induction n as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros [|n].
  - reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m o : nat,
    n * (m * o) = (n * m) * o.
Proof.
  intros n m o.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite mult_plus_distr_r.
    rewrite <- IHn.
    reflexivity.
Qed.
