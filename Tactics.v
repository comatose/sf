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
