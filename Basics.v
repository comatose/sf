Module NatPlayground.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

  Check (S(S(S(S(S O))))).
  Check 4.
  Check pred.

  Fixpoint evenb (n : nat) : bool :=
    match n with
    | O => true
    | S n' => negb (evenb n')
    end.

  Example test_evenb : evenb (S O) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_evenb2 : evenb (S (S O)) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition oddb (n : nat) := negb (evenb n).
  Example test_oddb1 : oddb O = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Example test_plus1 : plus (S O) (S (S O)) = S (S (S O)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Compute mult (S (S O)) (S (S (S O))).

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | _, O => n
    | S n', S m' => minus n' m'
    end.

  Fixpoint exp (n m : nat) : nat :=
    match m with
    | O => S O
    | S m' => mult n (exp n m')
    end.

  Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => S O
    | S n' => mult n (factorial n')
    end.

  Example test_factorial1: factorial (S (S (S O))) = S (S (S (S (S (S O))))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
  Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

  Compute (S O) + (S O).

  Fixpoint beq_nat (n m : nat) : bool :=
    match n, m with
    | O, O => true
    | S n', S m' => beq_nat n' m'
    | _, _ => false
    end.

  Fixpoint beq_nat2 (n m : nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | _ => false
           end
    | S n' => match m with
              | O => false
              | S m' => beq_nat2 n' m'
              end
    end.

  Example test_beg_nat21 : beq_nat = beq_nat2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_beg_nat1 : beq_nat (S (S O)) (S (S O)) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_beg_nat2 : beq_nat (S (S O)) (S (S(S O))) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => leb n' m'
              end
    end.

  Type (beq_nat = beq_nat2).

  Theorem plus_O_n : forall n : nat, O + n = n.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.

  Theorem plus_1_l : forall n : nat, (S O) + n = S n.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.

  Theorem plus_id_example : forall n m : nat,
      n = m -> n + n = m + m.
  Proof.
    intros n m H.
    rewrite <- H.
    reflexivity.
  Qed.

  Theorem plus_id_exercise : forall n m o : nat,
      n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o H1 H2.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  Qed.

  Theorem mult_0_plus : forall n m : nat,
      (O + n) * m = n * m.
  Proof.
    intros n m.
    rewrite -> plus_O_n.
    reflexivity.
  Qed.

  Theorem mult_S_1 : forall n m : nat,
      m = S n -> m * ((S O) + n) = m * m.

  Proof.
    intros n m H.
    rewrite -> plus_1_l.
    rewrite <- H.
    reflexivity.
  Qed.

  Theorem plus_1_neq_0 : forall n : nat,
      beq_nat (n + (S O)) O = false.
  Proof.
    intros n.
    destruct n as [| n'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Theorem negb_involutive : forall b : bool,
      negb (negb b) = b.
  Proof.
    intros b.
    destruct b.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_commutative : forall b c : bool,
      andb b c = andb c b.

  Proof.
    intros b c.
    destruct b.
    - destruct c.
      + reflexivity.
      + reflexivity.
    - destruct c.
      + reflexivity.
      + reflexivity.
  Qed.

  Theorem plus_1_neq_0' : forall n : nat,
      beq_nat (n + (S O)) O = false.
  Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_commutative'' : forall b c,
      andb b c = andb c b.

  Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_true_elim2 : forall b c : bool,
      andb b c = true -> c = true.
  Proof.
    intros [][].
    - reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
  Qed.

  Theorem zero_nbeq_plus_1 : forall n : nat,
      beq_nat O (n + (S O)) = false.
  Proof.
    intros [|n].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Theorem identify_fn_applied_twice:
    forall f : (bool -> bool),
      (forall x : bool, f x = x) ->
      forall b : bool, f (f b) = b.
  Proof.
    intros f.
    intros H.
    intros b.
    rewrite -> H.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem negation_fn_applied_twice:
    forall f : (bool -> bool),
      (forall x : bool, f x = negb x) ->
      forall b : bool, f (f b) = b.
  Proof.
    intros f H b.
    rewrite -> H.
    rewrite -> H.
    destruct b.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_eq_orb :
    forall b c : bool,
      (andb b c = orb b c) ->
      b = c.
  Proof.
    intros [] [].
    - simpl.
      reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.
End NatPlayground.

Module BinPlayground.
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

  Fixpoint bin_to_nat (n : bin) : NatPlayground.nat :=
    match n with
    | O => NatPlayground.O
    | I => NatPlayground.S NatPlayground.O
    | T n' => NatPlayground.plus (bin_to_nat n') (NatPlayground.S (NatPlayground.S NatPlayground.O))
    end.

  Example test_bin_incr1: bin_to_nat (incr O) = NatPlayground.S (bin_to_nat O).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr2: bin_to_nat (incr I) = NatPlayground.S (bin_to_nat I).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr3: bin_to_nat (incr (T O)) = NatPlayground.S (bin_to_nat (T O)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr4: bin_to_nat (incr (T I)) = NatPlayground.S (bin_to_nat (T I)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr5: bin_to_nat (incr (T (T O))) = NatPlayground.S (bin_to_nat (T (T O))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint nat_to_bin (n : NatPlayground.nat) : bin :=
    match n with
    | NatPlayground.O => O
    | NatPlayground.S NatPlayground.O => I
    | NatPlayground.S (NatPlayground.S n') => T (nat_to_bin n')
    end.

  Example test_bin_recovery1 : bin_to_nat (nat_to_bin NatPlayground.O) = NatPlayground.O.
  Proof. reflexivity. Qed.

  Example test_bin_recovery2 : bin_to_nat (nat_to_bin (NatPlayground.S NatPlayground.O)) = NatPlayground.S NatPlayground.O.
  Proof. reflexivity. Qed.

  Example test_bin_recovery3 : bin_to_nat (nat_to_bin (NatPlayground.S (NatPlayground.S NatPlayground.O))) = NatPlayground.S (NatPlayground.S NatPlayground.O).
  Proof. reflexivity. Qed.

  Example test_bin_recovery4 : bin_to_nat (nat_to_bin (NatPlayground.S (NatPlayground.S (NatPlayground.S NatPlayground.O)))) = NatPlayground.S (NatPlayground.S (NatPlayground.S NatPlayground.O)).
  Proof. reflexivity. Qed.
End BinPlayground.

