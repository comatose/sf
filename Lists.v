Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair f _ => f
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair _ s => s
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros [x y].
  simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p: natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros [].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p: natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros [].
  reflexivity.
Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: rest" := (cons x rest) (at level 60, right associativity).
Notation "[]" := (nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil)..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => []
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | cons _ rest => 1 + (length rest)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: rest => h :: (app rest l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof.
  simpl. reflexivity. Qed.
Example test_app2 : nil ++ [4;5] = [4;5].
Proof.
  simpl. reflexivity. Qed.
Example test_app3 : [1;2;3] ++ nil = [1;2;3].
Proof.
  simpl. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [] => default
  | h :: _ => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | [] => []
  | _ :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 2 [] = 2.
Proof. simpl. reflexivity. Qed.
Example test_tl : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | cons h rest =>
    match h with
    | 0 => nonzeros rest
    | _ => h :: nonzeros rest
    end
  end.
Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint filter (pred:nat -> bool) (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: rest =>
    match (pred h) with
    | true => h :: filter pred rest
    | false => filter pred rest
    end
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | 0 => true
  | S n' => negb (evenb n')
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint oddmembers (l:natlist) : natlist :=
  filter oddb l.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition count_if (pred:nat -> bool) (l:natlist) : nat :=
  length (filter pred l).

Definition countoddmembers (l:natlist) : nat :=
  count_if oddb l.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
  simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2:natlist) : natlist :=
  match l1, l2 with
  | (cons h1 rest1), (cons h2 rest2) => h1 :: h2 :: alternate rest1 rest2
  | nil, rest => rest
  | rest, nil => rest
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => beq_nat n' m'
  | _, _ => false
  end.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: rest =>
    match (beq_nat h v) with
    | true => S (count v rest)
    | _ => count v rest
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add : nat -> bag -> bag := cons .
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: rest =>
    match beq_nat h v with
    | false => h :: remove_one v rest
    | true => rest
    end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: rest =>
    match beq_nat h v with
    | false => h :: remove_all v rest
    | true => remove_all v rest
    end
  end.
  

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
 Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | cons h rest =>
    match member h s2 with
    | false => false
    | true => subset rest (remove_one h s2)
    end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
 Proof. simpl. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 Proof. simpl. reflexivity. Qed.
