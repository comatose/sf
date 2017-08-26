Require Export Induction.
Module NatList.

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
    | 0, 0 => true
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

  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [|n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | cons h rest => rev rest ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
  Proof.
    induction l as [|n l' IHl'].
    - simpl. reflexivity.
    - simpl.
      rewrite <- IHl'.
  Abort.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = length l1 + length l2.
  Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHl'. reflexivity.
  Qed.

  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    induction l as [|n l' IHl'].
    - simpl. reflexivity.
    - simpl.
      rewrite -> app_length.
      simpl.
      rewrite -> IHl'.
      rewrite -> plus_comm.
      reflexivity.
  Qed.

  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    induction l as [|n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_app_distr : forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite -> app_assoc.
      reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    induction l as [|n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> rev_app_distr.
      simpl. rewrite -> IHl'.
      reflexivity. Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl'.
      destruct n as [|n'].
      + reflexivity.
      + simpl. reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) :=
    match l1, l2 with
    | nil, nil => true
    | _ , nil => false
    | nil, _ => false
    | h1 :: l1' , h2 :: l2' =>
      match beq_nat h1 h2 with
      | true => beq_natlist l1' l2'
      | false => false
      end
    end.

  Example test_beq_natlist1 :
    (beq_natlist nil nil = true).
  Proof. reflexivity. Qed.

  Example test_beq_natlist2 :
    beq_natlist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.

  Example test_beq_natlist3 :
    beq_natlist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem beq_natlist_refl : forall l : natlist,
      true = beq_natlist l l.
  Proof.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'.
      induction n as [|n'].
      + simpl. reflexivity.
      + simpl. rewrite <- IHn'.
        reflexivity.
  Qed.

  Fixpoint leb (n m : nat) : bool :=
    match n with
    | 0 => true
    | S n' => match m with
              | 0 => false
              | S m' => leb n' m'
              end
    end.

  Theorem count_member_nonzero : forall s : bag,
      leb 1 (count 1 (1 :: s)) = true.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
      leb n (S n) = true.
  Proof.
    induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed.

  Theorem remove_decrease_count : forall s : bag,
      leb (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    induction s as [|n s' IHs'].
    - simpl. reflexivity.
    - simpl.
      induction n as [|n'].
      + simpl. rewrite -> ble_n_Sn. reflexivity.
      + simpl. rewrite -> IHs'. reflexivity.
  Qed.

  Theorem rev_injective : forall l1 l2 : natlist,
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Inductive natoption :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint nth_error (l:natlist) (n:nat) :=
    match l, n with
    | nil, _ => None
    | h::_ , 0 => Some h
    | _::t , S n' => nth_error t n'
    end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d:nat) (o:natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.
  
  Definition hd_error (l:natlist) : natoption :=
    match l with
    | nil => None
    | h::_ => Some h
    end.

  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.

  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.

  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
      hd default l = option_elim default (hd_error l).
  Proof.
    destruct l as [|n l'].
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Inductive id : Type :=
  | Id : nat -> id.

  Definition beq_id (x1 x2 : id) :=
    match x1, x2 with
      | Id n, Id m => beq_nat n m
    end.

  Theorem beq_id_refl : forall (x : id),
      true = beq_id x x.
  Proof.
    destruct x as [n].
    simpl.
    induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHn'.
      reflexivity.
  Qed.

  Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

  Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record x' v d' => if beq_id x x' then Some v
                        else find x d'
    end.

  Theorem update_eq : forall (d : partial_map) (x : id) (v : nat),
      find x (update d x v) = Some v.

  Proof.
    intros d x v.
    destruct d as [|x' v' d'].
    - simpl. rewrite <- beq_id_refl. reflexivity.
    - simpl. rewrite <- beq_id_refl. reflexivity.
  Qed.

  Theorem update_neq: forall (d:partial_map) (x y : id) (o : nat),
      beq_id x y = false -> find x (update d y o) = find x d.
  Proof.
    intros d x y o H.
    simpl.
    rewrite -> H. reflexivity.
    Qed.

End NatList.
