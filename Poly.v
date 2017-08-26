Require Export Lists.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Fixpoint repeat (X : Type) (x : X) (n : nat) : list X :=
  match n with
  | 0 => nil X
  | S n' => cons X x (repeat X x n')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Module MumbleGrumble.
  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c: mumble.

  Inductive grumble (X : Type) :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  Check d mumble (b a 5).
  Check d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).
  Check c.
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X} _.

Fixpoint repeat''' {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h l1' => cons h (app l1' l2)
  end.

Fixpoint rev {X : Type} (l : list X) : (list X) :=
  match l with
  | nil => nil
  | cons h l' => app (rev l') (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Theorem app_nil_r : forall (X : Type) (l : list X),
    l ++ [] = l.
Proof.
  induction l as [| x' l' H].
  - simpl. reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l as [].
  - simpl. reflexivity.
  - simpl. intros m n.
    rewrite -> IHl. reflexivity.
Qed.

Lemma app_length : forall X (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1 as [].
  - simpl. reflexivity.
  - simpl. intros l2. rewrite -> IHl1. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [|x l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X (l : list X),
    rev (rev l) = l.
Proof.
  induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | h1::l1', h2::l2' => (h1, h2) :: (combine l1' l2')
  end.

Check combine.
Check @combine.

Fixpoint split {X Y : Type} (l : list (X * Y)) : list X * list Y :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' => (x :: fst (split l'), y :: snd (split l'))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity. Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X: Type} (l: list X) (n: nat) : option X :=
  match l, n with
  | [], _ => None
  | x :: _, 0 => Some x
  | _ :: l', S n' => nth_error l' n'
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X): X :=
  f (f (f n)).

Fixpoint filter {X : Type} (pred : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: l' => if pred h then h :: filter pred l' else filter pred l'
  end.

Example test_anon_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Definition partition {X : Type} (pred : X -> bool) (l : list X) : list X * list X :=
  (filter pred l, filter (fun b => negb (pred b)) l).

Fixpoint oddb (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => negb (oddb n')
  end.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint  map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | x :: l' => f x :: map f l'
  end.

Lemma map_dist : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [|n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f.
  induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. 
    rewrite -> map_dist. simpl. reflexivity.
Qed.

Fixpoint flatten {X : Type} (l : list (list X)) : list X :=
  match l with
  | [] => []
  | x :: l' => x ++ flatten l'
  end.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  flatten (map f l).

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (o : option X) : option Y :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | [] => b
  | x :: l' => f x (fold f l' b)
  end.

Definition constfun {X Y: Type} (x : X) : Y -> X :=
  fun _ => x.

Definition ftrue {Y : Type} : Y -> bool := constfun true.

Example constfun_example1 : ftrue false = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) [99] = 5.
Proof. reflexivity. Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall (X: Type) (l : list X),
    fold_length l = length l.
Proof.
  intros X.
  induction l as [].
  - reflexivity.
  - simpl. rewrite <- IHl. simpl. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x acc => f x :: acc) l [].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
    fold_map f l = map f l.

Proof.
  intros X Y f.
  induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) : X -> Y -> Z :=
  (fun x y => f (x, y)).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) : (X * Y) -> Z :=
  (fun p => f (fst p) (snd p)).

Example test_map2 : map (plus 3) [2; 0; 2] = [5; 3; 5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  
