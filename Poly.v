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
  | S count' => cons _ x (repeat' _ x count')
  end.
