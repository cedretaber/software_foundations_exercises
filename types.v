Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive colour : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : colour) : bool :=
  match c with
  | black
  | white => true
  | primary _ => false
  end.

Definition isRed (c : colour) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb: nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).
