Require Import Arith.
Definition f x := x + 100.

Compute f 10.

Definition g x := x - 100.

Compute g 110.

Theorem g_f : forall x, g (f x) = x.
Proof.
  intros x. unfold f, g.
  rewrite Nat.add_sub. reflexivity.
Qed.
