Require Import lessthan.
Require Import Kami.

Theorem lt_spec: forall a, forall b, (test_lt a b) = (Nat.ltb #(a) #(b)).
Proof.
intros a b.
reflexivity.
Qed.
