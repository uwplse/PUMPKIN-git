Require Import Arith NPeano.

Theorem test:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. auto.
Qed.

