Require Import Arith NPeano.

Module Test.

Theorem test:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - auto with arith.
  - constructor. auto.
Qed.

End Test.
