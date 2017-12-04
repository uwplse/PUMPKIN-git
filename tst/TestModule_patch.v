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
Definition patch :=
fun (n m p : nat) (_ : le n m) (_ : le m p) (H1 : le n p) =>
le_plus_trans n p (S O) H1
.


End Test.
