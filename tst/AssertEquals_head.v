Require Import Test_head_patch.

Print patch.

Theorem assertEquals:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p ->
    n < p + 1.
Proof.
  exact patch.
Qed.
