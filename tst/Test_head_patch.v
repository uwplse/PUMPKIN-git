Require Import Arith NPeano.

Theorem test:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0; auto with arith.
Qed.
Definition patch :=
fun (n m p : nat) (_ : le n m) (_ : le m p) (H1 : lt n (S p)) =>
@eq_ind_r nat (PeanoNat.Nat.add (S O) p) (fun n0 : nat => lt n n0) H1
  (PeanoNat.Nat.add p (S O)) (PeanoNat.Nat.add_comm p (S O))
.

