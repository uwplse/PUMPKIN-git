# PUMPKIN-git: A git helper for PUMPKIN PATCH

## Building

You need the [core](https://opam.ocaml.org/packages/core/) package to build this tool.
You can install it through opam:

```
opam install core
```
Once you have that, you can build the tool:

```
cd src
make
export PATH=`pwd`:$PATH # for trying out the tool
```

# Usage

The normal workflow goes as follows:

```
cd /some/git/repo/with/coq/code
gitter changed_proof proofs/file.v
# Now "proofs/file.v.tmp" has "changed_proof_old" in it as well
```

There is a simple example in the repository. Simply run this script:

```
cd tst
./test.sh
```

It should print this output:

```
The definition has been added to Test.v.tmp.
Difference between Test.v and Test.v.tmp:

2a3,13
> Theorem test_old:
>   forall (n m p : nat),
>     n <= m ->
>     m <= p ->
>     n <= p + 1.
> Proof.
>   intros. induction H0.
>   - auto with arith.
>   - constructor. auto.
> Qed.
> 
```
