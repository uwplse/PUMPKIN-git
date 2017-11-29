# PUMPKIN-git: A git helper for PUMPKIN PATCH

## Dependencies

To use this tool, you need to have the [PUMPKIN PATCH plugin](https://github.com/uwplse/PUMPKIN-PATCH) installed.

In addition, you need the [core](https://opam.ocaml.org/packages/core/) package.
You can install it through opam:

```
opam install core
```

## Building

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
# Now "proofs/file_patch.v" contains a patch between versions of changed_proof
```

There is a simple example in the repository. Simply run this script:

```
cd tst
./test.sh
```

It should patch a proof from an old revision of this repository and open
up Coqtop. From there, you can print the patch:

```
Print patch.
```

This should give you the following output:

```
patch =
  fun (n m p : nat) (_ : n <= m) (_ : m <= p) (H1 : n <= p) =>
    le_plus_trans n p 1 H1
  : forall n m p : nat, n <= m -> m <= p -> n <= p -> n <= p + 1
```

