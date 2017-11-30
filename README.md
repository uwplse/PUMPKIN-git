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
pumpkin-git changed_proof proofs/file.v
# Now "proofs/file_patch.v" contains a patch between versions of changed_proof
```

There is a simple example in the repository. Simply run this script:

```
cd tst
./test.sh
```

It should patch a proof in Test.v from an old revision of this repository and
add the patch to the file Test_patch.v. It should then print the
patch and verify that it has the correct type. The output
should be as follows:

```
Added patch to Test_patch.v. Patch is:
patch =
fun (n m p : nat) (_ : n <= m) (_ : m <= p) (H1 : n <= p) =>
Plus.le_plus_trans n p 1 H1
     : forall n m p : nat, n <= m -> m <= p -> n <= p -> n <= p + 1

Argument scopes are [nat_scope nat_scope nat_scope _ _ _]
Verified that this is the expected patch.
```

Any other output means that there is a bug in the tool or in PUMPKIN PATCH.
If this happens, please report an issue.

