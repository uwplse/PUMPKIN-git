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

Suppose you are working inside of a local repository with some Coq code.
In this repository, you make a breaking change, and adapt an example
proof to that change.
You can use PUMPKIN-git to search that example for a patch that corresponds to
the change, which you can use to patch other broken proofs.

Simply run:

```
pumpkin-git example_proof_id file.v
```

This will search for a patch that corresponds to the change in
`changed_term_name` compared to the HEAD of your local repository.
It will then prompt you with the patch it finds, and either
overwrite the file (if you say yes) or save the results to a temporary file
(if you say no).

There is an example of this in the repository:

```
cd tst
./testhead.sh
```

The example automatically responds no to the prompt,
and so will write to a temporary file.

When the changed proof depends on other terms that have also changed,
you must pass those terms in using the `-changed` flag:

```
pumpkin-git example_proof_id file.v -changed dep1_id -changed dep2_id ...
```

This is temporary; we are in the process of working on
pulling in dependencies automatically.

## Options for Control

### Old Revisions

The optional `-rev` flag searches for patches
against a revision other than HEAD:

```
pumpkin-git example_proof_id file.v -rev rev
```

There is an example of this usage in the repository:

```
cd tst
./test.sh
```

### Naming the Patch

The default name of the patch is `patch`. The `-patch` flag
controls the name of the patch:

```
pumpkin-git example_proof_id file.v -patch patch_id
```

### Hint Database Integration

The `-hint` flag automatically adds the patch it finds to a hint database
if it is present:

```
pumpkin-git example_proof_id file.v -hint
```

There is an example of this usage in the repository:

```
cd tst
./testhint.sh
```

### Modes

The default mode is `interactive`: PUMPKIN-git searches for a patch,
adds the patch to the text from `file.v`, then prompts you to overwrite
`file.v` with the result.
The `-mode` option changes the behavior of PUMPKIN to any of the following:

* `show`: Print the old definition of `example_proof_id` and exit.
* `define`: Add the old definition of `example_proof_id` to the text from `file.v` and save the result as `file_patch.v`.
* `lazy`: Add the definition of `example_proof_id` and a call to PUMPKIN to the text from `file.v`, then save the result as `file_patch.v`. (This is useful for debugging.)
* `call`: Add the definition of `example_proof_id` and a call to PUMPKIN to the text from `file.v`, save the result as `file_patch.v`, then compile `file_patch.v` to call PUMPKIN and search for a patch.
* `safe`: Call PUMPKIN to search for a patch, add the patch to the text from `file.v`, and save the result as `file_patch.v`.
* `force`: Call PUMPKIN to search for a patch and add the patch directly to `file.v` without prompting the user.

There are examples for all of these modes in the repository.

## Guiding PUMPKIN

The PUMPKIN plugin takes as an optional argument a lemma to cut by
to help guide search. The PUMPKIN-git option `-cut` passes this argument
directly to PUMPKIN-git:

```
pumpkin-git example_proof_id file.v -cut (fun arg ... => cut_id arg ...)
```

In order to use this, you must define the lemma `cut_id` _earlier_ in the file
than `example_proof_id`. The format for passing in this argument
is otherwise exactly the same as using PUMPKIN directly.

There is an example of this usage in the repository:

```
cd tst
./testcut.sh
```

# Contributors

The Git infrastructure for this plugin was written by Nate Yazdani,
then modified by Talia Ringer to support calling PUMPKIN.
