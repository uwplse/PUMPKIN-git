# PUMPKIN-git: A git helper for PUMPKIN PATCH

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
# Now "proofs/file.v.tmp" has "changed_proof_old" in it as well
```
