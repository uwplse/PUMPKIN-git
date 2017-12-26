#!/bin/sh
# Run coq-dpdgraph's Depgraph functionality via command line

if [ "$#" -ne 2 ]
then
  echo "Usage: $0 filename identifier" >&2
  exit 1
fi

coqtop -l $1 <<EOF
Require dpdgraph.dpdgraph.
Print DependGraph $2.
EOF


