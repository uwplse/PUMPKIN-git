
/(Theorem|Lemma|Example)[ ]+$IDENTIFIER[ ]+/{
  :prf
  p
  /(Qed|Admitted)[.]/!{
    n
    b prf
  }
  q
}

/(Definition|Let|Fixpoint|CoFixpoint)[ ]+$IDENTIFIER[ ]+/{
  :def
  p
  /[^.][.]([ ]*[(][*].*[*][)])*[ ]*$/!{
    n
    b def
  }
  q
}

/(Inductive|CoInductive)[ ]+$IDENTIFIER[ ]+/{
  :ind
  p
  /[^.][.]([ ]*[(][*].*[*][)])*[ ]*$/!{
    n
    b ind
  }
  q
}
