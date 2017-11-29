rm Test_patch.v
pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e
coqtop -load-vernac-source Test_patch.v

