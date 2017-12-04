# USE THE FORCE

set -e

cp Test.v Test_tmp.v
pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode force
coqc Test.v
echo "Added patch to Test.v. Patch is:"
coqc AssertEquals_Overwrite.v
echo "Verified that this is the expected patch."
echo ""
echo "Reverting Test.v to its previous state."
mv Test_tmp.v Test.v
