# Test automatically adding to hints

rm Test_patch.v

set -e

pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode safe -hint
coqc Test_patch.v
echo "Added patch to Test_patch.v. Patch is:"
coqc AssertEquals_hint.v
echo "Verified that this is the expected patch."
