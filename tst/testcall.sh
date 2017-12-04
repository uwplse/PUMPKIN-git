# Test basic functionality in call mode

rm Test_patch.v

set -e

pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode call
echo "----"
echo ""
echo "Test_patch.v compiles. Checking patch."
echo ""
coqc AssertEquals.v
echo "Verified that this is the expected patch."
