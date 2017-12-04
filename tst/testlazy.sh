# Test basic functionality in lazy mode

rm Test_patch.v

set -e

pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode lazy
echo "Added definition and PUMPKIN call to Test_patch.v."
echo "Now executing the call:"
coqc Test_patch.v
echo "----"
echo ""
echo "Test_patch.v compiles. Checking patch."
echo ""
coqc AssertEquals.v
echo "Verified that this is the expected patch."
