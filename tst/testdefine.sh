# Test basic functionality with define mode

rm Test_patch.v

set -e

pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode define
echo "Added old definition of test to Test_patch.v."
echo ""
coqc Test_patch.v
echo "Test_patch.v compiles. Showing file contents:"
echo ""
cat Test_patch.v

