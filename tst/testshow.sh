# Test basic functionality with an old revision in show mode

set -e

echo "Showing old definition of test:"
echo ""
pumpkin-git test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e -mode show
echo ""
echo "Success"
