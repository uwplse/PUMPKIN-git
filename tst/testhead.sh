# Test modifying a file and patching against HEAD

rm Test_patch.v
mv Test_head.v Test_head_tmp.v
mv Test_head_edit.v Test_head.v
pumpkin-git test Test_head.v -mode safe
mv Test_head.v Test_head_edit.v
mv Test_head_tmp.v Test_head.v

set -e
coqc Test_head_patch.v
echo "Added patch to Test_head_patch.v. Patch is:"
coqc AssertEquals_head.v
echo "Verified that this is the expected patch."
