# Test basic functionality with an old revision

rm TestModule_patch.v

set -e

pumpkin-git test TestModule.v -rev 99fcc53a0866c3f375c849190418b5baa44cb35d -safe
coqc TestModule_patch.v
echo "Added patch to TestModule_patch.v. Patch is:"
coqc AssertEquals_Module.v
echo "Verified that this is the expected patch."
