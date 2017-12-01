rm TestCut_patch.v
pumpkin-git bin_to_nat_pres_incr TestCut.v -rev 534605ba751735bc74915da8febd5780a187e05f -safe
coqc TestCut_patch.v
# echo "Added patch to Test_patch.v. Patch is:"
# coqc AssertEquals.v
# echo "Verified that this is the expected patch."

