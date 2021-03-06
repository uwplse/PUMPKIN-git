# Test cutting an intermediate lemma

rm TestCut_patch.v

set -e

pumpkin-git bin_to_nat_pres_incr TestCut.v -rev 534605ba751735bc74915da8febd5780a187e05f -mode safe -cut "(fun (H : cut) b0 => H (bin_to_nat b0))" -changed bin_to_nat
coqc TestCut_patch.v
echo "Patches are:"
coqc CutResults.v
echo "Verified that these are the expected patches."



