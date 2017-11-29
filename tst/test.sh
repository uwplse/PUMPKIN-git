rm Test_patch.v
gitter test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e
echo "The definition has been added to Test_patch.v."
echo "Difference between Test.v and Test_patch.v:"
echo ""
diff Test.v Test_patch.v
