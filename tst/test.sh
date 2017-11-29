rm Test.v.tmp
gitter test Test.v -rev 1d578537e1b38a7996e94b14788b5f4f5913dc3e
echo "The definition has been added to Test.v.tmp."
echo "Difference between Test.v and Test.v.tmp:"
echo ""
diff Test.v Test.v.tmp
